open Place_encoding
module L = Place_lookup
module A = Archive

type assigned = PName.t -> PG.selection

let decided (assigned : assigned) n =
  match assigned n with PG.Decided v -> Some v | _ -> None

(* the location itself and each one above it, deepest first *)
let rec ups l = l :: (match l with [] -> [] | _ :: t -> ups t)

(* the occupant the partial layout holds at location l, if decided *)
let occupant ~assigned (l : string list) =
  match l with
  | [] -> None
  | a :: t -> (
      match decided assigned (R.Name.Loc (t, a)) with
      | Some (R.Version.Occ x) -> Some x
      | _ -> None)

(* where the walk from l for a lands in the partial layout, reading an
   undecided location as absent: the first decided occupant going up *)
let visible ~assigned l a =
  List.find_map
    (fun l' ->
      match decided assigned (R.Name.Loc (l', a)) with
      | Some (R.Version.Occ x) -> Some (l', x)
      | _ -> None)
    (ups l)

let mem v cands = List.exists (PVersion.equal v) cands
let is_dep (ed : L.edge) = not ed.L.e.Npl.e_peer
let is_peer (ed : L.edge) = ed.L.e.Npl.e_peer
let key (ed : L.edge) = ed.L.e.Npl.e_dir

(* npm-pick-manifest's sort criteria above semver, as Pick ranks them *)
let rank ar (x : Npl.Occ.t) : bool * bool * bool =
  match x with
  | Npl.Occ.Top -> (true, true, true)
  | Npl.Occ.Reg (m, v) -> (
      match A.meta ar (m, v.IVer.s) with
      | Some mt -> A.ver_rank ar mt
      | None -> (true, true, true))

let best ar (cands : Npl.Occ.t list) : Npl.Occ.t =
  match cands with
  | [] -> invalid_arg "best"
  | c :: cs ->
      List.fold_left
        (fun a b ->
          let d = compare (rank ar b) (rank ar a) in
          if d > 0 || (d = 0 && occ_compare b a > 0) then b else a)
        c cs

(* dist-tags.latest first, under the same two criteria, as the npm
   reading's tagged *)
let tagged ar (cands : Npl.Occ.t list) : Npl.Occ.t option =
  List.find_opt
    (function
      | Npl.Occ.Top -> false
      | Npl.Occ.Reg (m, v) -> (
          A.loaded_latest ar m = Some v.IVer.s
          &&
          match A.meta ar (m, v.IVer.s) with
          | Some mt -> A.ver_rank ar mt = (true, true, true)
          | None -> false))
    cands

let pick ar cands =
  match tagged ar cands with Some c -> c | None -> best ar cands

(* npm resolves a peer together with its peer set: the packages the copy
   at l brings in that peer on a too, and theirs while each does
   (build-ideal-tree.js #loadPeerSet), each at the version already decided
   for it or else npm's pick for its range.  Their accepted sets on a,
   which a pick for the walk from l should meet. *)
let peer_set st ~assigned l a : Npl.Occ.t list list =
  let seen = Hashtbl.create 16 in
  let rec go at (y : Npl.Occ.t) =
    if Hashtbl.mem seen y then []
    else begin
      Hashtbl.replace seen y ();
      List.concat_map
        (fun (ed : L.edge) ->
          let x =
            match
              Option.bind at (fun l ->
                  decided assigned (R.Name.Walk (l, key ed)))
            with
            | Some (R.Version.Found (_, x)) -> Some x
            | _ ->
                if ed.L.accepts = [] then None
                else Some (pick (L.archive st) ed.L.accepts)
          in
          match x with
          | None -> []
          | Some x -> (
              match
                List.filter
                  (fun (p : L.edge) ->
                    is_peer p && key p = a && not p.L.e.Npl.e_opt)
                  (L.edges st x)
              with
              | [] -> []
              | ps -> List.map (fun (p : L.edge) -> p.L.accepts) ps @ go None x))
        (List.filter is_dep (L.edges st y))
    end
  in
  match match l with [] -> Some Npl.Occ.Top | _ -> occupant ~assigned l with
  | Some y -> go (Some l) y
  | None -> []

(* arborist's PlaceDep for the walk from l for a, which is the edge's
   placement (place-dep.js, can-place-dep.js):
   - KEEP: the copy the walk already reaches, when the edge takes it;
   - an optional edge that reaches nothing stays unplaced;
   - otherwise npm-pick-manifest's pick among what the edges take, put in
     the shallowest node_modules from l up that holds nothing yet, stopping
     at the first that holds a copy or that a walk already passes (⊥), and
     at a level whose own package wants another version; a level whose
     package peers on a is passed over (deepest-nesting-target.js).
   Preference only: every answer is one of [cands], and a placement that
   breaks a decided walk is a conflict the solver backtracks from. *)
let choose_walk st ~assigned l a cands =
  let keep =
    match visible ~assigned l a with
    | Some (l', x) when mem (R.Version.Found (l', x)) cands ->
        Some (R.Version.Found (l', x))
    | Some _ -> None
    | None -> if mem R.Version.Bot cands then Some R.Version.Bot else None
  in
  match keep with
  | Some v -> v
  | None -> (
      let offered =
        List.sort_uniq occ_compare
          (List.filter_map
             (function R.Version.Found (_, x) -> Some x | _ -> None)
             cands)
      in
      let offered =
        match
          List.fold_left
            (fun acc s ->
              let h = Hashtbl.create 64 in
              List.iter (fun y -> Hashtbl.replace h y ()) s;
              List.filter (Hashtbl.mem h) acc)
            offered
            (peer_set st ~assigned l a)
        with
        | [] -> offered
        | met -> met
      in
      match offered with
      | [] -> Pac_common.Order.greatest PVersion.compare cands
      | _ -> (
          let u = pick (L.archive st) offered in
          let wants (y : Npl.Occ.t) =
            let es = L.edges st y in
            let peers = List.exists (fun ed -> is_peer ed && key ed = a) es in
            let dep = List.find_opt (fun ed -> is_dep ed && key ed = a) es in
            (peers, dep)
          in
          let rec climb best = function
            | [] -> best
            | lv :: rest -> (
                match decided assigned (R.Name.Loc (lv, a)) with
                | Some _ -> best
                | None -> (
                    let peers, dep =
                      match occupant ~assigned lv with
                      | Some y -> wants y
                      | None -> (false, None)
                    in
                    if lv <> [] && lv <> l && peers then climb best rest
                    else
                      match dep with
                      | Some ed
                        when lv <> l
                             && not
                                  (List.exists
                                     (fun x -> occ_compare x u = 0)
                                     ed.L.accepts) ->
                          best
                      | _ ->
                          let best =
                            if mem (R.Version.Found (lv, u)) cands then Some lv
                            else best
                          in
                          climb best rest))
          in
          match climb None (ups l) with
          | Some lv -> R.Version.Found (lv, u)
          | None -> Pac_common.Order.greatest PVersion.compare cands))

let choose st ~assigned (n : PName.t) (cands : PVersion.t list) : PVersion.t =
  match n with
  | R.Name.Walk (l, a) -> choose_walk st ~assigned l a cands
  | _ -> Pac_common.Order.greatest PVersion.compare cands

(* npm's queue (#buildDepStep): the depender shallowest in node_modules,
   then first by path under the collation, and its edges in name order
   (build-ideal-tree.js:60-85, 997) *)
let rank_tbl : (PName.t, int * string * string) Hashtbl.t = Hashtbl.create 4096

let name_rank (n : PName.t) =
  Pac_common.Tbl.memo rank_tbl n (fun () ->
      match n with
      | R.Name.Walk (l, a) | R.Name.Loc (l, a) -> (List.length l, lock_path l, a)
      | R.Name.Root -> (-1, "", ""))

let before n m =
  let d, p, a = name_rank n and d', p', a' = name_rank m in
  match compare d d' with
  | 0 -> (
      match Order.collate p p' with 0 -> Order.collate a a' < 0 | c -> c < 0)
  | c -> c < 0

let least = function
  | [] -> None
  | (n, _) :: rest ->
      Some (List.fold_left (fun b (m, _) -> if before m b then m else b) n rest)

(* A name the constraints have narrowed to one version, or to none, first:
   deciding it places nothing, and a dead end is found at once.  Then the
   walk npm's queue resolves next: npm pops the copy first in its queue and
   resolves all its edges before popping another, so the copy whose edges
   are being resolved stays current while any is open, however early in
   the queue the copies it places sit. *)
let next current ~assigned:_ (open_names : (PName.t * int) list) : PName.t =
  match List.find_opt (fun (_, c) -> c <= 1) open_names with
  | Some (n, _) -> n
  | None -> (
      let own =
        match !current with
        | Some l ->
            List.filter
              (function R.Name.Walk (l', _), _ -> l' = l | _ -> false)
              open_names
        | None -> []
      in
      match least own with
      | Some n -> n
      | None -> (
          match least open_names with
          | Some (R.Name.Walk (l, _) as n) ->
              current := Some l;
              n
          | Some n -> n
          | None -> fst (List.hd open_names)))

let hooks : (L.t, PName.t, PG.selection, PVersion.t) Pac_common.Order.driver =
 fun order st ->
  match order with
  | `Tool ->
      Pac_common.Order.make ~next:(next (ref None)) ~choose:(choose st) ()
  | `Pubgrub -> Pac_common.Order.make ()
  | `Random seed -> Pac_common.Order.random seed
