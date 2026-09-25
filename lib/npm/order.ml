(* npm's order, replayed through PubGrub's next and choose hooks.

   build-ideal-tree.js places what each copy's problem edges fetch, taking
   copies from a queue ordered by where they sit in node_modules
   (#buildDepStep), and takes for each edge the version npm-pick-manifest
   picks, unless the copy's node_modules lookup already finds one the
   range admits.  The replay rebuilds that tree from the solver's
   decisions, so next names the directory npm resolves next and choose
   picks what npm would put there.  Both are preference only: next names
   an open name, and choose returns one of its candidates. *)

open Encoding
module L = Lookup

(* Intl.Collator("en"), which arborist orders its queue and a package's
   dependencies by (@isaacs/string-locale-compare): punctuation counts, and
   sorts before digits and letters in the root collation's order, so "_"
   sorts before "-" where byte order has it after; case decides only
   between strings that are otherwise equal. *)
let collation =
  "_-,;:!?.'\"()[]{}@*/\\&#%`^+<=>|~$0123456789abcdefghijklmnopqrstuvwxyz"

let primary =
  let t = Array.init 256 (fun i -> 1000 + i) in
  t.(Char.code ' ') <- -1;
  String.iteri
    (fun i c ->
      t.(Char.code c) <- i;
      t.(Char.code (Char.uppercase_ascii c)) <- i)
    collation;
  t

let collate (a : string) (b : string) : int =
  let la = String.length a and lb = String.length b in
  let rec level w i =
    if i = la || i = lb then compare la lb
    else match compare (w a.[i]) (w b.[i]) with 0 -> level w (i + 1) | c -> c
  in
  let upper c = c >= 'A' && c <= 'Z' in
  match level (fun c -> primary.(Char.code c)) 0 with
  | 0 -> ( match level upper 0 with 0 -> compare a b | c -> c)
  | c -> c

type assigned = PName.t -> PG.selection

let decided (assigned : assigned) n =
  match assigned n with PG.Decided (Np.Vs.Orig u) -> Some u | _ -> None

(* a package's edges in the order npm meets them, by name in its
   collation (build-ideal-tree.js:997, 1428) *)
let by_dir st q =
  List.sort
    (fun (x : Np.coq_Dependency) (y : Np.coq_Dependency) ->
      collate x.Np.d_dir y.Np.d_dir)
    (L.active_dependencies st q)

let peers_on st q (a : string) =
  List.filter_map
    (fun (r : Np.coq_PeerDependency) ->
      if r.Np.p_name = a then Some r.Np.p_range else None)
    (L.peer_dependencies st q)

(* what p (key k at v) holds, by key: its dependencies, then the mandatory
   peers those install beside them *)
let held st ~assigned k v =
  let deps = by_dir st (snd k, v) in
  let dirs = List.map (fun (d : Np.coq_Dependency) -> d.Np.d_dir) deps in
  let held = Hashtbl.create 16 in
  let rec hold key =
    if not (Hashtbl.mem held key) then (
      let u = decided assigned (Np.Nm.Intermediate (k, v, key)) in
      Hashtbl.replace held key u;
      Option.iter
        (fun u ->
          List.iter
            (fun (r : Np.coq_PeerDependency) ->
              if (not r.Np.p_optional) && not (List.mem r.Np.p_name dirs) then
                hold (r.Np.p_name, r.Np.p_name))
            (L.peer_dependencies st (snd key, u)))
        u)
  in
  List.iter
    (fun (d : Np.coq_Dependency) -> hold (d.Np.d_dir, d.Np.d_target))
    deps;
  held

(* the peer ranges on a below the copy of key at u: those of its
   dependencies, and of theirs while each peers on a too, each copy met
   once however many starts reach it.  A dependency not decided yet is
   taken at npm's pick for its range, as npm fetches it. *)
let below st ~assigned (a : string) seen start =
  let rec go (key, u) =
    if Hashtbl.mem seen (key, u) then []
    else (
      Hashtbl.replace seen (key, u) ();
      List.concat_map
        (fun (d : Np.coq_Dependency) ->
          let okey = (d.Np.d_dir, d.Np.d_target) in
          let w =
            match decided assigned (Np.Nm.Intermediate (key, u, okey)) with
            | Some w -> Some w
            | None -> Pick.pick_in st d.Np.d_target d.Np.d_range
          in
          match w with
          | None -> []
          | Some w -> (
              match peers_on st (d.Np.d_target, w) a with
              | [] -> []
              | rs -> rs @ go (okey, w)))
        (by_dir st (snd key, u)))
  in
  go start

(* The peer ranges npm resolves into p's peer-only directory a that the
   encoding sends to another directory, in the order npm meets them: on
   behalf of a package q that p holds and that peers on a, so that q's own
   peer is what fills the directory, the peers on a of q's dependencies,
   and of theirs while each peers on a too.  npm places a peer inside a
   package that peers on the same name only at the root (can-place-dep.js:
   "cannot place peers inside their dependents, except for tops"), so
   these land beside q's own peer; the encoding puts them in q's
   directory. *)
let peer_ranges_into st ~assigned (k : string * string) (v : string)
    (a : string) : Np.coq_Range list =
  let seen = Hashtbl.create 16 in
  Hashtbl.fold
    (fun key u acc ->
      match u with
      | Some u when peers_on st (snd key, u) a <> [] -> (key, u) :: acc
      | _ -> acc)
    (held st ~assigned k v) []
  |> List.sort (fun ((d, _), _) ((d', _), _) -> collate d d')
  |> List.concat_map (below st ~assigned a seen)

(* A directory no dependency of p names: only a peer asks for it, so
   childCands offers every published version of the target and nothing
   narrows the slot but the peer ranges. *)
let peer_only st p (a : string) =
  not
    (List.exists
       (fun (d : Np.coq_Dependency) -> d.Np.d_dir = a)
       (L.active_dependencies st p))

(* npm's Node.canReplace: a peer range the version in the directory fails
   brings in npm's pick for that range, which takes the directory over when
   every range into it accepts it -- the calculus's own, which [cands]
   reflects, and each such range met before.  Preference only: the result
   is one of [cands]. *)
let replace st ~assigned k v (m : string * string) cands c =
  let t = snd m in
  let holds rg = function
    | Np.Vs.Orig u -> Np.rgHolds rg u
    | Np.Vs.Gran _ -> false
  in
  let takes_over into x =
    List.exists (PVersion.equal x) cands
    && List.for_all (fun r -> holds r x) into
  in
  let step (into, c) rg =
    let rg = L.effective st t rg in
    let c =
      if holds rg c then c
      else
        match Pick.pick_in st t rg with
        | Some u when takes_over into (Np.Vs.Orig u) -> Np.Vs.Orig u
        | _ -> c
    in
    (rg :: into, c)
  in
  snd
    (List.fold_left step ([], c) (peer_ranges_into st ~assigned k v (fst m)))

(* npm's own tree as the replay has built it: where each copy sits in
   node_modules, which is what npm's queue is ordered by and what a
   package's lookup of a name finds *)
type copy = {
  id : int;
  key : string * string;
  ver : string;
  up : copy option;
  depth : int;
  path : string;
  kids : (string, copy) Hashtbl.t;
  (* the directories whose edge npm has resolved at this copy *)
  seen : (string, unit) Hashtbl.t;
}

module DepsQueue = Set.Make (struct
  type t = copy

  let compare x y =
    match compare x.depth y.depth with
    | 0 -> ( match collate x.path y.path with 0 -> compare x.id y.id | c -> c)
    | c -> c
end)

type t = {
  st : L.t;
  mutable queue : DepsQueue.t;
  mutable current : copy option;
  mutable ids : int;
  (* each package's first copy, where choose resolves a directory the
     replay did not hand out *)
  first : ((string * string) * string, copy) Hashtbl.t;
  (* the decisions the tree was built from, which a backtrack can undo *)
  made : (PName.t, PVersion.t) Hashtbl.t;
  (* every decision choose returned, latest first, so that the ones a
     backtrack undid are the ones on top that no longer hold *)
  mutable decided : (PName.t * PVersion.t) list;
  (* the directory next handed the solver, and the copy it is resolved at *)
  mutable pending : (PName.t * copy) option;
}

let restart o =
  let root = o.st.L.root in
  let top =
    {
      id = 0;
      key = (fst root, fst root);
      ver = snd root;
      up = None;
      depth = 0;
      path = "";
      kids = Hashtbl.create 64;
      seen = Hashtbl.create 64;
    }
  in
  o.queue <- DepsQueue.singleton top;
  o.current <- None;
  o.ids <- 1;
  Hashtbl.reset o.first;
  Hashtbl.replace o.first (top.key, top.ver) top;
  Hashtbl.reset o.made;
  o.pending <- None

let create st =
  let o =
    {
      st;
      queue = DepsQueue.empty;
      current = None;
      ids = 0;
      first = Hashtbl.create 1024;
      made = Hashtbl.create 1024;
      decided = [];
      pending = None;
    }
  in
  restart o;
  o

(* node's module lookup: the copy's own node_modules, then each one above *)
let rec resolve (x : copy) (a : string) : copy option =
  match Hashtbl.find_opt x.kids a with
  | Some c -> Some c
  | None -> Option.bind x.up (fun u -> resolve u a)

(* the edge a copy's package has on directory a, as npm reads it: the
   target and the range, under the root's flat override *)
let edge_at st (x : copy) (a : string) =
  List.find_map
    (fun (d : Np.coq_Dependency) ->
      if d.Np.d_dir = a then
        Some (d.Np.d_target, L.effective st d.Np.d_target d.Np.d_range)
      else None)
    (L.active_dependencies st (snd x.key, x.ver))

let fits (t, rg) (m : string * string) (u : string) =
  snd m = t && Np.rgHolds rg u

(* whether putting u at m above t would take a package below t that
   already reaches the copy above off it (checkCanPlaceNoCurrent) *)
let breaks st (m : string * string) u (t : copy) (above : copy) =
  let a = fst m in
  let rec walk (d : copy) =
    (not (Hashtbl.mem d.kids a))
    && ((match edge_at st d a with
        | Some e -> fits e above.key above.ver && not (fits e m u)
        | None -> false)
       || Hashtbl.fold (fun _ k acc -> acc || walk k) d.kids false)
  in
  walk t

let fine st (x : copy) (m : string * string) u (t : copy) =
  let a = fst m in
  t == x
  || (match edge_at st t a with Some e -> fits e m u | None -> true)
     &&
     match Option.bind t.up (fun p -> resolve p a) with
     | Some above -> not (breaks st m u t above)
     | None -> true

let peers_at st (t : copy) (a : string) =
  List.exists
    (fun (r : Np.coq_PeerDependency) -> r.Np.p_name = a)
    (L.peer_dependencies st (snd t.key, t.ver))

(* PlaceDep: from the requirer up, the shallowest node_modules npm can put
   the copy in, stopping at the first that holds another version of the
   name (can-place-dep.js checkCanPlaceCurrent, CONFLICT, as npm neither
   replaces nor keeps there when the lookup below already failed).  A
   level is refused if its own package wants a version the copy is not,
   or if a package below it that already reaches a copy further up would
   no longer be satisfied; a level whose package peers on the name is
   passed over.  Replacing an older copy, which npm does when every edge
   into it accepts the newer, is not modelled. *)
let rec climb st (x : copy) (m : string * string) u (t : copy) best =
  let onward b = match t.up with Some p -> climb st x m u p b | None -> b in
  if t.up <> None && peers_at st t (fst m) then onward best
  else if Hashtbl.mem t.kids (fst m) || not (fine st x m u t) then best
  else onward (Some t)

let place o (x : copy) (m : string * string) (u : string) =
  let at = Option.value (climb o.st x m u x None) ~default:x in
  let c =
    {
      id = o.ids;
      key = m;
      ver = u;
      up = Some at;
      depth = at.depth + 1;
      path = at.path ^ "/node_modules/" ^ fst m;
      kids = Hashtbl.create 8;
      seen = Hashtbl.create 8;
    }
  in
  o.ids <- o.ids + 1;
  Hashtbl.replace at.kids (fst m) c;
  if not (Hashtbl.mem o.first (m, u)) then Hashtbl.replace o.first (m, u) c;
  o.queue <- DepsQueue.add c o.queue

(* npm resolving x's edge on directory m, which the solver has decided at
   u: nothing happens if x's lookup already finds that copy *)
let settle o (x : copy) (m : string * string) (u : string) =
  match resolve x (fst m) with
  | Some c when c.key = m && c.ver = u -> ()
  | _ -> place o x m u

let dir_of (n : PName.t) =
  match n with
  | Np.Nm.Intermediate (_, _, m) -> fst m
  | Np.Nm.Granular (k, _) -> fst k

(* x's directories the solver has opened and npm has not yet resolved at
   x, in the order npm meets them *)
let open_dirs o ~(assigned : assigned) (x : copy) =
  List.filter
    (fun n ->
      (not (Hashtbl.mem x.seen (dir_of n)))
      && match assigned n with PG.Unselected -> false | _ -> true)
    (L.dirs o.st (x.key, x.ver))
  |> List.sort (fun a b -> collate (dir_of a) (dir_of b))

(* build-ideal-tree.js: #buildDepStep pops the copy that is shallowest in
   node_modules, then first by path (DepsQueue), and places what each of
   its problem edges fetches in the order of the edges' names; each copy
   placed joins the queue.  The replay runs that loop over the solver's
   decisions until it reaches a directory not yet decided, which is the
   one to decide next. *)
let rec advance o ~assigned =
  match o.current with
  | None -> (
      match DepsQueue.min_elt_opt o.queue with
      | None -> None
      | Some x ->
          o.queue <- DepsQueue.remove x o.queue;
          o.current <- Some x;
          advance o ~assigned)
  | Some x -> (
      match open_dirs o ~assigned x with
      | [] ->
          o.current <- None;
          advance o ~assigned
      | n :: _ -> (
          match (n, assigned n) with
          | Np.Nm.Intermediate (_, _, m), PG.Decided (Np.Vs.Orig u) ->
              settle o x m u;
              Hashtbl.replace x.seen (fst m) ();
              Hashtbl.replace o.made n (Np.Vs.Orig u);
              advance o ~assigned
          | _, PG.Decided _ ->
              Hashtbl.replace x.seen (dir_of n) ();
              advance o ~assigned
          | _ -> Some (n, x)))

(* A backtrack that undid a decision the tree was built from starts the
   replay again from the root, over the decisions that stand. *)
let rec sync o ~(assigned : assigned) =
  match o.decided with
  | (n, v) :: rest
    when match assigned n with
         | PG.Decided w -> not (PVersion.equal v w)
         | _ -> true ->
      if Hashtbl.mem o.made n then restart o;
      o.decided <- rest;
      sync o ~assigned
  | _ -> ()

let is_granular (n, _) = match n with Np.Nm.Granular _ -> true | _ -> false

(* A granular name first, since it has one version and only opens its
   package's directories, then the directory npm resolves next. *)
let next o ~assigned (open_names : (PName.t * int) list) : PName.t =
  sync o ~assigned;
  match List.find_opt is_granular open_names with
  | Some (n, _) -> n
  | None -> (
      match advance o ~assigned with
      | Some (n, x) ->
          o.pending <- Some (n, x);
          n
      | None -> fst (List.hd open_names))

(* the copy whose lookup resolves directory m of p (key k at v) *)
let resolved_at o (n : PName.t) k v =
  match o.pending with
  | Some (n', x) when PName.compare n n' = 0 -> Some x
  | _ -> Hashtbl.find_opt o.first (k, v)

(* npm leaves a slot on a version its tree already holds when the range
   admits it: an edge whose node_modules lookup finds a satisfying copy is
   valid, so #problemEdges fetches nothing for it.  So the copy the
   requirer's lookup finds in the replayed tree outranks both the dist-tag
   and the newest; resolving afresh is what brings in a second copy of a
   package npm's tree already holds.  A peer edge is no different: one the
   lookup already satisfies is skipped (build-ideal-tree.js:1427, 1438),
   and a copy out of the lookup's sight is not reused.  Preference only:
   the filter falls back to the whole candidate list, so nothing that was
   satisfiable stops being so. *)
let reused at (m : string * string) cands =
  let found c =
    match (at, c) with
    | Some x, Np.Vs.Orig u -> (
        match resolve x (fst m) with
        | Some y -> y.key = m && y.ver = u
        | None -> false)
    | _ -> false
  in
  match List.filter found cands with [] -> cands | l -> l

let greatest = function
  | [] -> invalid_arg "greatest"
  | c :: cs ->
      List.fold_left (fun a b -> if PVersion.compare b a > 0 then b else a) c cs

let choose o ~assigned (n : PName.t) (cands : PVersion.t list) : PVersion.t =
  match n with
  | Np.Nm.Granular _ -> greatest cands
  | Np.Nm.Intermediate (k, v, m) ->
      let st = o.st in
      let c =
        Pick.pick st.L.ar (snd m) (reused (resolved_at o n k v) m cands)
      in
      let c =
        if peer_only st (snd k, v) (fst m) then
          replace st ~assigned k v m cands c
        else c
      in
      o.decided <- (n, c) :: o.decided;
      c
