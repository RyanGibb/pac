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

let is_root st (k, v) =
  let r = st.L.root in
  k = (fst r, fst r) && v = snd r

(* what p (key k at v) holds, by key: its dependencies, and for the root
   the mandatory peers those, and its own, install beside them *)
let held st ~assigned k v =
  let deps = by_dir st (snd k, v) in
  let dirs = List.map (fun (d : Np.coq_Dependency) -> d.Np.d_dir) deps in
  let root = is_root st (k, v) in
  let held = Hashtbl.create 16 in
  let rec peers_of q =
    List.iter
      (fun (r : Np.coq_PeerDependency) ->
        if (not r.Np.p_optional) && not (List.mem r.Np.p_name dirs) then
          hold (r.Np.p_name, r.Np.p_name))
      (L.peer_dependencies st q)
  and hold key =
    if not (Hashtbl.mem held key) then (
      let u = decided assigned (Np.Nm.Intermediate (k, v, key)) in
      Hashtbl.replace held key u;
      if root then Option.iter (fun u -> peers_of (snd key, u)) u)
  in
  List.iter
    (fun (d : Np.coq_Dependency) -> hold (d.Np.d_dir, d.Np.d_target))
    deps;
  if root then peers_of (snd k, v);
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

(* The peer ranges npm resolves into p's peer-only directory a from below
   the copies p holds, in the order npm meets them: on behalf of a package
   q that p holds and that peers on a, so that q's own peer is what fills
   the directory, the peers on a of q's dependencies, and of theirs while
   each peers on a too.  They reach the directory through q's sight, but
   only once the copies below q are decided, so choosing a version all of
   them accept here spares the solver a backtrack. *)
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
  let holds rg = function Np.Vs.Orig u -> Np.rgHolds rg u | _ -> false in
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
  snd (List.fold_left step ([], c) (peer_ranges_into st ~assigned k v (fst m)))

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

(* whether x or a copy above it is the copy u at m *)
let rec within_copy (x : copy) (m : string * string) (u : string) =
  (x.key = m && x.ver = u)
  || match x.up with Some p -> within_copy p m u | None -> false

(* npm resolving x's edge on directory m, which the solver has decided at
   u: nothing happens if x's lookup already finds that copy, nor where the
   copy is x itself or above it, which npm closes with a link rather than
   unroll a cycle through one name forever *)
let settle o (x : copy) (m : string * string) (u : string) =
  match resolve x (fst m) with
  | Some c when c.key = m && c.ver = u -> ()
  | _ when within_copy x m u -> ()
  | _ -> place o x m u

let dir_of (n : PName.t) =
  match n with
  | Np.Nm.Intermediate (_, _, m) -> fst m
  | Np.Nm.Granular (k, _) -> fst k
  | Np.Nm.Sight (_, _, a) | Np.Nm.Link (_, _, _, _, a) | Np.Nm.Desc (a, _, _) ->
      a

let is_open (assigned : assigned) n =
  match assigned n with PG.Entailed _ -> true | _ -> false

(* the first link not yet decided that resolves into directory h *)
let open_link o ~(assigned : assigned) h =
  List.find_opt (is_open assigned) (L.links_into o.st h)

(* x's directories the solver has opened and npm has not yet resolved at
   x, in the order npm meets them; a directory only a peer asks for is
   opened by the link that resolves into it *)
let open_dirs o ~(assigned : assigned) (x : copy) =
  List.filter
    (fun n ->
      (not (Hashtbl.mem x.seen (dir_of n)))
      && ((match assigned n with PG.Unselected -> false | _ -> true)
         || open_link o ~assigned n <> None))
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
          match (n, assigned n, open_link o ~assigned n) with
          | _, _, Some l -> Some (l, x)
          | Np.Nm.Intermediate (_, _, m), PG.Decided (Np.Vs.Orig u), None ->
              settle o x m u;
              Hashtbl.replace x.seen (fst m) ();
              Hashtbl.replace o.made n (Np.Vs.Orig u);
              advance o ~assigned
          | _, PG.Decided _, None ->
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
let is_link (n, _) = match n with Np.Nm.Link _ -> true | _ -> false

(* A link whose value is already settled, which the replay has no
   directory for: it reads its holder's sight, or its holder's copy is
   decided, or it has no holder, offering the copy itself or nothing. *)
let eager o ~assigned (n, _) =
  match n with
  | Np.Nm.Link (k, v, _, _, a) -> (
      match L.holder o.st (k, v) a with
      | None | Some (Np.Nm.Sight _) -> true
      | Some h -> ( match assigned h with PG.Decided _ -> true | _ -> false))
  | _ -> false

(* A granular name first, since it has one version and only opens its
   package's directories, then a settled link, then the directory npm
   resolves next; a sight last, once every link into it is decided. *)
let next o ~assigned (open_names : (PName.t * int) list) : PName.t =
  sync o ~assigned;
  match List.find_opt is_granular open_names with
  | Some (n, _) -> n
  | None -> (
      match List.find_opt (eager o ~assigned) open_names with
      | Some (n, _) -> n
      | None -> (
          match advance o ~assigned with
          | Some (n, x) ->
              o.pending <- Some (n, x);
              n
          | None -> (
              match List.find_opt is_link open_names with
              | Some (n, _) -> n
              | None -> fst (List.hd open_names))))

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

let greatest = Pac_common.Order.greatest PVersion.compare
let is_orig = function Np.Vs.Orig _ -> true | _ -> false

(* what npm puts in directory m of p (key k at v), resolved at the copy
   the replay holds for the name n that decides it *)
let fill o ~assigned n k v (m : string * string) cands =
  let st = o.st in
  let c = Pick.pick st.L.ar (snd m) (reused (resolved_at o n k v) m cands) in
  if peer_only st (snd k, v) (fst m) then replace st ~assigned k v m cands c
  else c

let within (assigned : assigned) n x =
  match assigned n with
  | PG.Entailed r -> PG.Ranges.contains x r
  | PG.Decided y -> PVersion.equal x y
  | PG.Unselected -> true

(* A link carries what its holder shows at a into the copy's sight, so its
   value is the holder's: the copy there when there is one, else what npm
   would place there for this peer and for every other link into the same
   directory, whose ranges narrow the directory together as npm's peer set
   does. *)
let choose_link o ~assigned n (k, v) a cands =
  let st = o.st in
  let origs = List.filter (fun c -> c <> Np.Vs.Bot) cands in
  let bot = List.mem Np.Vs.Bot cands in
  let fallback () = if bot then Np.Vs.Bot else List.hd cands in
  match L.holder st (k, v) a with
  | None -> fallback ()
  | Some h -> (
      match (h, assigned h) with
      | _, PG.Decided x -> if List.mem x cands then x else fallback ()
      | Np.Nm.Sight _, PG.Entailed r -> (
          match List.filter (fun x -> PG.Ranges.contains x r) origs with
          | x :: _ -> x
          | [] -> fallback ())
      | Np.Nm.Sight _, PG.Unselected -> fallback ()
      | Np.Nm.Intermediate (_, _, m), sel -> (
          let inside = List.filter (within assigned h) origs in
          let others =
            List.filter (fun l -> PName.compare l n <> 0) (L.links_into st h)
          in
          let agreed =
            List.filter
              (fun x -> List.for_all (fun l -> within assigned l x) others)
              inside
          in
          match (sel, inside) with
          | PG.Unselected, _ when bot -> Np.Vs.Bot
          | _, [] -> fallback ()
          | _ ->
              fill o ~assigned n k v m (if agreed = [] then inside else agreed))
      | _ -> fallback ())

(* A sight no link reads is left Free, so that holders offering different
   versions can share the copy; one that a link reads keeps the value the
   links agree on, and Bot only when they agree on none. *)
let choose o ~assigned (n : PName.t) (cands : PVersion.t list) : PVersion.t =
  match n with
  | Np.Nm.Granular _ | Np.Nm.Desc _ -> greatest cands
  | Np.Nm.Intermediate (k, v, m) ->
      let c = fill o ~assigned n k v m cands in
      o.decided <- (n, c) :: o.decided;
      c
  | Np.Nm.Link (k, v, _, _, a) -> choose_link o ~assigned n (k, v) a cands
  | Np.Nm.Sight _ -> (
      if L.links_into o.st n = [] && List.mem Np.Vs.Free cands then Np.Vs.Free
      else
        match List.filter is_orig cands with
        | [] -> if List.mem Np.Vs.Bot cands then Np.Vs.Bot else List.hd cands
        | l -> greatest l)

(* A link, its holder's directory and the copy's sight are one version
   wherever the sight is read, and each constraint between them is one
   dependency per version, so a random pick that breaks it rules out only
   itself: a peer like @types/node (2364 versions) then costs a conflict
   per version.  A random order therefore picks among the versions the
   others already leave open, and leaves a link that may be Bot at Bot
   while nothing else opens its holder's directory, as npm installs no
   optional peer by itself.  Preference only: an empty filter keeps
   [cands]. *)
let viable st ~assigned (n : PName.t) cands =
  let keep ok = match List.filter ok cands with [] -> cands | l -> l in
  (* what a link into a directory asks of it, when it cannot be Bot *)
  let binds l =
    match (l, assigned l) with
    | _, PG.Decided (Np.Vs.Orig w) -> Some (PVersion.equal (Np.Vs.Orig w))
    | Np.Nm.Link (_, _, m, u, a), PG.Entailed r
      when not (PG.Ranges.contains Np.Vs.Bot r) -> (
        match assigned (Np.Nm.Sight (m, u, a)) with
        | PG.Decided (Np.Vs.Orig y) -> Some (PVersion.equal (Np.Vs.Orig y))
        | _ -> Some (fun x -> PG.Ranges.contains x r))
    | _ -> None
  in
  match n with
  | Np.Nm.Link (k, v, m, u, a) -> (
      match L.holder st (k, v) a with
      | None -> cands
      | Some h ->
          let s = Np.Nm.Sight (m, u, a) in
          let ok x =
            match x with
            | Np.Vs.Bot ->
                within assigned s Np.Vs.Bot || within assigned s Np.Vs.Free
            | Np.Vs.Orig _ ->
                within assigned h x
                && (within assigned s x || within assigned s Np.Vs.Free)
            | Np.Vs.Free -> false
          in
          let unopened =
            match assigned h with PG.Unselected -> true | _ -> false
          in
          if unopened && List.mem Np.Vs.Bot cands && ok Np.Vs.Bot then
            [ Np.Vs.Bot ]
          else keep ok)
  | Np.Nm.Intermediate (k, v, m) -> (
      (* a descriptor another directory has decided binds this one too *)
      let desc_ok =
        match L.desc_name st (snd k, v) m with
        | Some d -> (
            match assigned d with
            | PG.Decided y -> fun x -> x = Np.Vs.Bot || PVersion.equal x y
            | PG.Entailed r -> fun x -> x = Np.Vs.Bot || PG.Ranges.contains x r
            | PG.Unselected -> fun _ -> true)
        | None -> fun _ -> true
      in
      match List.filter_map binds (L.links_into st n) with
      | [] -> keep desc_ok
      | bs ->
          keep (fun x ->
              is_orig x && desc_ok x && List.for_all (fun b -> b x) bs))
  | Np.Nm.Sight _ -> (
      (* a link reading the sight fixes it, Bot included *)
      let reads l =
        match assigned l with
        | PG.Decided x -> Some (PVersion.equal x)
        | _ -> binds l
      in
      match List.filter_map reads (L.links_into st n) with
      | [] -> cands
      | bs -> keep (fun x -> List.for_all (fun b -> b x) bs))
  | Np.Nm.Granular _ | Np.Nm.Desc _ -> cands

(* build-ideal-tree.js places what each copy's problem edges fetch, taking
   copies from a queue ordered by where they sit in node_modules
   (#buildDepStep), and takes for each edge the version npm-pick-manifest
   picks, unless the copy's node_modules lookup already finds one the
   range admits.  The replay rebuilds that tree from the solver's
   decisions, so next names the directory npm resolves next and choose
   picks what npm would put there.  [`Pubgrub] leaves both to PubGrub. *)
let hooks : (L.t, PName.t, PG.selection, PVersion.t) Pac_common.Order.driver =
 fun order st ->
  match order with
  | `Tool ->
      let o = create st in
      Pac_common.Order.make ~next:(next o) ~choose:(choose o) ()
  | `Pubgrub -> Pac_common.Order.make ()
  | `Random seed ->
      let r = Pac_common.Order.random seed in
      let choose = Option.get r.Pac_common.Order.choose in
      {
        r with
        choose =
          Some
            (fun ~assigned n cands ->
              choose ~assigned n (viable st ~assigned n cands));
      }
