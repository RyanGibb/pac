(* npm solving over the verified pipeline, cargo_solve/apk_solve-style:
   packuments live in hashtables; every lookup is answered from a small
   Inst sub-instance in the shape one of Npm.v's four lookup theorems
   justifies,
   pushed through the extracted Npm reduction into Core; PubGrub solves
   the accumulated core graph lazily, and the solution comes back through
   npmResolution and npmParents.  Trusted here (TCB): the parser, the
   version comparator, the registry fetch, the policy constants below,
   and the plumbing. *)

module E = Pac
module P = Npm_parse

let c2r c = if c < 0 then E.Lt else if c > 0 then E.Gt else E.Eq
let r2c = function E.Lt -> -1 | E.Eq -> 0 | E.Gt -> 1

module StringOT = struct
  type t = string

  let compare a b = c2r (String.compare a b)
  let eq_dec (a : string) b = String.equal a b
end

module NVerOT = struct
  type t = string

  let compare a b = c2r (Npm_version.compare a b)
  let eq_dec a b = Npm_version.compare a b = 0
end

(* SemverMatch: the two tests V.compare cannot express.  Both take the
   candidate version first and the comparator's constant second. *)
module PM = struct
  let isPre = Npm_version.is_prerelease
  let sameCore = Npm_version.same_core
end

module Np = E.Npm (StringOT) (NVerOT) (StringOT) (StringOT) (PM)
module R = Np.Reduction
module T = Np.T

(* ---- policy ------------------------------------------------------------

   Each is a decision the calculus leaves to the frontend; none is forced
   by the theory, and each is a place where this driver may disagree with
   npm. *)

(* The platform valuation.  os/cpu/libc are gates against a fixed
   environment; an unset variable fails its gate.  engines is not gated
   at all -- npm does not consult it when selecting versions -- so the
   parser creates no gate over "node" or "npm" and this has no entry for
   them.  A real frontend would read these from the host. *)
let host_os = "linux"
let host_cpu = "x64"
let host_libc = "glibc"

let rho (x : string) : string option =
  match x with
  | "os" -> Some host_os
  | "cpu" -> Some host_cpu
  | "libc" -> Some host_libc
  | _ -> None

(* devDependencies participate only from the root package: that is
   depActive's rule in the theory, not a choice made here, but only the
   root's packument is parsed for them. *)

(* Prerelease versions stay in the repository.  The calculus admits one
   only inside a comparator set that names a prerelease at the same
   release core, so no filtering is needed here. *)

(* ---- the archive ---- *)

type archive = {
  cache : string;
  offline : bool;
  (* false under --omit=optional: an optional row is then dropped
     outright rather than only when the registry cannot satisfy it *)
  optional : bool;
  pkgs : (string, P.ver list) Hashtbl.t;
  latest : (string, string) Hashtbl.t;
  entry : (string * string, P.ver) Hashtbl.t;
  (* peer rows indexed by the directory they name, for peerRowsNamed *)
  peer_by_name : (string, (string * string) * P.peer) Hashtbl.t;
  (* dependency rows indexed by the key they introduce, for the granular
     version lookup's key test *)
  dep_by_key : (string * string, (string * string) * P.dep) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_fetched : int;
  mutable n_opt_dropped : int;
}

let empty_archive ?(optional = true) ~cache ~offline () =
  {
    cache;
    offline;
    optional;
    pkgs = Hashtbl.create 1024;
    latest = Hashtbl.create 1024;
    entry = Hashtbl.create 16384;
    peer_by_name = Hashtbl.create 4096;
    dep_by_key = Hashtbl.create 16384;
    n_names = 0;
    n_vers = 0;
    n_fetched = 0;
    n_opt_dropped = 0;
  }

(* ---- registry access ---- *)

(* npm has no bulk index, so a packument is fetched per name and cached;
   a cached file is reused, which is what makes runs repeatable and lets
   the tests run with no network at all. *)
let escape (n : string) : string =
  String.concat "%2F" (String.split_on_char '/' n)

let cache_file ar n = Filename.concat ar.cache (escape n ^ ".json")

let rec mkdir_p d =
  if d <> "" && d <> "/" && d <> "." && not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Sys.mkdir d 0o755 with Sys_error _ -> ()
  end

let fetch ar (n : string) : string option =
  let f = cache_file ar n in
  if Sys.file_exists f then Some f
  else if ar.offline then None
  else begin
    mkdir_p ar.cache;
    let tmp = f ^ ".tmp" in
    let url = "https://registry.npmjs.org/" ^ escape n in
    let cmd =
      (* a name with no packument is normal here: the registry is full of
         manifests naming packages that were never published *)
      Printf.sprintf "curl -fsSL %s -o %s 2>/dev/null" (Filename.quote url)
        (Filename.quote tmp)
    in
    ar.n_fetched <- ar.n_fetched + 1;
    if Sys.command cmd = 0 then begin
      Sys.rename tmp f;
      Some f
    end
    else begin
      (try Sys.remove tmp with Sys_error _ -> ());
      None
    end
  end

let index_ver ar (v : P.ver) =
  let p = (v.P.v_name, v.P.v_vers) in
  Hashtbl.replace ar.entry p v;
  List.iter (fun r -> Hashtbl.add ar.peer_by_name r.P.p_name (p, r)) v.P.v_peers;
  List.iter
    (fun d -> Hashtbl.add ar.dep_by_key (d.P.d_dir, d.P.d_target) (p, d))
    v.P.v_deps

let load_name ar ~(root : bool) (n : string) : P.ver list =
  match Hashtbl.find_opt ar.pkgs n with
  | Some vs -> vs
  | None ->
      let vs =
        match fetch ar n with
        | None -> []
        | Some f -> (
            match P.load ~root f with
            | None -> []
            | Some pk ->
                (match pk.P.pk_latest with
                | Some l -> Hashtbl.replace ar.latest n l
                | None -> ());
                (* the packument's "name" is authoritative; a manifest
                   with a different one is not this package's *)
                List.map (fun v -> { v with P.v_name = n }) pk.P.pk_vers)
      in
      Hashtbl.replace ar.pkgs n vs;
      ar.n_names <- ar.n_names + 1;
      ar.n_vers <- ar.n_vers + List.length vs;
      List.iter (index_ver ar) vs;
      vs

let versions_of ar n =
  List.map (fun (v : P.ver) -> v.P.v_vers) (load_name ar ~root:false n)

let meta ar p : P.ver option = Hashtbl.find_opt ar.entry p

(* There is no cone pass: the transitive closure over every version of
   every dependency is most of the registry, so a packument is fetched
   only when a sub-instance actually reads that name.  That is sound
   because a name only ever reaches one through a row of a package already
   loaded -- an exit edge names the key its own intermediate carries, and
   a peer edge names a directory its own declarer asked for. *)

(* ---- parse-AST -> extracted terms ---- *)

let xop : Npm_version.op -> E.cmpOp = function
  | Npm_version.Ge -> E.OpGe
  | Npm_version.Gt -> E.OpGt
  | Npm_version.Le -> E.OpLe
  | Npm_version.Lt -> E.OpLt
  | Npm_version.Eq -> E.OpEq
  | Npm_version.Ne -> E.OpNe

let xcomp : Npm_version.comparator -> Np.coq_Comparator = function
  | Npm_version.Any -> Np.CAny
  | Npm_version.Cmp (o, c) -> Np.COp (xop o, c)

let xrange (rg : Npm_version.range) : Np.coq_Range =
  List.map (fun cs -> List.map xcomp cs) rg

let rec xgate : P.gate -> Np.coq_Gate = function
  | P.GTrue -> Np.GTrue
  | P.GFalse -> Np.GFalse
  | P.GCmp (o, x, y) -> Np.GCmp (xop o, x, y)
  | P.GAnd (a, b) -> Np.GAnd (xgate a, xgate b)
  | P.GOr (a, b) -> Np.GOr (xgate a, xgate b)
  | P.GNot a -> Np.GNot (xgate a)

let xdep (d : P.dep) : Np.coq_DepRow =
  {
    Np.d_dir = d.P.d_dir;
    Np.d_target = d.P.d_target;
    Np.d_range = xrange d.P.d_range;
    Np.d_dev = d.P.d_dev;
  }

let xpeer (r : P.peer) : Np.coq_PeerRow =
  {
    Np.p_name = r.P.p_name;
    Np.p_range = xrange r.P.p_range;
    Np.p_optional = r.P.p_optional;
  }

(* ---- the solver state ---- *)

type state = {
  ar : archive;
  root : string * string;
  ovr : (string * Np.coq_Range) list;
  rows : (string * string, Np.coq_DepRow list) Hashtbl.t;
  prows : (string * string, Np.coq_PeerRow list) Hashtbl.t;
  grows : (string * string, Np.coq_Gate list) Hashtbl.t;
  repo_at : (string, Np.RepoSet.t) Hashtbl.t;
  plat_at : (string, ((string * string) * Np.coq_Gate) list) Hashtbl.t;
  (* the sets a sub-instance hands the calculus are sorted lists, so
     building one is quadratic; they are keyed by the names read rather than
     by the package reading them, because consecutive versions read the
     same *)
  repo_of : (string list, Np.RepoSet.t) Hashtbl.t;
  plat_of : (string list, ((string * string) * Np.coq_Gate) list) Hashtbl.t;
  vcache : (Np.Nm.name, Np.Vs.version list) Hashtbl.t;
  (* the optional-row verdict, keyed by what decides it *)
  opt_keep : (string * string, bool) Hashtbl.t;
  mutable n_lookups : int;
}

let mk_state ar root =
  let ovr =
    match meta ar root with
    | Some v -> List.map (fun (n, rg) -> (n, xrange rg)) v.P.v_ovr
    | None -> []
  in
  {
    ar;
    root;
    ovr;
    rows = Hashtbl.create 16384;
    prows = Hashtbl.create 16384;
    grows = Hashtbl.create 16384;
    repo_at = Hashtbl.create 4096;
    plat_at = Hashtbl.create 4096;
    repo_of = Hashtbl.create 4096;
    plat_of = Hashtbl.create 4096;
    vcache = Hashtbl.create 65536;
    opt_keep = Hashtbl.create 1024;
    n_lookups = 0;
  }

let peer_rows st p =
  match Hashtbl.find_opt st.prows p with
  | Some l -> l
  | None ->
      let l =
        match meta st.ar p with
        | None -> []
        | Some v -> List.map xpeer v.P.v_peers
      in
      Hashtbl.replace st.prows p l;
      l

let gate_rows st p =
  match Hashtbl.find_opt st.grows p with
  | Some l -> l
  | None ->
      let l =
        match meta st.ar p with
        | None -> []
        | Some v -> List.map xgate v.P.v_gates
      in
      Hashtbl.replace st.grows p l;
      l

(* repoPreimage I ns and platPreimage I ns at one name *)
let repo_at st (n : string) : Np.RepoSet.t =
  match Hashtbl.find_opt st.repo_at n with
  | Some s -> s
  | None ->
      let s =
        Np.RepoSet.ofList (List.map (fun v -> (n, v)) (versions_of st.ar n))
      in
      Hashtbl.replace st.repo_at n s;
      s

let plat_at st (n : string) =
  match Hashtbl.find_opt st.plat_at n with
  | Some l -> l
  | None ->
      let l =
        List.concat_map
          (fun v ->
            let p = (n, v) in
            List.map (fun g -> (p, g)) (gate_rows st p))
          (versions_of st.ar n)
      in
      Hashtbl.replace st.plat_at n l;
      l

let repo_of st (ns : string list) : Np.RepoSet.t =
  let ns = List.sort_uniq String.compare ns in
  match Hashtbl.find_opt st.repo_of ns with
  | Some s -> s
  | None ->
      let s = Np.RepoSet.unions (List.map (repo_at st) ns) in
      Hashtbl.replace st.repo_of ns s;
      s

let plat_of st (ns : string list) =
  let ns = List.sort_uniq String.compare ns in
  match Hashtbl.find_opt st.plat_of ns with
  | Some l -> l
  | None ->
      let l = List.concat_map (plat_at st) ns in
      Hashtbl.replace st.plat_of ns l;
      l

let mk_inst st ~repo ~plat ~deps ~peers : Np.coq_Inst =
  {
    Np.inst_repo = repo;
    Np.inst_dep = deps;
    Np.inst_peer = peers;
    Np.inst_plat = plat;
    Np.inst_ovr = st.ovr;
    Np.inst_root = st.root;
  }

(* ---- optionalDependencies ----------------------------------------------

   An optional row is an ordinary dependency that npm abandons in exactly
   one situation: the target cannot be resolved.  #pruneFailedOptional
   then makes the whole optionalSet inert, and nothing else drops the row
   -- a peer conflict over an optional dependency is an ordinary
   ERESOLVE.  So the test is whether any version of the target is
   available to satisfy the range, and it lives here rather than in the
   parser, which sees one manifest at a time and has no registry.

   Available, not merely published: engines/os/cpu are an availability
   cut in this model, effRepo removing a gated-out package from the
   repository outright, so for resolution it does not exist.  npm reaches
   the same outcome by a different route -- ENOTARGET at fetch for a
   range nothing matches, EBADPLATFORM at reify for a platform mismatch,
   both pruned because the row is optional -- and the outcome is what is
   modelled.  Testing published versions instead would make the commonest
   optional dependency in the ecosystem, a darwin-only binary such as
   fsevents, a false unsatisfiable on every other platform.

   The instance is the one effRepo reads and no more: it takes inst_repo
   and the gate rows in inst_plat, so this is granSubInst's narrowing to a
   single name -- repoAt and platAt at the target -- with the row and
   peer fields empty, since nothing here consults them.  Both halves are
   already memoized per name, so the check reuses whatever the
   sub-instances built.

   It is applied where a row is read rather than where a packument is
   loaded, because deciding at load time would have to resolve every
   optional target of every version eagerly -- the cone pass the driver
   deliberately does not do, and it would not even terminate on a cycle.
   Read lazily it costs nothing: the target of a row that survives is a
   slot target the sub-instance was going to load anyway.

   Evaluation is the calculus's throughout, via the extracted effRepo and
   rgHolds and under the same flat override the calculus would apply; the
   mirror in npm_version.ml is not used. *)
let dep_keep st (d : P.dep) : bool =
  (not d.P.d_optional)
  || st.ar.optional
     &&
     let n = d.P.d_target in
     let key = (n, Npm_version.string_of_range d.P.d_range) in
     match Hashtbl.find_opt st.opt_keep key with
     | Some b -> b
     | None ->
         let rg =
           match List.assoc_opt n st.ovr with
           | Some rg -> rg
           | None -> xrange d.P.d_range
         in
         let inst =
           mk_inst st ~repo:(repo_at st n) ~plat:(plat_at st n) ~deps:[]
             ~peers:[]
         in
         let b =
           Np.VSet.exists_ (Np.rgHolds rg)
             (Np.realVersions (Np.effRepo rho inst) n)
         in
         if not b then st.ar.n_opt_dropped <- st.ar.n_opt_dropped + 1;
         Hashtbl.replace st.opt_keep key b;
         b

let dep_rows st p =
  match Hashtbl.find_opt st.rows p with
  | Some l -> l
  | None ->
      let l =
        match meta st.ar p with
        | None -> []
        | Some v -> List.map xdep (List.filter (dep_keep st) v.P.v_deps)
      in
      Hashtbl.replace st.rows p l;
      l

(* the rows introducing key k, for granSubInst; the same filter as dep_rows, so
   the two views of a package's rows cannot disagree about keysOf *)
let dep_rows_by_key st (k : string * string) =
  List.filter_map
    (fun (p, d) -> if dep_keep st d then Some (p, xdep d) else None)
    (Hashtbl.find_all st.ar.dep_by_key k)

(* depRows I p: the rows depActive keeps, i.e. dev rows only at the root *)
let active_rows st p =
  List.filter
    (fun (d : Np.coq_DepRow) -> (not d.Np.d_dev) || p = st.root)
    (dep_rows st p)

let own_dep_rows st p = List.map (fun d -> (p, d)) (dep_rows st p)
let own_peer_rows st p = List.map (fun r -> (p, r)) (peer_rows st p)

(* slotTargets I p *)
let slot_targets st p =
  List.sort_uniq String.compare
    (List.map (fun (d : Np.coq_DepRow) -> d.Np.d_target) (active_rows st p))

(* peerNamesAt I q *)
let peer_names_at st q =
  List.sort_uniq String.compare
    (List.map (fun (r : Np.coq_PeerRow) -> r.Np.p_name) (peer_rows st q))

(* peerRowsNamed I n *)
let peer_rows_named st (n : string) =
  List.map (fun (p, r) -> (p, xpeer r)) (Hashtbl.find_all st.ar.peer_by_name n)

(* ---- the four sub-instances, one per lookup theorem ---- *)

(* versions_lookupGran: granSubInst I k cuts the repository to the key's
   registry name, and platPreimage is keyed by package, so the gate rows
   that come with it are exactly those of the packages that survive.  Two
   narrowings below are the driver's own.  keysOf is a union of one key
   per row plus the root's, and the granular lookup asks it only whether
   it contains k, so rows that cannot introduce k are dropped.  The lookup
   asks the repository only whether the looked-up version is available, so
   it is cut to that one package -- and platPreimage then selects that
   package's gate rows by itself. *)
let gran_sub_inst st (k : string * string) (w : string) =
  let p = (snd k, w) in
  let repo =
    if List.mem w (versions_of st.ar (snd k)) then
      Np.RepoSet.add p Np.RepoSet.empty
    else Np.RepoSet.empty
  in
  let plat = List.map (fun g -> (p, g)) (gate_rows st p) in
  let deps = dep_rows_by_key st k in
  let peers = if fst k = snd k then peer_rows_named st (fst k) else [] in
  mk_inst st ~repo ~plat ~deps ~peers

(* versions_lookupInt: intSubInst I p m is p's own dependency rows, the
   peer rows naming the key's directory, and the repository and gates at
   the key's registry name together with p's slot targets. *)
let int_sub_inst st (p : string * string) (m : string * string) =
  let ns = snd m :: slot_targets st p in
  mk_inst st ~repo:(repo_of st ns) ~plat:(plat_of st ns)
    ~deps:(own_dep_rows st p)
    ~peers:(peer_rows_named st (fst m))

(* dependees_lookupGran: pkgSubInst I p is p's own dependency rows, its own
   peer rows, and the repository and gates at their targets.  The peer
   rows are there for the root, whose granular node carries the edges
   that install its own peers; for any other package rootPeerEdges tests
   the whole package and emits nothing, so they are inert. *)
let pkg_sub_inst st (p : string * string) =
  let ns = slot_targets st p @ peer_names_at st p in
  mk_inst st ~repo:(repo_of st ns) ~plat:(plat_of st ns)
    ~deps:(own_dep_rows st p) ~peers:(own_peer_rows st p)

(* dependees_lookupInt: peerSubInst I p m u is p's own dependency rows, the
   peer rows of the dependee that was selected, and the repository and
   gates at p's slot targets and at the directories those peers name.
   This is the second hop npm's peer auto-installation costs. *)
let peer_sub_inst st (p : string * string) (m : string * string) (u : string) =
  let q = (snd m, u) in
  let ns = slot_targets st p @ peer_names_at st q in
  mk_inst st ~repo:(repo_of st ns) ~plat:(plat_of st ns)
    ~deps:(own_dep_rows st p) ~peers:(own_peer_rows st q)

(* ---- the lookups, answered by the extracted calculus ---- *)

let versions st (n : Np.Nm.name) : Np.Vs.version list =
  match Hashtbl.find_opt st.vcache n with
  | Some l -> l
  | None ->
      st.n_lookups <- st.n_lookups + 1;
      let l =
        match n with
        | Np.Nm.Granular (k, w) ->
            T.VSet.elements (R.versions rho (gran_sub_inst st k w) n)
        | Np.Nm.Intermediate (k, v, m) ->
            T.VSet.elements (R.versions rho (int_sub_inst st (snd k, v) m) n)
      in
      Hashtbl.replace st.vcache n l;
      l

let dependees st (s : T.Pkg.t) : T.Dependees.t list =
  st.n_lookups <- st.n_lookups + 1;
  let hs =
    match s with
    | Np.Nm.Granular (k, _), Np.Vs.Orig v ->
        R.dependees rho (pkg_sub_inst st (snd k, v)) s
    | Np.Nm.Intermediate (k, v, m), Np.Vs.Orig u ->
        R.dependees rho (peer_sub_inst st (snd k, v) m u) s
    | _ -> T.DependeesSet.empty
  in
  T.DependeesSet.elements hs

(* ---- PubGrub ---- *)

module PName = struct
  type t = Np.Nm.name

  let compare a b = r2c (Np.Nm.compare a b)

  let pp_key fmt ((a, t) : string * string) =
    if a = t then Format.fprintf fmt "%s" a
    else Format.fprintf fmt "%s(npm:%s)" a t

  let pp fmt (n : t) =
    match n with
    | Np.Nm.Granular (k, w) -> Format.fprintf fmt "%a@%s" pp_key k w
    | Np.Nm.Intermediate (k, v, m) ->
        Format.fprintf fmt "<%a@%s=>%a>" pp_key k v pp_key m
end

module PVersion = struct
  type t = Np.Vs.version

  let compare a b = r2c (Np.Vs.compare a b)

  let pp fmt (v : t) =
    match v with
    | Np.Vs.Orig v -> Format.fprintf fmt "%s" v
    | Np.Vs.Gran w -> Format.fprintf fmt "gran:%s" w
end

module PG = Pubgrub.Make (PName) (PVersion)

let greatest = function
  | [] -> invalid_arg "greatest"
  | c :: cs ->
      List.fold_left (fun a b -> if PVersion.compare b a > 0 then b else a) c cs

(* npm-pick-manifest offers dist-tags.latest before the highest version
   the range admits, and takes it whenever the range admits it; only the
   ordering differs from ours, so a package published ahead of its own
   latest tag no longer drags its newest release in.  Preference only:
   the tag is consulted inside the candidates, never outside them. *)
let tagged st (n : string) (cands : PVersion.t list) : PVersion.t option =
  match Hashtbl.find_opt st.ar.latest n with
  | None -> None
  | Some l ->
      let l = Np.Vs.Orig l in
      List.find_opt (fun c -> PVersion.compare c l = 0) cands

(* A directory no dependency row of p names: only a peer asks for it, so
   childCands offers every published version of the target and nothing
   narrows the slot but the peer ranges. *)
let peer_only st p (a : string) =
  not
    (List.exists (fun (d : Np.coq_DepRow) -> d.Np.d_dir = a) (active_rows st p))

(* Is the candidate's own granular node already carried?  It holds
   exactly one version, so any assignment to it is that version. *)
let carried ~assigned (m : string * string) (c : PVersion.t) =
  match c with
  | Np.Vs.Gran _ -> false
  | Np.Vs.Orig u -> (
      match assigned (Np.Nm.Granular (m, u)) with
      | PG.Unselected -> false
      | PG.Decided w -> PVersion.compare w c = 0
      | PG.Entailed r -> PG.Ranges.contains c r)

(* npm fills a peer slot from the tree before resolving it, so a version
   the partial solution already carries outranks both the dist-tag and
   the newest; resolving afresh is what brings in a second tree of a
   package the answer already holds.  Preference only, as in
   deb_solve's alt_carried: the filter falls back to the whole candidate
   list, so nothing that was satisfiable stops being so. *)
let choose st ~assigned (n : PName.t) (cands : PVersion.t list) : PVersion.t =
  match n with
  | Np.Nm.Granular _ -> greatest cands
  | Np.Nm.Intermediate (k, v, m) -> (
      let cands =
        if peer_only st (snd k, v) (fst m) then
          match List.filter (carried ~assigned m) cands with
          | [] -> cands
          | reused -> reused
        else cands
      in
      match tagged st (snd m) cands with Some c -> c | None -> greatest cands)

type result = {
  installs : ((string * string) * string) list;
  tree : (((string * string) * string) * ((string * string) * string)) list;
  nodes : int;
  lookups : int;
}

let solve ?(debug = false) ar (root : string * string) =
  Pubgrub.set_debug debug;
  let st = mk_state ar root in
  let root_key = (fst root, fst root) in
  let root_n = Np.Nm.Granular (root_key, snd root) in
  let versions n = versions st n in
  (* the decisive memoization: PubGrub asks for the same node's
     dependencies over and over during propagation *)
  let cache = Hashtbl.create 65536 in
  let dependencies n (u : Np.Vs.version) =
    match Hashtbl.find_opt cache (n, u) with
    | Some r -> r
    | None ->
        let r =
          List.map
            (fun ((m, vs) : T.Dependees.t) ->
              (m, PG.Ranges.of_list (T.VSet.elements vs)))
            (dependees st (n, u))
        in
        Hashtbl.replace cache (n, u) r;
        r
  in
  match
    PG.solve ~choose:(choose st) ~vers:versions ~deps:dependencies
      [ (root_n, PG.Ranges.of_list [ Np.Vs.Orig (snd root) ]) ]
  with
  | Error inc ->
      Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
      None
  | Ok sol ->
      let s = T.PkgSet.ofList sol in
      (* back through the proved decoders *)
      let installs = Np.PkgSet.elements (R.npmResolution s) in
      let tree = Np.Conc.ParentRel.elements (R.npmParents s) in
      Some
        {
          installs = List.sort compare installs;
          tree = List.sort compare tree;
          nodes = List.length sol;
          lookups = st.n_lookups;
        }
