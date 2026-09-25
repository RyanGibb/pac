(* npm solving over the verified pipeline, cargo_solve/apk_solve-style:
   packuments live in hashtables; every lookup is answered from a small
   Inst sub-instance in the shape one of Npm.v's four lookup theorems
   justifies (the granular one narrowed further, at gran_sub_inst),
   pushed through the extracted Npm reduction into Core; PubGrub solves
   the accumulated core graph lazily, and the solution comes back through
   npmResolution and npmParents.  Trusted here (TCB): the parser, the
   version comparator, the engines evaluation (Npm_version.holds_pre),
   the registry fetch, the policy constants below, PubGrub, whose
   solution is decoded unchecked, and the plumbing. *)

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

(* SemverMatch: the two tests V.compare cannot express.  sameCore takes
   the candidate version first and the comparator's constant second. *)
module PM = struct
  let isPre = Npm_version.is_prerelease
  let sameCore = Npm_version.same_core
end

module Np = E.Npm (StringOT) (NVerOT) (PM)
module R = Np.Reduction
module T = Np.T

(* ---- policy ------------------------------------------------------------

   Each is a decision the calculus leaves to the frontend; none is forced
   by the theory, and each is a place where this driver may disagree with
   npm. *)

(* No platform valuation.  npm chooses versions without os, cpu or libc
   -- they appear nowhere in npm-pick-manifest -- and tests them only
   once the tree is built (#checkEngineAndPlatform): EBADPLATFORM for a
   required package, inert for an optional one, which the lockfile still
   records.  So the parser reads none of them and nothing cuts the
   repository. *)

(* The host npm-pick-manifest ranks engines against.  npm always has one,
   arborist passing process.version as nodeVersion and the CLI its own
   version as npmVersion, but nothing here can read a node that need not
   be installed, so an unset half leaves that sub-key untested exactly as
   checkEngine does for a null version: every candidate then passes and
   the engine keys tie, leaving deprecated and semver to decide.  A
   correspondence harness has to supply both, as eval/cargo does for
   --rust-version, or the two sides rank by different rules. *)
let node_version : string option = None
let npm_version : string option = None

(* semver takes a leading v or = on the version it tests, which is the
   shape `node --version` prints; our comparator parses digits only. *)
let host_version (s : string) : string =
  if s <> "" && (s.[0] = 'v' || s.[0] = 'V' || s.[0] = '=') then
    String.sub s 1 (String.length s - 1)
  else s

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
  (* false under --omit=optional: an optional dependency is then dropped
     outright rather than only when the registry cannot satisfy it *)
  optional : bool;
  node : string option;
  npm : string option;
  pkgs : (string, P.ver list) Hashtbl.t;
  latest : (string, string) Hashtbl.t;
  tags : (string, (string * string) list) Hashtbl.t;
  entry : (string * string, P.ver) Hashtbl.t;
  (* peer dependencies indexed by the directory they name, for
     peerDependenciesNamed *)
  peer_by_name : (string, (string * string) * P.peer) Hashtbl.t;
  (* dependencies indexed by the key they introduce, for the granular
     version lookup's key test *)
  dep_by_key : (string * string, (string * string) * P.dep) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_fetched : int;
  mutable n_opt_dropped : int;
}

let empty_archive ?(optional = true) ?(node = node_version)
    ?(npm = npm_version) ~cache ~offline () =
  {
    cache;
    offline;
    optional;
    node = Option.map host_version node;
    npm = Option.map host_version npm;
    pkgs = Hashtbl.create 1024;
    latest = Hashtbl.create 1024;
    tags = Hashtbl.create 1024;
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
    (* one scratch file per process: processes sharing a cache fetch the
       same name at once, and a shared one is renamed away under the
       other; the rename stays within the directory, so it is atomic *)
    let tmp = Printf.sprintf "%s.%d.tmp" f (Unix.getpid ()) in
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
                Hashtbl.replace ar.tags n pk.P.pk_tags;
                (* the name fetched under is authoritative: a manifest's
                   own "name" is overwritten, not checked *)
                List.map (fun v -> { v with P.v_name = n }) pk.P.pk_vers)
      in
      Hashtbl.replace ar.pkgs n vs;
      ar.n_names <- ar.n_names + 1;
      ar.n_vers <- ar.n_vers + List.length vs;
      List.iter (index_ver ar) vs;
      vs

let versions_of ar n =
  List.map (fun (v : P.ver) -> v.P.v_vers) (load_name ar ~root:false n)

(* the version a dist-tag names, which arborist's #add reads through
   npm-pick-manifest (index.js, `wanted && type === 'tag'`): the tagged
   version exactly, whatever its engines or deprecation *)
let dist_tag ar (n : string) (tag : string) : string option =
  ignore (load_name ar ~root:false n);
  Option.bind (Hashtbl.find_opt ar.tags n) (List.assoc_opt tag)

(* The query is published nowhere, so it enters the archive as the only
   version of its name; a registry package of that name is then out of
   reach, as it would be had it been the root. *)
let add_root ar (v : P.ver) : string * string =
  Hashtbl.replace ar.pkgs v.P.v_name [ v ];
  ar.n_names <- ar.n_names + 1;
  ar.n_vers <- ar.n_vers + 1;
  index_ver ar v;
  (v.P.v_name, v.P.v_vers)

let meta ar p : P.ver option = Hashtbl.find_opt ar.entry p

(* checkEngine, npm-install-checks/lib/index.js: engines.node and
   engines.npm are the two sub-keys it tests, and a null host version
   passes its own sub-key rather than failing it, so a package declaring
   a requirement we have no host for is ranked as though it declared
   none. *)
let engine_ok ar (p : string * string) : bool =
  match meta ar p with
  | None -> true
  | Some v ->
      let ok host rg =
        match (host, rg) with
        | Some h, Some rg -> Npm_version.holds_pre h rg
        | _ -> true
      in
      ok ar.node v.P.v_eng_node && ok ar.npm v.P.v_eng_npm

let deprecated ar (p : string * string) : bool =
  match meta ar p with None -> false | Some v -> v.P.v_deprecated

(* There is no cone pass: the transitive closure over every version of
   every dependency is most of the registry, so a packument is fetched
   only when a sub-instance actually reads that name.  That is sound
   because a name only ever reaches one through a declaration of a
   package already loaded -- an exit edge names the key its own
   intermediate carries, and a peer edge names a directory its own
   declarer asked for. *)

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

(* This is what npm does for the literal range "*", and for an empty one,
   which it reads as "*": npm-pick-manifest's special case (lib/index.js,
   range === '*') takes dist-tags.latest even when that is a prerelease,
   provided it is neither deprecated nor refused by the host's engines,
   where semver itself admits no prerelease under "*".  Our ranges admit a
   prerelease only beside a comparator naming one at its release core, so
   such a range is read as "* || =latest", which admits that one prerelease
   and no other.  The target's packument decides it, so the rewrite is made
   here rather than in the parser, which sees one manifest at a time. *)
let star_range ar ~star (t : string) (rg : Npm_version.range) :
    Npm_version.range =
  if not star then rg
  else (
    ignore (load_name ar ~root:false t);
    match Hashtbl.find_opt ar.latest t with
    | Some l
      when Npm_version.is_prerelease l
           && Hashtbl.mem ar.entry (t, l)
           && (not (deprecated ar (t, l)))
           && engine_ok ar (t, l) ->
        rg @ [ [ Npm_version.Cmp (Npm_version.Eq, l) ] ]
    | _ -> rg)

let dep_range ar (d : P.dep) : Np.coq_Range =
  xrange (star_range ar ~star:d.P.d_star d.P.d_target d.P.d_range)

let xdep ar (d : P.dep) : Np.coq_Dependency =
  {
    Np.d_dir = d.P.d_dir;
    Np.d_target = d.P.d_target;
    Np.d_range = dep_range ar d;
    Np.d_dev = d.P.d_dev;
  }

(* a peer names a directory, and npm fetches the peer's range from the
   packument of that name *)
let xpeer ar (r : P.peer) : Np.coq_PeerDependency =
  {
    Np.p_name = r.P.p_name;
    Np.p_range =
      xrange (star_range ar ~star:r.P.p_star r.P.p_name r.P.p_range);
    Np.p_optional = r.P.p_optional;
  }

(* ---- the solver state ---- *)

type state = {
  ar : archive;
  root : string * string;
  ovr : (string * Np.coq_Range) list;
  dep_tbl : (string * string, Np.coq_Dependency list) Hashtbl.t;
  peer_tbl : (string * string, Np.coq_PeerDependency list) Hashtbl.t;
  repo_at : (string, Np.RepoSet.t) Hashtbl.t;
  (* keyed by the names read rather than by the package reading them, so
     packages that read the same names share one set *)
  repo_of : (string list, Np.RepoSet.t) Hashtbl.t;
  vcache : (Np.Nm.name, Np.Vs.version list) Hashtbl.t;
  (* the optional-dependency verdict, keyed by what decides it *)
  opt_keep : (string * string, bool) Hashtbl.t;
  (* each package's directories, as far as the solver has looked: the
     intermediates its granular node and its directories point to *)
  dirs : ((string * string) * string, Np.Nm.name list) Hashtbl.t;
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
    dep_tbl = Hashtbl.create 16384;
    peer_tbl = Hashtbl.create 16384;
    repo_at = Hashtbl.create 4096;
    repo_of = Hashtbl.create 4096;
    vcache = Hashtbl.create 65536;
    opt_keep = Hashtbl.create 1024;
    dirs = Hashtbl.create 4096;
    n_lookups = 0;
  }

let peer_dependencies st p =
  match Hashtbl.find_opt st.peer_tbl p with
  | Some l -> l
  | None ->
      let l =
        match meta st.ar p with
        | None -> []
        | Some v -> List.map (xpeer st.ar) v.P.v_peers
      in
      Hashtbl.replace st.peer_tbl p l;
      l

(* repoPreimage I ns at one name *)
let repo_at st (n : string) : Np.RepoSet.t =
  match Hashtbl.find_opt st.repo_at n with
  | Some s -> s
  | None ->
      let s =
        Np.RepoSet.ofList (List.map (fun v -> (n, v)) (versions_of st.ar n))
      in
      Hashtbl.replace st.repo_at n s;
      s

let repo_of st (ns : string list) : Np.RepoSet.t =
  let ns = List.sort_uniq String.compare ns in
  match Hashtbl.find_opt st.repo_of ns with
  | Some s -> s
  | None ->
      let s = Np.RepoSet.unions (List.map (repo_at st) ns) in
      Hashtbl.replace st.repo_of ns s;
      s

let mk_inst st ~repo ~deps ~peers : Np.coq_Inst =
  {
    Np.inst_repo = repo;
    Np.inst_dep = deps;
    Np.inst_peer = peers;
    Np.inst_ovr = st.ovr;
    Np.inst_root = st.root;
  }

(* ---- optionalDependencies ----------------------------------------------

   An optional entry is an ordinary dependency that this driver abandons
   in one situation only: no published version of the target matches the
   range (ENOTARGET).  npm abandons more.  #pruneFailedOptional makes the
   dependency's whole optional set inert when anything in it fails to
   load, a transitive ENOTARGET, a network failure or an allow-* gate
   included, and #checkEngineAndPlatform does the same when anything in
   it fails engines or platform; none of these is modelled.  A peer
   conflict over an optional dependency is an ordinary ERESOLVE.  The
   test lives here rather than in the parser, which sees one manifest at
   a time and has no registry.

   An optional package the host cannot run is only marked inert, and the
   lockfile still records it, so a darwin-only binary such as fsevents
   stays in the answer on linux exactly as it stays in npm's lockfile.

   The repository read is repoPreimage at the target alone, memoized per
   name in repo_at, so the check reuses whatever the sub-instances built.

   It is applied where a dependency is read rather than where a packument is
   loaded, because deciding at load time would have to resolve every
   optional target of every version eagerly -- the cone pass the driver
   deliberately does not do.  Read lazily, the target of a dependency that
   survives is a slot target the sub-instance was going to load anyway.

   The range is evaluated by the calculus, via the extracted rgHolds and
   under the same flat override the calculus would apply; only the "*"
   rewrite's engines test (star_range) evaluates in OCaml. *)
let dep_keep st (d : P.dep) : bool =
  (not d.P.d_optional)
  || st.ar.optional
     &&
     let n = d.P.d_target in
     let own = star_range st.ar ~star:d.P.d_star n d.P.d_range in
     let key = (n, Npm_version.string_of_range own) in
     match Hashtbl.find_opt st.opt_keep key with
     | Some b -> b
     | None ->
         let rg =
           match List.assoc_opt n st.ovr with
           | Some rg -> rg
           | None -> xrange own
         in
         let b =
           Np.VSet.exists_ (Np.rgHolds rg)
             (Np.realVersions (repo_at st n) n)
         in
         if not b then st.ar.n_opt_dropped <- st.ar.n_opt_dropped + 1;
         Hashtbl.replace st.opt_keep key b;
         b

let dependencies st p =
  match Hashtbl.find_opt st.dep_tbl p with
  | Some l -> l
  | None ->
      let l =
        match meta st.ar p with
        | None -> []
        | Some v ->
            List.map (xdep st.ar) (List.filter (dep_keep st) v.P.v_deps)
      in
      Hashtbl.replace st.dep_tbl p l;
      l

(* dependenciesOf I p: what depActive keeps, i.e. dev dependencies only
   at the root *)
let active_dependencies st p =
  List.filter
    (fun (d : Np.coq_Dependency) -> (not d.Np.d_dev) || p = st.root)
    (dependencies st p)

let own_dependencies st p = List.map (fun d -> (p, d)) (dependencies st p)
let own_peer_dependencies st p =
  List.map (fun r -> (p, r)) (peer_dependencies st p)

(* slotTargets I p *)
let slot_targets st p =
  List.sort_uniq String.compare
    (List.map
       (fun (d : Np.coq_Dependency) -> d.Np.d_target)
       (active_dependencies st p))

(* peerNamesAt I q *)
let peer_names_at st q =
  List.sort_uniq String.compare
    (List.map
       (fun (r : Np.coq_PeerDependency) -> r.Np.p_name)
       (peer_dependencies st q))

(* peerDependenciesNamed I n *)
let peer_dependencies_named st (n : string) =
  List.map
    (fun (p, r) -> (p, xpeer st.ar r))
    (Hashtbl.find_all st.ar.peer_by_name n)

(* ---- the four sub-instances, one per lookup theorem ---- *)

(* versions_lookupGran: granSubInst I k cuts the repository to the key's
   registry name.  Two narrowings below are the driver's own.  keysOf is
   a union of one key per dependency and per peer dependency plus the
   root's, and the granular lookup asks it only whether it contains k, so
   one dependency introducing k answers it, or failing that one peer:
   google-closure-compiler's releases pin each platform binary at a range
   of their own, and testing every such dependency costs a pass over the
   binary's versions per range.  The filter is the one dependencies
   applies, so the two views of a package's dependencies cannot disagree
   about keysOf.  The lookup asks the repository only whether the
   looked-up version is published, so it is cut to that one package. *)
let gran_sub_inst st (k : string * string) (w : string) =
  let p = (snd k, w) in
  let repo =
    if List.mem w (versions_of st.ar (snd k)) then
      Np.RepoSet.add p Np.RepoSet.empty
    else Np.RepoSet.empty
  in
  let deps =
    Option.to_list
      (List.find_map
         (fun (q, d) -> if dep_keep st d then Some (q, xdep st.ar d) else None)
         (Hashtbl.find_all st.ar.dep_by_key k))
  in
  let peers =
    if deps = [] && fst k = snd k then
      Option.to_list
        (Option.map
           (fun (q, r) -> (q, xpeer st.ar r))
           (Hashtbl.find_opt st.ar.peer_by_name (fst k)))
    else []
  in
  mk_inst st ~repo ~deps ~peers

(* versions_lookupInt: intSubInst I p m is p's own dependencies, the peer
   dependencies naming the key's directory, and the repository at the
   key's registry name together with p's slot targets. *)
let int_sub_inst st (p : string * string) (m : string * string) =
  let ns = snd m :: slot_targets st p in
  mk_inst st ~repo:(repo_of st ns)
    ~deps:(own_dependencies st p)
    ~peers:(peer_dependencies_named st (fst m))

(* dependees_lookupGran: pkgSubInst I p is p's own dependencies, its own
   peer dependencies, and the repository at their targets.  The peer
   dependencies are there for the root, whose granular node carries the
   edges
   that install its own peers; for any other package rootPeerEdges tests
   the whole package and emits nothing, so they are inert. *)
let pkg_sub_inst st (p : string * string) =
  let ns = slot_targets st p @ peer_names_at st p in
  mk_inst st ~repo:(repo_of st ns)
    ~deps:(own_dependencies st p) ~peers:(own_peer_dependencies st p)

(* dependees_lookupInt: peerSubInst I p m u is p's own dependencies, the
   peer dependencies of the dependee that was selected, and the
   repository at p's slot targets and at the directories those peers
   name.  This is the second hop npm's peer auto-installation costs. *)
let peer_sub_inst st (p : string * string) (m : string * string) (u : string) =
  let q = (snd m, u) in
  let ns = slot_targets st p @ peer_names_at st q in
  mk_inst st ~repo:(repo_of st ns)
    ~deps:(own_dependencies st p) ~peers:(own_peer_dependencies st q)

(* ---- the lookups, answered by the extracted calculus ---- *)

let versions st (n : Np.Nm.name) : Np.Vs.version list =
  match Hashtbl.find_opt st.vcache n with
  | Some l -> l
  | None ->
      st.n_lookups <- st.n_lookups + 1;
      let l =
        match n with
        | Np.Nm.Granular (k, w) ->
            T.VSet.elements (R.versions (gran_sub_inst st k w) n)
        | Np.Nm.Intermediate (k, v, m) ->
            T.VSet.elements (R.versions (int_sub_inst st (snd k, v) m) n)
      in
      Hashtbl.replace st.vcache n l;
      l

let dependees st (s : T.Pkg.t) : T.Dependees.t list =
  st.n_lookups <- st.n_lookups + 1;
  let hs =
    match s with
    | Np.Nm.Granular (k, _), Np.Vs.Orig v ->
        R.dependees (pkg_sub_inst st (snd k, v)) s
    | Np.Nm.Intermediate (k, v, m), Np.Vs.Orig u ->
        R.dependees (peer_sub_inst st (snd k, v) m u) s
    | _ -> T.DependeesSet.empty
  in
  let hs = T.DependeesSet.elements hs in
  List.iter
    (fun ((m, _) : T.Dependees.t) ->
      match m with
      | Np.Nm.Intermediate (k, v, _) ->
          let l = Option.value ~default:[] (Hashtbl.find_opt st.dirs (k, v)) in
          if not (List.exists (fun x -> Np.Nm.compare x m = E.Eq) l) then
            Hashtbl.replace st.dirs (k, v) (m :: l)
      | Np.Nm.Granular _ -> ())
    hs;
  hs

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

(* npm-pick-manifest's sort keys above semver, lib/index.js:167-181:

     ((notdeprb && engineb) - (notdepra && enginea)) ||
     (engineb - enginea) ||
     (notdeprb - notdepra) ||
     semver.rcompare(vera, verb, sortSemverOpt)

   deprecated and engines are one preference because they are one sort
   function, and the middle key is what orders them against each other: a
   deprecated version the host can run outranks a current one it cannot.
   Neither drops a candidate, so neither can make anything unsatisfiable
   -- a package whose every version is deprecated resolves to its newest,
   and a pinned version the host cannot run still installs, which is what
   --engine-strict exists to refuse at install time.

   The three keys npm sorts above these have no counterpart here.  avoid
   is npm audit fix's, passed by nothing that writes an ordinary
   lockfile; policyRestrictions and stagedVersions appear in no public
   packument, and the parser reads neither, so restricted and staged are
   uniformly false.  A Gran version stands for a granularity class rather
   than a release, so it carries neither key. *)
let pick_keys st (n : string) (c : PVersion.t) : bool * bool * bool =
  match c with
  | Np.Vs.Gran _ -> (true, true, true)
  | Np.Vs.Orig v ->
      let p = (n, v) in
      let nd = not (deprecated st.ar p) and eng = engine_ok st.ar p in
      (nd && eng, eng, nd)

let best st (n : string) (cands : PVersion.t list) : PVersion.t =
  match cands with
  | [] -> invalid_arg "best"
  | c :: cs ->
      List.fold_left
        (fun a b ->
          let d = compare (pick_keys st n b) (pick_keys st n a) in
          if d > 0 || (d = 0 && PVersion.compare b a > 0) then b else a)
        c cs

(* npm-pick-manifest offers dist-tags.latest before the highest version
   the range admits, and takes it whenever the range admits it; only the
   ordering differs from ours, so a package published ahead of its own
   latest tag no longer drags its newest release in.  Preference only:
   the tag is consulted inside the candidates, never outside them.

   The fast path is guarded by the same two keys as the sort
   (index.js:119-132, [engineOk(mani, ..) && !mani.deprecated]), so a
   deprecated or unrunnable latest is not a shortcut past them.  It is
   not merely redundant with the sort: the tag may name a version the
   sort would rank below a newer one. *)
let tagged st (n : string) (cands : PVersion.t list) : PVersion.t option =
  match Hashtbl.find_opt st.ar.latest n with
  | None -> None
  | Some l ->
      if deprecated st.ar (n, l) || not (engine_ok st.ar (n, l)) then None
      else
        let l = Np.Vs.Orig l in
        List.find_opt (fun c -> PVersion.compare c l = 0) cands

(* A directory no dependency of p names: only a peer asks for it, so
   childCands offers every published version of the target and nothing
   narrows the slot but the peer ranges. *)
let peer_only st p (a : string) =
  not
    (List.exists
       (fun (d : Np.coq_Dependency) -> d.Np.d_dir = a)
       (active_dependencies st p))

(* what npm-pick-manifest returns from these candidates *)
let pick st (t : string) (cands : PVersion.t list) : PVersion.t =
  match tagged st t cands with Some c -> c | None -> best st t cands

(* npm's pick for a range over every published version, under the root's
   flat override as the calculus reads one *)
let pick_in st (t : string) (rg : Np.coq_Range) : string option =
  let rg = match List.assoc_opt t st.ovr with Some o -> o | None -> rg in
  match
    List.filter_map
      (fun u -> if Np.rgHolds rg u then Some (Np.Vs.Orig u) else None)
      (versions_of st.ar t)
  with
  | [] -> None
  | pool -> (
      match pick st t pool with Np.Vs.Orig u -> Some u | Np.Vs.Gran _ -> None)

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

(* The peer ranges npm resolves into p's peer-only directory a that the
   encoding sends to another directory, in the order npm meets them: on
   behalf of a package q that p holds and that peers on a, so that q's own
   peer is what fills the directory, the peers on a of q's dependencies,
   and of theirs while each peers on a too.  npm places a peer inside a
   package that peers on the same name only at the root (can-place-dep.js:
   "cannot place peers inside their dependents, except for tops"), so
   these land beside q's own peer; the
   encoding puts them in q's directory.  npm meets a package's edges by
   name in its collation (build-ideal-tree.js:997, 1428).

   A dependency not decided yet is taken at npm's pick for its range, as
   npm fetches it. *)
let peer_ranges_into st ~assigned (k : string * string) (v : string)
    (a : string) : Np.coq_Range list =
  let p = (snd k, v) in
  let decided n =
    match assigned n with PG.Decided (Np.Vs.Orig u) -> Some u | _ -> None
  in
  let deps q =
    List.sort
      (fun (x : Np.coq_Dependency) (y : Np.coq_Dependency) ->
        collate x.Np.d_dir y.Np.d_dir)
      (active_dependencies st q)
  in
  let peers_on q =
    List.filter_map
      (fun (r : Np.coq_PeerDependency) ->
        if r.Np.p_name = a then Some r.Np.p_range else None)
      (peer_dependencies st q)
  in
  let dirs = List.map (fun (d : Np.coq_Dependency) -> d.Np.d_dir) (deps p) in
  (* what p holds, by key: its dependencies, then the mandatory peers
     those install beside them *)
  let held = Hashtbl.create 16 in
  let rec hold key =
    if not (Hashtbl.mem held key) then (
      let u = decided (Np.Nm.Intermediate (k, v, key)) in
      Hashtbl.replace held key u;
      Option.iter
        (fun u ->
          List.iter
            (fun (r : Np.coq_PeerDependency) ->
              if (not r.Np.p_optional) && not (List.mem r.Np.p_name dirs) then
                hold (r.Np.p_name, r.Np.p_name))
            (peer_dependencies st (snd key, u)))
        u)
  in
  List.iter
    (fun (d : Np.coq_Dependency) -> hold (d.Np.d_dir, d.Np.d_target))
    (deps p);
  let seen = Hashtbl.create 16 in
  let rec below (key, u) =
    if Hashtbl.mem seen (key, u) then []
    else (
      Hashtbl.replace seen (key, u) ();
      List.concat_map
        (fun (d : Np.coq_Dependency) ->
          let okey = (d.Np.d_dir, d.Np.d_target) in
          let w =
            match decided (Np.Nm.Intermediate (key, u, okey)) with
            | Some w -> Some w
            | None -> pick_in st d.Np.d_target d.Np.d_range
          in
          match w with
          | None -> []
          | Some w -> (
              match peers_on (d.Np.d_target, w) with
              | [] -> []
              | rs -> rs @ below (okey, w)))
        (deps (snd key, u)))
  in
  Hashtbl.fold
    (fun key u acc ->
      match u with
      | Some u when peers_on (snd key, u) <> [] -> (key, u) :: acc
      | _ -> acc)
    held []
  |> List.sort (fun ((d, _), _) ((d', _), _) -> collate d d')
  |> List.concat_map below

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
  let step (into, c) rg =
    let rg = match List.assoc_opt t st.ovr with Some o -> o | None -> rg in
    let c =
      if holds rg c then c
      else
        match pick_in st t rg with
        | Some u ->
            let x = Np.Vs.Orig u in
            if
              List.exists (fun y -> PVersion.compare x y = 0) cands
              && List.for_all (fun r -> holds r x) into
            then x
            else c
        | None -> c
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

type order = {
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

let restart st o =
  let top =
    {
      id = 0;
      key = (fst st.root, fst st.root);
      ver = snd st.root;
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

let new_order st =
  let o =
    {
      queue = DepsQueue.empty;
      current = None;
      ids = 0;
      first = Hashtbl.create 1024;
      made = Hashtbl.create 1024;
      decided = [];
      pending = None;
    }
  in
  restart st o;
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
        Some
          ( d.Np.d_target,
            match List.assoc_opt d.Np.d_target st.ovr with
            | Some o -> o
            | None -> d.Np.d_range )
      else None)
    (active_dependencies st (snd x.key, x.ver))

let fits (t, rg) (m : string * string) (u : string) =
  snd m = t && Np.rgHolds rg u

(* PlaceDep: from the requirer up, the shallowest node_modules npm can put
   the copy in, stopping at the first that holds another version of the
   name (can-place-dep.js checkCanPlaceCurrent, CONFLICT, as npm neither
   replaces nor keeps there when the lookup below already failed).  A
   level is refused if its own package wants a version the copy is not,
   or if a package below it that already reaches a copy further up would
   no longer be satisfied (checkCanPlaceNoCurrent); a level whose package
   peers on the name is passed over.  Replacing an older copy, which npm
   does when every edge into it accepts the newer, is not modelled. *)
let place st o (x : copy) (m : string * string) (u : string) =
  let a = fst m in
  let breaks t (above : copy) =
    let rec walk (d : copy) =
      (not (Hashtbl.mem d.kids a))
      && ((match edge_at st d a with
            | Some e -> fits e above.key above.ver && not (fits e m u)
            | None -> false)
         || Hashtbl.fold (fun _ k acc -> acc || walk k) d.kids false)
    in
    walk t
  in
  let peers_on (t : copy) =
    List.exists
      (fun (r : Np.coq_PeerDependency) -> r.Np.p_name = a)
      (peer_dependencies st (snd t.key, t.ver))
  in
  let fine (t : copy) =
    t == x
    || (match edge_at st t a with Some e -> fits e m u | None -> true)
       &&
       match Option.bind t.up (fun p -> resolve p a) with
       | Some above -> not (breaks t above)
       | None -> true
  in
  let rec climb (t : copy) best =
    let onward b = match t.up with Some p -> climb p b | None -> b in
    if t.up <> None && peers_on t then onward best
    else if Hashtbl.mem t.kids a || not (fine t) then best
    else onward (Some t)
  in
  let at = match climb x None with Some t -> t | None -> x in
  let c =
    {
      id = o.ids;
      key = m;
      ver = u;
      up = Some at;
      depth = at.depth + 1;
      path = at.path ^ "/node_modules/" ^ a;
      kids = Hashtbl.create 8;
      seen = Hashtbl.create 8;
    }
  in
  o.ids <- o.ids + 1;
  Hashtbl.replace at.kids a c;
  if not (Hashtbl.mem o.first (m, u)) then Hashtbl.replace o.first (m, u) c;
  o.queue <- DepsQueue.add c o.queue

(* npm resolving x's edge on directory m, which the solver has decided at
   u: nothing happens if x's lookup already finds that copy *)
let settle st o (x : copy) (m : string * string) (u : string) =
  match resolve x (fst m) with
  | Some c when c.key = m && c.ver = u -> ()
  | _ -> place st o x m u

let dir_of (n : PName.t) =
  match n with
  | Np.Nm.Intermediate (_, _, m) -> fst m
  | Np.Nm.Granular (k, _) -> fst k

(* build-ideal-tree.js: #buildDepStep pops the copy that is shallowest in
   node_modules, then first by path (DepsQueue), and places what each of
   its problem edges fetches in the order of the edges' names; each copy
   placed joins the queue.  The replay runs that loop over the solver's
   decisions until it reaches a directory not yet decided, which is the
   one to decide next. *)
let rec advance st ~assigned o =
  match o.current with
  | None -> (
      match DepsQueue.min_elt_opt o.queue with
      | None -> None
      | Some x ->
          o.queue <- DepsQueue.remove x o.queue;
          o.current <- Some x;
          advance st ~assigned o)
  | Some x -> (
      let open_dirs =
        List.filter
          (fun n ->
            (not (Hashtbl.mem x.seen (dir_of n)))
            && match assigned n with PG.Unselected -> false | _ -> true)
          (Option.value ~default:[] (Hashtbl.find_opt st.dirs (x.key, x.ver)))
      in
      match List.sort (fun a b -> collate (dir_of a) (dir_of b)) open_dirs with
      | [] ->
          o.current <- None;
          advance st ~assigned o
      | n :: _ -> (
          match (n, assigned n) with
          | Np.Nm.Intermediate (_, _, m), PG.Decided (Np.Vs.Orig u) ->
              settle st o x m u;
              Hashtbl.replace x.seen (fst m) ();
              Hashtbl.replace o.made n (Np.Vs.Orig u);
              advance st ~assigned o
          | _, PG.Decided _ ->
              Hashtbl.replace x.seen (dir_of n) ();
              advance st ~assigned o
          | _ -> Some (n, x)))

(* The solver's `next`: a granular name first, since it has one version and
   only opens its package's directories, then the directory npm resolves
   next.  A backtrack that undid a decision the tree was built from starts
   the replay again from the root, over the decisions that stand. *)
let next st o ~assigned (open_names : (PName.t * int) list) : PName.t =
  let holds (n, v) =
    match assigned n with
    | PG.Decided w -> PVersion.compare v w = 0
    | _ -> false
  in
  let rec undo = function
    | d :: rest when not (holds d) ->
        if Hashtbl.mem o.made (fst d) then restart st o;
        undo rest
    | l -> l
  in
  o.decided <- undo o.decided;
  match
    List.find_opt
      (fun (n, _) -> match n with Np.Nm.Granular _ -> true | _ -> false)
      open_names
  with
  | Some (n, _) -> n
  | None -> (
      match advance st ~assigned o with
      | Some (n, x) ->
          o.pending <- Some (n, x);
          n
      | None -> fst (List.hd open_names))

(* npm leaves a slot on a version its tree already holds when the range
   admits it: an edge whose node_modules lookup finds a satisfying copy is
   valid, so #problemEdges fetches nothing for it.  So the copy the
   requirer's lookup finds in the replayed tree outranks both the dist-tag
   and the newest; resolving afresh is what brings in a second copy of a
   package npm's tree already holds.  A peer edge is no different: one the
   lookup already satisfies is skipped (build-ideal-tree.js:1427, 1438), and
   a copy out of the lookup's sight is not reused.  Preference only, as in
   deb_solve's alt_carried: the filter falls back to the whole candidate
   list, so nothing that was satisfiable stops being so. *)
let choose st o ~assigned (n : PName.t) (cands : PVersion.t list) : PVersion.t =
  match n with
  | Np.Nm.Granular _ -> greatest cands
  | Np.Nm.Intermediate (k, v, m) ->
      let peer = peer_only st (snd k, v) (fst m) in
      let at =
        match o.pending with
        | Some (n', x) when PName.compare n n' = 0 -> Some x
        | _ -> Hashtbl.find_opt o.first (k, v)
      in
      let reuse c =
        match (at, c) with
        | Some x, Np.Vs.Orig u -> (
            match resolve x (fst m) with
            | Some y -> y.key = m && y.ver = u
            | None -> false)
        | _ -> false
      in
      let reused =
        match List.filter reuse cands with [] -> cands | reused -> reused
      in
      let c = pick st (snd m) reused in
      let c = if peer then replace st ~assigned k v m cands c else c in
      o.decided <- (n, c) :: o.decided;
      c

(* A dependee's versions as runs of the name's own sorted versions rather
   than as one point per version.  The solver tests every version of a name
   against its range on each assignment and each decision, and a union of
   points costs a comparison per point, so a wide name under "*" -- 2364
   versions of @types/node -- made each test quadratic, and that was most
   of the solve time of a seven-node goal.  A run [lo, next) holds exactly
   the same versions of this name, and the solver considers no others.  A
   few points cost less than asking for the name's versions, which the
   solver may never need. *)
let runs (all : PVersion.t list Lazy.t) (vs : PVersion.t list) : PG.Ranges.t =
  if List.compare_length_with vs 32 <= 0 then PG.Ranges.of_list vs
  else begin
    let inside = Hashtbl.create (List.length vs) in
    List.iter (fun v -> Hashtbl.replace inside v ()) vs;
    let rec go acc lo = function
      | [] -> (
          match lo with
          | Some l -> PG.Ranges.union acc (PG.Ranges.higher_than l)
          | None -> acc)
      | v :: rest -> (
          if Hashtbl.mem inside v then
            go acc (match lo with None -> Some v | l -> l) rest
          else
            match lo with
            | Some l ->
                go (PG.Ranges.union acc (PG.Ranges.between l v)) None rest
            | None -> go acc None rest)
    in
    go PG.Ranges.empty None (Lazy.force all)
  end

type result = {
  installs : ((string * string) * string) list;
  tree : (((string * string) * string) * ((string * string) * string)) list;
  nodes : int;
  lookups : int;
}

let solve ?(debug = false) ar (root : string * string) =
  Pubgrub.set_debug debug;
  let st = mk_state ar root in
  let order = new_order st in
  let root_key = (fst root, fst root) in
  let root_n = Np.Nm.Granular (root_key, snd root) in
  let versions n = versions st n in
  (* PubGrub widens each dependency's depender range by asking for the
     dependencies of the depender's neighbouring versions, once per
     dependency, so the same node is asked for over and over *)
  let cache = Hashtbl.create 65536 in
  let dependencies n (u : Np.Vs.version) =
    match Hashtbl.find_opt cache (n, u) with
    | Some r -> r
    | None ->
        let r =
          List.map
            (fun ((m, vs) : T.Dependees.t) ->
              (m, runs (lazy (versions m)) (T.VSet.elements vs)))
            (dependees st (n, u))
        in
        Hashtbl.replace cache (n, u) r;
        r
  in
  match
    PG.solve ~next:(next st order) ~choose:(choose st order) ~vers:versions
      ~deps:dependencies
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
