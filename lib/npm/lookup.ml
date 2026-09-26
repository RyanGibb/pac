open Encoding
module P = Npm_parse
module A = Archive
module Tbl = Pac_common.Tbl

(* This is what npm does for the literal range "*", and for an empty one,
   which it reads as "*": npm-pick-manifest's special case (lib/index.js,
   range === '*') takes dist-tags.latest even when that is a prerelease,
   provided it is neither deprecated nor refused by the host's engines,
   where semver itself admits no prerelease under "*".  Our ranges admit a
   prerelease only beside a comparator naming one at its release core, so
   such a range is read as "* || =latest", which admits that one prerelease
   and no other.  The target's packument decides it, so the rewrite is made
   here rather than in the parser, which sees one manifest at a time. *)
let star_range ar (t : string) (rg : Npm_version.range) : Npm_version.range =
  match A.latest ar t with
  | Some l
    when Npm_version.is_prerelease l
         && Hashtbl.mem ar.A.entry (t, l)
         && (not (A.deprecated ar (t, l)))
         && A.engine_ok ar (t, l) ->
      rg @ [ [ Npm_version.Cmp (Npm_version.Eq, l) ] ]
  | _ -> rg

(* npm-pick-manifest takes a dist-tag's version exactly, and a tag the
   packument lacks matches nothing (ETARGET) *)
let spec_range ar (t : string) : P.spec -> Npm_version.range = function
  | P.Tag g -> (
      match A.dist_tag ar t g with
      | Some v -> [ [ Npm_version.Cmp (Npm_version.Eq, v) ] ]
      | None -> [ [ Npm_version.Cmp (Npm_version.Lt, "0.0.0") ] ])
  | P.Star -> star_range ar t [ [ Npm_version.Any ] ]
  | P.Range rg -> rg

let own_range ar (d : P.dep) = spec_range ar d.P.d_target d.P.d_spec

let xdep ar (d : P.dep) : Np.coq_Dependency =
  {
    Np.d_dir = d.P.d_dir;
    Np.d_target = d.P.d_target;
    Np.d_range = xrange (own_range ar d);
    Np.d_dev = d.P.d_dev;
  }

(* a peer names a directory, and npm fetches the peer's range from the
   packument of that name *)
let xpeer ar (r : P.peer) : Np.coq_PeerDependency =
  {
    Np.p_name = r.P.p_name;
    Np.p_range = xrange (spec_range ar r.P.p_name r.P.p_spec);
    (* binds only a copy the declarer's depender holds itself, npm's legacy
       rule; arborist checks whatever copy the declarer resolves to
       (edge.js:266-277) *)
    Np.p_optional = r.P.p_optional;
  }

type t = {
  ar : A.t;
  root : string * string;
  (* false under --omit=optional: an optional dependency is then dropped
     outright rather than only when the registry cannot satisfy it *)
  optional : bool;
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

let create ~optional ar root =
  let ovr =
    match A.meta ar root with
    | Some v -> List.map (fun (n, rg) -> (n, xrange rg)) v.P.v_ovr
    | None -> []
  in
  {
    ar;
    root;
    optional;
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

(* the range the calculus reads for a dependency on t: the root's flat
   override when there is one *)
let effective st (t : string) (rg : Np.coq_Range) : Np.coq_Range =
  Option.value (List.assoc_opt t st.ovr) ~default:rg

let peer_dependencies st p =
  Tbl.memo st.peer_tbl p (fun () ->
      match A.meta st.ar p with
      | None -> []
      | Some v -> List.map (xpeer st.ar) v.P.v_peers)

let repo_at st (n : string) : Np.RepoSet.t =
  Tbl.memo st.repo_at n (fun () ->
      Np.RepoSet.ofList (List.map (fun v -> (n, v)) (A.versions_of st.ar n)))

let repo_of st (ns : string list) : Np.RepoSet.t =
  let ns = List.sort_uniq String.compare ns in
  Tbl.memo st.repo_of ns (fun () -> Np.RepoSet.unions (List.map (repo_at st) ns))

let mk_inst st ~repo ~deps ~peers : Np.coq_Inst =
  {
    Np.inst_repo = repo;
    Np.inst_dep = deps;
    Np.inst_peer = peers;
    Np.inst_ovr = st.ovr;
    Np.inst_root = st.root;
  }

(* Whether some published version of the target matches the range, as the
   calculus reads the range: via the extracted rgHolds and under the same
   flat override.  Only the "*" rewrite's engines test (star_range)
   evaluates in OCaml.  The repository read is the target's alone,
   memoized per name in repo_at, so the check reuses whatever the
   sub-instances built. *)
let matches_published st (d : P.dep) : bool =
  let n = d.P.d_target and own = own_range st.ar d in
  Tbl.memo st.opt_keep
    (n, Npm_version.string_of_range own)
    (fun () ->
      Np.VSet.exists_
        (Np.rgHolds (effective st n (xrange own)))
        (Np.realVersions (repo_at st n) n))

(* An optional entry is an ordinary dependency that this driver abandons
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

   It is applied where a dependency is read rather than where a packument
   is loaded, because deciding at load time would have to resolve every
   optional target of every version eagerly -- the cone pass the driver
   deliberately does not do.  Read lazily, the target of a dependency that
   survives is a slot target the sub-instance was going to load anyway. *)
let dep_keep st (d : P.dep) : bool =
  (not d.P.d_optional) || (st.optional && matches_published st d)

(* what the optional-dependency test read and what it abandoned, both in
   distinct (target, range) pairs *)
let optional_verdicts st =
  let dropped =
    Hashtbl.fold (fun _ b n -> if b then n else n + 1) st.opt_keep 0
  in
  (Hashtbl.length st.opt_keep, dropped)

let dependencies st p =
  Tbl.memo st.dep_tbl p (fun () ->
      match A.meta st.ar p with
      | None -> []
      | Some v -> List.map (xdep st.ar) (List.filter (dep_keep st) v.P.v_deps))

let active_dependencies st p =
  List.filter
    (fun (d : Np.coq_Dependency) -> (not d.Np.d_dev) || p = st.root)
    (dependencies st p)

let own_dependencies st p = List.map (fun d -> (p, d)) (dependencies st p)

let own_peer_dependencies st p =
  List.map (fun r -> (p, r)) (peer_dependencies st p)

let slot_targets st p =
  List.sort_uniq String.compare
    (List.map
       (fun (d : Np.coq_Dependency) -> d.Np.d_target)
       (active_dependencies st p))

let peer_names_at st q =
  List.sort_uniq String.compare
    (List.map
       (fun (r : Np.coq_PeerDependency) -> r.Np.p_name)
       (peer_dependencies st q))

let peer_dependencies_named st (n : string) =
  List.map
    (fun (p, r) -> (p, xpeer st.ar r))
    (Hashtbl.find_all st.ar.A.peer_by_name n)

(* The granular versions lookup's sub-instance, which the calculus cuts
   to the key's registry name, narrowed twice more here.  The instance's
   keys are a union of one per dependency and per peer dependency plus the
   root's, and the granular lookup asks only whether they contain k, so
   one dependency introducing k answers it, or failing that one peer:
   google-closure-compiler's releases pin each platform binary at a range
   of their own, and testing every such dependency costs a pass over the
   binary's versions per range.  The filter is the one dependencies
   applies, so the two views of a package's dependencies cannot disagree
   about the keys.  The lookup asks the repository only whether the
   looked-up version is published, so it is cut to that one package. *)
let gran_sub_inst st (k : string * string) (w : string) =
  let repo =
    if List.mem w (A.versions_of st.ar (snd k)) then
      Np.RepoSet.add (snd k, w) Np.RepoSet.empty
    else Np.RepoSet.empty
  in
  let deps =
    Option.to_list
      (List.find_map
         (fun (q, d) -> if dep_keep st d then Some (q, xdep st.ar d) else None)
         (Hashtbl.find_all st.ar.A.dep_by_key k))
  in
  let peers =
    if deps = [] && fst k = snd k then
      Option.to_list
        (Option.map
           (fun (q, r) -> (q, xpeer st.ar r))
           (Hashtbl.find_opt st.ar.A.peer_by_name (fst k)))
    else []
  in
  mk_inst st ~repo ~deps ~peers

(* the intermediate versions lookup's sub-instance: p's own dependencies,
   the peer dependencies naming the key's directory, and the repository at
   the key's registry name together with p's slot targets. *)
let int_sub_inst st (p : string * string) (m : string * string) =
  let ns = snd m :: slot_targets st p in
  mk_inst st ~repo:(repo_of st ns) ~deps:(own_dependencies st p)
    ~peers:(peer_dependencies_named st (fst m))

(* the granular dependees lookup's sub-instance: p's own dependencies, its
   own peer dependencies, and the repository at their targets.  The peer
   dependencies are there for the root, whose granular node carries the
   edges that install its own peers; for any other package they emit no
   edge, so they are inert. *)
let pkg_sub_inst st (p : string * string) =
  let ns = slot_targets st p @ peer_names_at st p in
  mk_inst st ~repo:(repo_of st ns) ~deps:(own_dependencies st p)
    ~peers:(own_peer_dependencies st p)

(* the intermediate dependees lookup's sub-instance: p's own dependencies,
   the peer dependencies of the dependee that was selected, and the
   repository at p's slot targets and at the directories those peers
   name.  This is the second hop npm's peer auto-installation costs. *)
let peer_sub_inst st (p : string * string) (m : string * string) (u : string) =
  let q = (snd m, u) in
  let ns = slot_targets st p @ peer_names_at st q in
  mk_inst st ~repo:(repo_of st ns) ~deps:(own_dependencies st p)
    ~peers:(own_peer_dependencies st q)

let versions st (n : Np.Nm.name) : Np.Vs.version list =
  Tbl.memo st.vcache n (fun () ->
      match n with
      | Np.Nm.Granular (k, w) ->
          T.VSet.elements (R.versions (gran_sub_inst st k w) n)
      | Np.Nm.Intermediate (k, v, m) ->
          T.VSet.elements (R.versions (int_sub_inst st (snd k, v) m) n))

let record_dir st (m : Np.Nm.name) =
  match m with
  | Np.Nm.Intermediate (k, v, _) ->
      let l = Option.value ~default:[] (Hashtbl.find_opt st.dirs (k, v)) in
      if not (List.exists (fun x -> Np.Nm.compare x m = E.Eq) l) then
        Hashtbl.replace st.dirs (k, v) (m :: l)
  | Np.Nm.Granular _ -> ()

let dependees st (s : T.Pkg.t) : T.Dependees.t list =
  let hs =
    match s with
    | Np.Nm.Granular (k, _), Np.Vs.Orig v ->
        R.dependees (pkg_sub_inst st (snd k, v)) s
    | Np.Nm.Intermediate (k, v, m), Np.Vs.Orig u ->
        R.dependees (peer_sub_inst st (snd k, v) m u) s
    | _ -> T.DependeesSet.empty
  in
  let hs = T.DependeesSet.elements hs in
  List.iter (fun ((m, _) : T.Dependees.t) -> record_dir st m) hs;
  hs

(* the directories of p's copy the solver has opened so far *)
let dirs st p = Option.value ~default:[] (Hashtbl.find_opt st.dirs p)
