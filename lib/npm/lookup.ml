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
   and no other.  The dependee name's packument decides it, so the rewrite
   is made
   here rather than in the parser, which sees one manifest at a time. *)
let star_range ar (t : string) (rg : Npm_version.range) : Npm_version.range =
  (* Berry reads * as semver does, so the shared reading admits no
     prerelease under it *)
  if A.shared ar then rg
  else
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

let own_range ar (d : P.dep) = spec_range ar d.P.d_name d.P.d_spec

(* The descriptor is the spec as written under the shared reading, where every
   dependency with it resolves to one version as in Yarn Berry's lockfile;
   npm resolves each dependency apart, so otherwise there is none. *)
let xdep ar (d : P.dep) : Np.coq_Dependency =
  {
    Np.d_dir = d.P.d_dir;
    Np.d_name = d.P.d_name;
    Np.d_range = xrange (own_range ar d);
    Np.d_dev = d.P.d_dev;
    Np.d_desc = (if A.shared ar then Some d.P.d_raw else None);
  }

(* a peer names a directory, and npm fetches the peer's range from the
   packument of that name *)
let xpeer ar (r : P.peer) : Np.coq_PeerDependency =
  {
    Np.p_name = r.P.p_name;
    Np.p_range = xrange (spec_range ar r.P.p_name r.P.p_spec);
    (* need not be met, but what the declarer's depender shows it, its
       sight, its copy or itself, must be in range, as arborist checks
       whatever copy the declarer resolves to (edge.js:266-277) *)
    Np.p_optional = r.P.p_optional;
    Np.p_root = r.P.p_root;
  }

type t = {
  ar : A.t;
  root : string * string;
  optional : bool;
  ovr : (string * Np.coq_Range) list;
  dep_tbl : (string * string, Np.coq_Dependency list) Hashtbl.t;
  peer_tbl : (string * string, Np.coq_PeerDependency list) Hashtbl.t;
  repo_at : (string, Np.RepoSet.t) Hashtbl.t;
  repo_of : (string list, Np.RepoSet.t) Hashtbl.t;
  vcache : (Np.Nm.name, Np.Vs.version list) Hashtbl.t;
  opt_keep : (string * string, bool) Hashtbl.t;
  dirs : ((string * string) * string, Np.Nm.name list) Hashtbl.t;
  links_into : (Np.Nm.name, Np.Nm.name) Hashtbl.t;
  raw_tbl : (string * string, P.dep list) Hashtbl.t;
  desc_dirs : (Np.Nm.name, Np.Nm.name) Hashtbl.t;
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
    links_into = Hashtbl.create 4096;
    raw_tbl = Hashtbl.create 16384;
    desc_dirs = Hashtbl.create 4096;
    n_lookups = 0;
  }

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
  Tbl.memo st.repo_of ns (fun () ->
      Np.RepoSet.unions (List.map (repo_at st) ns))

let mk_inst st ~repo ~deps ~peers : Np.coq_Inst =
  {
    Np.inst_repo = repo;
    Np.inst_deps = deps;
    Np.inst_peers = peers;
    Np.inst_ovr = st.ovr;
    Np.inst_root = st.root;
  }

(* Whether some published version of the dependee name matches the range,
   as the
   calculus reads the range: via the extracted rgHolds and under the same
   flat override.  Only the "*" rewrite's engines test (star_range)
   evaluates in OCaml.  The repository read is the dependee name's alone,
   memoized per name in repo_at, so the check reuses whatever the
   sub-instances built. *)
let matches_published st (d : P.dep) : bool =
  let n = d.P.d_name and own = own_range st.ar d in
  Tbl.memo st.opt_keep
    (n, Npm_version.string_of_range own)
    (fun () ->
      Np.VSet.exists_
        (Np.rgHolds (effective st n (xrange own)))
        (Np.realVersions (repo_at st n) n))

(* An optional entry is an ordinary dependency that this driver abandons
   in one situation only: no published version of the dependee name matches
   the
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
   optional dependee name of every version eagerly -- the cone pass the
   driver deliberately does not do.  Read lazily, the dependee name of a
   dependency that survives is a slot name the sub-instance was going to
   load anyway.

   Under the shared reading an optional dependency is kept whatever the
   registry holds, as Yarn Berry fails to resolve one no version matches
   (YN0082). *)
let dep_keep st (d : P.dep) : bool =
  (not d.P.d_optional)
  || (st.optional && (A.shared st.ar || matches_published st d))

let optional_verdicts st =
  let dropped =
    Hashtbl.fold (fun _ b n -> if b then n else n + 1) st.opt_keep 0
  in
  (Hashtbl.length st.opt_keep, dropped)

(* p's dependencies as the manifest writes them, those the calculus reads *)
let raw_deps st p =
  Tbl.memo st.raw_tbl p (fun () ->
      match A.meta st.ar p with
      | None -> []
      | Some v -> List.filter (dep_keep st) v.P.v_deps)

let dependencies st p =
  Tbl.memo st.dep_tbl p (fun () -> List.map (xdep st.ar) (raw_deps st p))

let active_dependencies st p =
  List.filter
    (fun (d : Np.coq_Dependency) -> (not d.Np.d_dev) || p = st.root)
    (dependencies st p)

let own_dependencies st p = List.map (fun d -> (p, d)) (dependencies st p)

let desc_name st p (m : string * string) : Np.Nm.name option =
  match
    List.find_opt
      (fun (d : Np.coq_Dependency) -> d.Np.d_dir = fst m)
      (active_dependencies st p)
  with
  | Some { Np.d_name; Np.d_desc = Some s; _ } when d_name = snd m ->
      Some (Np.Nm.Desc (fst m, d_name, s))
  | _ -> None

let own_peer_dependencies st p =
  List.map (fun r -> (p, r)) (peer_dependencies st p)

let slot_names st p =
  List.sort_uniq String.compare
    (List.map
       (fun (d : Np.coq_Dependency) -> d.Np.d_name)
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
   the peer dependencies naming the key's directory (p's own among them,
   which empty the directory when p peers on it), and the repository at
   the key's registry name together with p's slot names. *)
let int_sub_inst st (p : string * string) (m : string * string) =
  let ns = snd m :: slot_names st p in
  mk_inst st ~repo:(repo_of st ns) ~deps:(own_dependencies st p)
    ~peers:(peer_dependencies_named st (fst m))

(* the granular dependees lookup's sub-instance: p's own dependencies, its
   own peer dependencies, and the repository at their dependee names.  The
   peer
   dependencies are there for the root, whose granular node carries the
   edges that install its own peers; for any other package they emit no
   edge, so they are inert. *)
let pkg_sub_inst st (p : string * string) =
  let ns = slot_names st p @ peer_names_at st p in
  mk_inst st ~repo:(repo_of st ns) ~deps:(own_dependencies st p)
    ~peers:(own_peer_dependencies st p)

(* the peer dependencies of a holder p, which decide where it offers a
   name, and of its dependee q, which ask for one *)
let two_peers st p q =
  own_peer_dependencies st p @ if q = p then [] else own_peer_dependencies st q

(* A copy's own dependencies and slot names, which only a peer with
   default reads: the copy's sight admits its own copy, and a link to it
   decides whether it holds one.  A peer with default is a peer beside a
   dependency of its name, which only the shared reading keeps, the parser
   otherwise dropping the peer (npm's _loadDeps), so outside it they are
   left out: no lookup reads them, and reading them would load packuments
   npm does not. *)
let dp_deps st q = if A.shared st.ar then own_dependencies st q else []
let dp_names st q = if A.shared st.ar then slot_names st q else []

(* the dependencies of a holder p and of its dependee q, whose peer with
   default reads its own *)
let two_deps st p q = own_dependencies st p @ if q = p then [] else dp_deps st q

(* the intermediate dependees lookup's sub-instance: p's own dependencies
   and peer dependencies and those of the dependee that was selected, and
   the repository at both slot names and at the directories the
   dependee's peers name *)
let peer_sub_inst st (p : string * string) (m : string * string) (u : string) =
  let q = (snd m, u) in
  let ns = slot_names st p @ peer_names_at st q @ dp_names st q in
  mk_inst st ~repo:(repo_of st ns) ~deps:(two_deps st p q)
    ~peers:(two_peers st p q)

(* the sight lookup's sub-instance: the copy's own peer dependencies and
   dependencies, whose ranges bound the sight, and the repository at the
   name and at its slot names *)
let sight_sub_inst st (c : string * string) (a : string) =
  mk_inst st
    ~repo:(repo_of st (a :: dp_names st c))
    ~deps:(dp_deps st c)
    ~peers:(own_peer_dependencies st c)

(* the link versions lookup's sub-instance: the holder's and the dependee's
   dependencies and peer dependencies, and the repository at the peer's
   name and both slot names *)
let link_sub_inst st (p : string * string) (q : string * string) (a : string) =
  mk_inst st
    ~repo:(repo_of st ((a :: slot_names st p) @ dp_names st q))
    ~deps:(two_deps st p q) ~peers:(two_peers st p q)

(* the link dependees lookup's sub-instance: the holder's and the
   dependee's dependencies and peer dependencies, which decide where the
   holder shows the name and whether the dependee holds its own, and the
   repository at the dependee's slot names *)
let holder_sub_inst st (p : string * string) (q : string * string) =
  mk_inst st
    ~repo:(repo_of st (dp_names st q))
    ~deps:(two_deps st p q) ~peers:(two_peers st p q)

(* the descriptor lookup's sub-instance: the repository at its dependee
   name *)
let desc_sub_inst st (t : string) =
  mk_inst st ~repo:(repo_at st t) ~deps:[] ~peers:[]

let versions st (n : Np.Nm.name) : Np.Vs.version list =
  Tbl.memo st.vcache n (fun () ->
      match n with
      | Np.Nm.Granular (k, w) ->
          T.VSet.elements (R.versions (gran_sub_inst st k w) n)
      | Np.Nm.Intermediate (k, v, m) ->
          T.VSet.elements (R.versions (int_sub_inst st (snd k, v) m) n)
      | Np.Nm.Sight (k, v, a) ->
          T.VSet.elements (R.versions (sight_sub_inst st (snd k, v) a) n)
      | Np.Nm.Link (k, v, m, u, a) ->
          T.VSet.elements
            (R.versions (link_sub_inst st (snd k, v) (snd m, u) a) n)
      | Np.Nm.Desc (_, t, _) ->
          T.VSet.elements (R.versions (desc_sub_inst st t) n))

let holder st ((k, v) : (string * string) * string) (a : string) :
    Np.Nm.name option =
  let p = (snd k, v) in
  R.holderName (holder_sub_inst st p p) (k, v) a

let record_dir st (m : Np.Nm.name) =
  match m with
  | Np.Nm.Intermediate (k, v, d) ->
      let l = Option.value ~default:[] (Hashtbl.find_opt st.dirs (k, v)) in
      if not (List.exists (fun x -> Np.Nm.compare x m = E.Eq) l) then begin
        Hashtbl.replace st.dirs (k, v) (m :: l);
        match desc_name st (snd k, v) d with
        | Some x -> Hashtbl.add st.desc_dirs x m
        | None -> ()
      end
  | _ -> ()

let desc_dirs st (x : Np.Nm.name) = Hashtbl.find_all st.desc_dirs x

let record_link st (l : Np.Nm.name) =
  match l with
  | Np.Nm.Link (k, v, _, _, a) -> (
      match holder st (k, v) a with
      | None -> ()
      | Some h ->
          record_dir st h;
          if
            not
              (List.exists
                 (fun x -> Np.Nm.compare x l = E.Eq)
                 (Hashtbl.find_all st.links_into h))
          then Hashtbl.add st.links_into h l)
  | _ -> ()

let dependees st (s : T.Pkg.t) : T.Dependees.t list =
  let hs =
    match s with
    | Np.Nm.Granular (k, _), Np.Vs.Orig v ->
        R.dependees (pkg_sub_inst st (snd k, v)) s
    | Np.Nm.Intermediate (k, v, m), Np.Vs.Orig u ->
        R.dependees (peer_sub_inst st (snd k, v) m u) s
    | Np.Nm.Link (k, v, m, u, _), _ ->
        R.dependees (holder_sub_inst st (snd k, v) (snd m, u)) s
    | _ -> T.DependeesSet.empty
  in
  let hs = T.DependeesSet.elements hs in
  List.iter
    (fun ((m, _) : T.Dependees.t) ->
      record_dir st m;
      record_link st m)
    hs;
  hs

let links_into st (h : Np.Nm.name) = Hashtbl.find_all st.links_into h
let dirs st p = Option.value ~default:[] (Hashtbl.find_opt st.dirs p)
