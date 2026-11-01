module Tbl = Pac_common.Tbl

(* npm-pick-manifest takes dist-tags.latest for the range "*" (or an empty
   one) even when it is a prerelease, if it is neither deprecated nor
   refused by the host's engines (lib/index.js, range === '*'), where
   semver admits no prerelease under "*"; so such a range is read as
   "* || =latest".  The dependee name's packument decides it, so it is made
   here rather than in the parser, which sees one manifest at a time. *)
let star_range ar (t : string) (rg : Npm_version.range) : Npm_version.range =
  (* Berry reads * as semver does, so the shared reading admits no
     prerelease under it *)
  if Archive.shared ar then rg
  else
    match Archive.latest ar t with
    | Some l
      when Npm_version.is_prerelease l
           && Option.is_some (Archive.meta ar (t, l))
           && (not (Archive.deprecated ar (t, l)))
           && Archive.engine_ok ar (t, l) ->
        rg @ [ [ Npm_version.Cmp (Npm_version.Eq, l) ] ]
    | _ -> rg

(* npm-pick-manifest takes a dist-tag's version exactly, and a tag the
   packument lacks matches nothing (ETARGET) *)
let spec_range ar (t : string) : Npm_parse.spec -> Npm_version.range = function
  | Npm_parse.Tag g -> (
      match Archive.dist_tag ar t g with
      | Some v -> [ [ Npm_version.Cmp (Npm_version.Eq, v) ] ]
      | None -> [ [ Npm_version.Cmp (Npm_version.Lt, "0.0.0") ] ])
  | Npm_parse.Star -> star_range ar t [ [ Npm_version.Any ] ]
  | Npm_parse.Range rg -> rg

let own_range ar (d : Npm_parse.dep) =
  spec_range ar d.Npm_parse.d_name d.Npm_parse.d_spec

module Make (Encoding : Encoding.S) = struct
  open Encoding

  (* The descriptor is the spec as written under the shared reading, where every
     dependency with it resolves to one version as in Yarn Berry's lockfile;
     npm resolves each dependency apart, so otherwise there is none. *)
  let xdep ar (d : Npm_parse.dep) : Npm.coq_Dependency =
    {
      Npm.d_dir = d.Npm_parse.d_dir;
      Npm.d_name = d.Npm_parse.d_name;
      Npm.d_range = xrange (own_range ar d);
      Npm.d_dev = d.Npm_parse.d_dev;
      Npm.d_desc = (if Archive.shared ar then Some d.Npm_parse.d_raw else None);
    }

  (* a peer names a directory, and npm fetches the peer's range from the
     packument of that name *)
  let xpeer ar (r : Npm_parse.peer) : Npm.coq_PeerDependency =
    {
      Npm.p_name = r.Npm_parse.p_name;
      Npm.p_range = xrange (spec_range ar r.Npm_parse.p_name r.Npm_parse.p_spec);
      (* need not be met, but what the declarer's depender shows it, its
         sight, its copy or itself, must be in range, as arborist checks
         whatever copy the declarer resolves to (edge.js:266-277) *)
      Npm.p_optional = r.Npm_parse.p_optional;
      Npm.p_root = r.Npm_parse.p_root;
    }

  type t = {
    ar : Archive.t;
    root : string * string;
    ovr_raw : (string * Npm_version.range) list;
    ovr : (string * Npm.coq_Range) list;
    dep_tbl : (string * string, Npm.coq_Dependency list) Hashtbl.t;
    peer_tbl : (string * string, Npm.coq_PeerDependency list) Hashtbl.t;
    repo_at : (string, Npm.RealPackageSet.t) Hashtbl.t;
    (* keyed by the names read rather than by the package reading them, so
       packages that read the same names share one set *)
    repo_of : (string list, Npm.RealPackageSet.t) Hashtbl.t;
    vcache : (Npm.Name.name, Npm.Version.version list) Hashtbl.t;
    (* the optional-dependency verdict, keyed by what decides it *)
    opt_keep : (string * string, bool) Hashtbl.t;
    (* each package's directories, as far as the solver has looked: the
       intermediates its granular node and its directories point to, and the
       directory each of its links resolves into *)
    dirs : ((string * string) * string, Npm.Name.name list) Hashtbl.t;
    (* the links resolving into each directory *)
    links_into : (Npm.Name.name, Npm.Name.name) Hashtbl.t;
    raw_tbl : (string * string, Npm_parse.dep list) Hashtbl.t;
    (* the directories reading each descriptor, as far as the solver has
       looked *)
    desc_dirs : (Npm.Name.name, Npm.Name.name) Hashtbl.t;
  }

  let create ar root =
    let ovr_raw =
      match Archive.meta ar root with Some v -> v.Npm_parse.v_ovr | None -> []
    in
    {
      ar;
      root;
      ovr_raw;
      ovr = List.map (fun (n, rg) -> (n, xrange rg)) ovr_raw;
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
    }

  let archive st = st.ar
  let root st = st.root

  let effective st (a : string) (rg : Npm.coq_Range) : Npm.coq_Range =
    Option.value (List.assoc_opt a st.ovr) ~default:rg

  let peer_dependencies st p =
    Tbl.memo st.peer_tbl p (fun () ->
        match Archive.meta st.ar p with
        | None -> []
        | Some v -> List.map (xpeer st.ar) v.Npm_parse.v_peers)

  (* The calculus keys the root's package by its name and version as it
     keys a registry package, so the registry's packages of the root's name
     are out of reach, and a sub-instance reading them is refused. *)
  let repo_at st (n : string) : Npm.RealPackageSet.t =
    if n = fst st.root then raise (Archive.Reaches_root n);
    Tbl.memo st.repo_at n (fun () ->
        Npm.RealPackageSet.ofList
          (List.map (fun v -> (n, v)) (Archive.versions_of st.ar n)))

  let repo_of st (ns : string list) : Npm.RealPackageSet.t =
    let ns = List.sort_uniq String.compare ns in
    Tbl.memo st.repo_of ns (fun () ->
        Npm.RealPackageSet.unions (List.map (repo_at st) ns))

  let mk_inst st ~repo ~deps ~peers : Npm.coq_Inst =
    {
      Npm.inst_real = repo;
      Npm.inst_deps = deps;
      Npm.inst_peers = peers;
      Npm.inst_ovr = st.ovr;
      Npm.inst_root = st.root;
    }

  (* the dependency the calculus reads, the root's flat override on its
     directory applied *)
  let effective_dep st (d : Npm.coq_Dependency) : Npm.coq_Dependency =
    Npm.ovrDep (mk_inst st ~repo:Npm.RealPackageSet.empty ~deps:[] ~peers:[]) d

  (* effective_dep's dependee name, read off the manifest's entry, whose
     range is not yet read *)
  let effective_name st (d : Npm_parse.dep) =
    if List.mem_assoc d.Npm_parse.d_dir st.ovr_raw then d.Npm_parse.d_dir
    else d.Npm_parse.d_name

  (* Whether some published version of the dependee name matches the range,
     as the calculus reads both: via the extracted rgHolds, and under the
     override on the dependency's directory, as effective_dep reads it.  Only
     the "*" rewrite's engines test (star_range) evaluates in OCaml.  The
     repository read is the dependee name's alone, memoized per name in
     repo_at, so the check reuses whatever the sub-instances built. *)
  let matches_published st (d : Npm_parse.dep) : bool =
    let n = effective_name st d in
    let rg =
      match List.assoc_opt d.Npm_parse.d_dir st.ovr_raw with
      | Some rg -> rg
      | None -> own_range st.ar d
    in
    Tbl.memo st.opt_keep
      (n, Npm_version.string_of_range rg)
      (fun () ->
        Npm.VSet.exists_
          (Npm.rgHolds (xrange rg))
          (Npm.realVersions (repo_at st n) n))

  (* An optional dependency is abandoned only when no published version of
     its dependee name matches the range (ENOTARGET); npm's other grounds
     (#pruneFailedOptional, #checkEngineAndPlatform) are not modelled.  An
     optional package the host cannot run stays in the answer, as npm only
     marks it inert and still locks it (fsevents on linux).  It is
     tested where a dependency is read, since testing at load time would
     resolve every optional dependee name eagerly.  The shared reading keeps
     it, as Yarn Berry fails on one no version matches (YN0082). *)
  let dep_keep st (d : Npm_parse.dep) : bool =
    (not d.Npm_parse.d_optional)
    || Archive.shared st.ar || matches_published st d

  let optional_verdicts st =
    let dropped =
      Hashtbl.fold (fun _ b n -> if b then n else n + 1) st.opt_keep 0
    in
    (Hashtbl.length st.opt_keep, dropped)

  (* p's dependencies as the manifest writes them, those the calculus reads *)
  let raw_deps st p =
    Tbl.memo st.raw_tbl p (fun () ->
        match Archive.meta st.ar p with
        | None -> []
        | Some v -> List.filter (dep_keep st) v.Npm_parse.v_deps)

  let dependencies st p =
    Tbl.memo st.dep_tbl p (fun () -> List.map (xdep st.ar) (raw_deps st p))

  let active_dependencies st p =
    List.filter_map
      (fun (d : Npm.coq_Dependency) ->
        if (not d.Npm.d_dev) || p = st.root then Some (effective_dep st d)
        else None)
      (dependencies st p)

  let own_dependencies st p = List.map (fun d -> (p, d)) (dependencies st p)

  let desc_name st p (m : string * string) : Npm.Name.name option =
    match
      List.find_opt
        (fun (d : Npm.coq_Dependency) -> d.Npm.d_dir = fst m)
        (active_dependencies st p)
    with
    | Some { Npm.d_name; Npm.d_desc = Some s; _ } when d_name = snd m ->
        Some (Npm.Name.Desc (fst m, d_name, s))
    | _ -> None

  let own_peer_dependencies st p =
    List.map (fun r -> (p, r)) (peer_dependencies st p)

  let slot_names st p =
    List.sort_uniq String.compare
      (List.map
         (fun (d : Npm.coq_Dependency) -> d.Npm.d_name)
         (active_dependencies st p))

  let peer_names_at st q =
    List.sort_uniq String.compare
      (List.map
         (fun (r : Npm.coq_PeerDependency) -> r.Npm.p_name)
         (peer_dependencies st q))

  let peer_dependencies_named st (n : string) =
    List.map (fun (p, r) -> (p, xpeer st.ar r)) (Archive.peers_naming st.ar n)

  (* the granular versions lookup's sub-instance: the lookup reads no
     instance at a granular name *)
  let gran_sub_inst st =
    mk_inst st ~repo:Npm.RealPackageSet.empty ~deps:[] ~peers:[]

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
     peer dependencies are there for the root, whose granular node carries
     the edges that install its own peers; for any other package they emit no
     edge, so they are inert. *)
  let pkg_sub_inst st (p : string * string) =
    let ns = slot_names st p @ peer_names_at st p in
    mk_inst st ~repo:(repo_of st ns) ~deps:(own_dependencies st p)
      ~peers:(own_peer_dependencies st p)

  (* the peer dependencies of a holder p, which decide where it offers a
     name, and of its dependee q, which ask for one *)
  let two_peers st p q =
    own_peer_dependencies st p
    @ if q = p then [] else own_peer_dependencies st q

  (* A copy's own dependencies and slot names, which only a peer with
     default reads: the copy's sight admits its own copy, and a link to it
     decides whether it holds one.  A peer with default is a peer beside a
     dependency of its name, which only the shared reading keeps, the parser
     otherwise dropping the peer (npm's _loadDeps), so outside it they are
     left out: no lookup reads them, and reading them would load packuments
     npm does not. *)
  let dp_deps st q = if Archive.shared st.ar then own_dependencies st q else []
  let dp_names st q = if Archive.shared st.ar then slot_names st q else []

  (* the dependencies of a holder p and of its dependee q, whose peer with
     default reads its own *)
  let two_deps st p q =
    own_dependencies st p @ if q = p then [] else dp_deps st q

  (* the intermediate dependees lookup's sub-instance: p's own dependencies
     and peer dependencies and those of the dependee that was selected, and
     the repository at both slot names and at the directories the
     dependee's peers name *)
  let peer_sub_inst st (p : string * string) (m : string * string) (u : string)
      =
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
  let link_sub_inst st (p : string * string) (q : string * string) (a : string)
      =
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

  (* The root's intermediates read the peer dependencies naming their
     directory that the manifests loaded so far declare, so a root-installable
     peer loaded later can fill a directory that answered empty.  Their
     versions only grow (versions_intermediate_mono), which the resolver
     contract allows, so they are asked afresh each time rather than held;
     every other name's versions are fixed once asked. *)
  let grows st (n : Npm.Name.name) =
    match n with
    | Npm.Name.Intermediate (k, _, _) -> k = (fst st.root, fst st.root)
    | _ -> false

  let versions st (n : Npm.Name.name) : Npm.Version.version list =
    let answer () =
      match n with
      | Npm.Name.Granular _ ->
          Reduced.VSet.elements (Reduction.versions (gran_sub_inst st) n)
      | Npm.Name.Intermediate (k, v, m) ->
          Reduced.VSet.elements
            (Reduction.versions (int_sub_inst st (snd k, v) m) n)
      | Npm.Name.Sight (k, v, a) ->
          Reduced.VSet.elements
            (Reduction.versions (sight_sub_inst st (snd k, v) a) n)
      | Npm.Name.Link (k, v, m, u, a) ->
          Reduced.VSet.elements
            (Reduction.versions (link_sub_inst st (snd k, v) (snd m, u) a) n)
      | Npm.Name.Desc (_, t, _) ->
          Reduced.VSet.elements (Reduction.versions (desc_sub_inst st t) n)
    in
    if grows st n then answer () else Tbl.memo st.vcache n answer

  let holder st ((k, v) : (string * string) * string) (a : string) :
      Npm.Name.name option =
    let p = (snd k, v) in
    Reduction.holderName (holder_sub_inst st p p) (k, v) a

  let record_dir st (m : Npm.Name.name) =
    match m with
    | Npm.Name.Intermediate (k, v, d) ->
        let l = Tbl.find_list st.dirs (k, v) in
        if not (List.exists (fun x -> Npm.Name.compare x m = Pac.Eq) l) then begin
          Hashtbl.replace st.dirs (k, v) (m :: l);
          match desc_name st (snd k, v) d with
          | Some x -> Hashtbl.add st.desc_dirs x m
          | None -> ()
        end
    | _ -> ()

  let desc_dirs st (x : Npm.Name.name) = Hashtbl.find_all st.desc_dirs x

  let record_link st (l : Npm.Name.name) =
    match l with
    | Npm.Name.Link (k, v, _, _, a) -> (
        match holder st (k, v) a with
        | None -> ()
        | Some h ->
            record_dir st h;
            if
              not
                (List.exists
                   (fun x -> Npm.Name.compare x l = Pac.Eq)
                   (Hashtbl.find_all st.links_into h))
            then Hashtbl.add st.links_into h l)
    | _ -> ()

  let dependees st (s : Reduced.Package.t) : Reduced.Dependee.t list =
    let hs =
      match s with
      | Npm.Name.Granular (k, _), Npm.Version.Orig v ->
          Reduction.dependees (pkg_sub_inst st (snd k, v)) s
      | Npm.Name.Intermediate (k, v, m), Npm.Version.Orig u ->
          Reduction.dependees (peer_sub_inst st (snd k, v) m u) s
      | Npm.Name.Link (k, v, m, u, _), _ ->
          Reduction.dependees (holder_sub_inst st (snd k, v) (snd m, u)) s
      | _ -> Reduced.DependeeSet.empty
    in
    let hs = Reduced.DependeeSet.elements hs in
    List.iter
      (fun ((m, _) : Reduced.Dependee.t) ->
        record_dir st m;
        record_link st m)
      hs;
    hs

  let links_into st (h : Npm.Name.name) = Hashtbl.find_all st.links_into h
  let dirs st p = Tbl.find_list st.dirs p
end
