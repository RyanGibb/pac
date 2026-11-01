module Tbl = Pac_common.Tbl

module Make (Place_encoding : Place_encoding.S) = struct
  open Place_encoding

  type edge = {
    e : NpmPlacement.coq_Edge;
    acc : Placement.VSet.t;
    accepts : NpmPlacement.Occupant.t list;
    id : int;
  }

  type t = {
    ar : Archive.t;
    root : string * string;
    ovr : (string * NpmPlacement.coq_Range) list;
    depth : int;
    dnat : Pac.nat;
    edge_tbl : (NpmPlacement.Occupant.t, edge list) Hashtbl.t;
    acc_tbl :
      (string * NpmPlacement.coq_Range, int * Placement.VSet.t) Hashtbl.t;
    repo_at : (string, NpmPlacement.RealPackageSet.t) Hashtbl.t;
    repo_of : (string list, NpmPlacement.RealPackageSet.t) Hashtbl.t;
    real_tbl : (string, NpmPlacement.VSet.t) Hashtbl.t;
    key_names : (string, string list) Hashtbl.t;
    key_inst : (string, int * Placement.coq_Inst) Hashtbl.t;
    vcache : (PName.t, int * PVersion.t list) Hashtbl.t;
  }

  let create ~depth ar root =
    let ovr =
      match Archive.root_meta ar with
      | Some v -> List.map (fun (n, rg) -> (n, xrange rg)) v.Npm_parse.v_ovr
      | None -> []
    in
    {
      ar;
      root;
      ovr;
      depth;
      dnat = Ot.int_nat depth;
      edge_tbl = Hashtbl.create 16384;
      acc_tbl = Hashtbl.create 16384;
      repo_at = Hashtbl.create 4096;
      repo_of = Hashtbl.create 4096;
      real_tbl = Hashtbl.create 4096;
      key_names = Hashtbl.create 4096;
      key_inst = Hashtbl.create 4096;
      vcache = Hashtbl.create 65536;
    }

  let archive st = st.ar
  let depth st = st.depth

  (* The project, which only the root holds, is not the registry's package
     of its name even at its version: arborist loads devDependencies for the
     top node alone. *)
  let meta st (x : NpmPlacement.Occupant.t) =
    match x with
    | NpmPlacement.Occupant.Proj -> Archive.root_meta st.ar
    | NpmPlacement.Occupant.Reg (m, v) -> Archive.meta st.ar (m, v.IVer.s)

  let repo_at st (n : string) : NpmPlacement.RealPackageSet.t =
    Tbl.memo st.repo_at n (fun () ->
        NpmPlacement.RealPackageSet.ofList
          (List.map (fun v -> (n, IVer.make v)) (Archive.versions_of st.ar n)))

  let repo_of st (ns : string list) : NpmPlacement.RealPackageSet.t =
    let ns = List.sort_uniq String.compare ns in
    Tbl.memo st.repo_of ns (fun () ->
        NpmPlacement.RealPackageSet.unions (List.map (repo_at st) ns))

  (* Dist-tags and npm's reading of "*" shape the range handed to the
     calculus, as in the npm reading. *)
  let xdep ar (d : Npm_parse.dep) : NpmPlacement.coq_Dependency =
    {
      NpmPlacement.d_dir = d.Npm_parse.d_dir;
      d_name = d.Npm_parse.d_name;
      d_range =
        xrange (Lookup.spec_range ar d.Npm_parse.d_name d.Npm_parse.d_spec);
      d_dev = d.Npm_parse.d_dev;
      d_optional = d.Npm_parse.d_optional;
    }

  let xpeer ar (r : Npm_parse.peer) : NpmPlacement.coq_PeerDependency =
    {
      NpmPlacement.p_dir = r.Npm_parse.p_name;
      p_name = r.Npm_parse.p_dependee_name;
      p_range =
        xrange
          (Lookup.spec_range ar r.Npm_parse.p_dependee_name r.Npm_parse.p_spec);
      p_optional = r.Npm_parse.p_optional;
    }

  let mk_inst st ~repo ~deps ~peers : NpmPlacement.coq_Inst =
    {
      NpmPlacement.inst_real = repo;
      inst_deps = deps;
      inst_peers = peers;
      inst_ovr = st.ovr;
      inst_root = fst st.root;
      inst_rootDeps = [];
      inst_rootPeers = [];
    }

  (* The occupant's sub-instance for its edges: its package's manifest.  The
     versions that decide whether each optional dependency can be met are
     real_at's, at the package it names once overridden. *)
  let occ_inst st (x : NpmPlacement.Occupant.t) : NpmPlacement.coq_Inst =
    let ds, rs =
      match meta st x with
      | None -> ([], [])
      | Some v ->
          ( List.map (xdep st.ar) v.Npm_parse.v_deps,
            List.map (xpeer st.ar) v.Npm_parse.v_peers )
    in
    match x with
    | NpmPlacement.Occupant.Proj ->
        {
          (mk_inst st ~repo:NpmPlacement.RealPackageSet.empty ~deps:[] ~peers:[])
          with
          NpmPlacement.inst_rootDeps = ds;
          inst_rootPeers = rs;
        }
    | NpmPlacement.Occupant.Reg (m, v) ->
        mk_inst st ~repo:NpmPlacement.RealPackageSet.empty
          ~deps:(List.map (fun d -> ((m, v), d)) ds)
          ~peers:(List.map (fun r -> ((m, v), r)) rs)

  (* An edge's accepted occupants read only the repository at the package it
     names, so they are computed once per package and range: acceptsIn over
     the name's versions, which are computed once per name. *)
  let real_at st (n : string) : NpmPlacement.VSet.t =
    Tbl.memo st.real_tbl n (fun () ->
        NpmPlacement.realVersions (repo_at st n) n)

  let accepted st (e : NpmPlacement.coq_Edge) : int * Placement.VSet.t =
    let n = e.NpmPlacement.e_name in
    Tbl.memo st.acc_tbl (n, e.NpmPlacement.e_range) (fun () ->
        ( Hashtbl.length st.acc_tbl,
          NpmPlacement.Reduction.acceptsIn n e.NpmPlacement.e_range
            (real_at st n) ))

  let note_key st (k : string) (m : string) =
    let l = Tbl.find_list st.key_names k in
    if not (List.mem m l) then
      Hashtbl.replace st.key_names k (List.sort String.compare (m :: l))

  (* An edge's key is noted before its atom is built, so the walk name the
     atom constrains already lists every package the atom accepts: every
     version set handed to the solver holds exact versions, as the resolver
     contract asks. *)
  let edges st (x : NpmPlacement.Occupant.t) : edge list =
    Tbl.memo st.edge_tbl x (fun () ->
        List.map
          (fun (e : NpmPlacement.coq_Edge) ->
            note_key st e.NpmPlacement.e_dir e.NpmPlacement.e_name;
            let id, acc = accepted st e in
            { e; acc; accepts = Placement.VSet.elements acc; id })
          (NpmPlacement.edgesOfBy (real_at st) (occ_inst st x) x))

  let key_names st k = Tbl.find_list st.key_names k

  (* A key's placement sub-instance: every package the manifests loaded so
     far alias to the key, and their versions.  A manifest aliasing another
     package there grows it, so it is rebuilt then; this is the one place
     the driver's instance is the explored part of npm's rather than the
     whole.  A location's and a walk's versions then only grow, which the
     resolver contract allows. *)
  let key_inst st (a : string) : Placement.coq_Inst =
    let ns = key_names st a in
    let g = List.length ns in
    match Hashtbl.find_opt st.key_inst a with
    | Some (g', i) when g' = g -> i
    | _ ->
        let i =
          ReductionLookup.nameInst
            {
              (mk_inst st ~repo:(repo_of st ns) ~deps:[] ~peers:[]) with
              NpmPlacement.inst_rootDeps =
                List.map
                  (fun m ->
                    {
                      NpmPlacement.d_dir = a;
                      d_name = m;
                      d_range = [];
                      d_dev = false;
                      d_optional = false;
                    })
                  ns;
            }
        in
        Hashtbl.replace st.key_inst a (g, i);
        i

  let versions st (n : PName.t) : PVersion.t list =
    match n with
    | Reduction.Name.Root ->
        [ Reduction.Version.Occ NpmPlacement.Occupant.Proj ]
    | Reduction.Name.Loc (l, a) | Reduction.Name.Walk (l, a) -> (
        let g = List.length (key_names st a) in
        (* a location's versions read only the key and whether it is above
           the bound, so locations share them *)
        let k =
          match n with
          | Reduction.Name.Loc _ ->
              Reduction.Name.Loc
                ((if List.length l < st.depth then [] else l), a)
          | _ -> n
        in
        match Hashtbl.find_opt st.vcache k with
        | Some (g', vs) when g' = g -> vs
        | _ ->
            let vs =
              Reduced.VSet.elements
                (Reduction.versions (key_inst st a) st.dnat n)
            in
            Hashtbl.replace st.vcache k (g, vs);
            vs)

  (* A name's dependees split by what each part reads, so that the parts are
     shared: an edge's atom reads the location, the edge's kind and key, and
     its accepted set.  PubGrub asks for the dependees of every version of a
     location while it widens a decision, and there these differ only in
     some edges. *)
  type part = Atom of string list * string * int * bool * bool

  let atom_parts st (lam : string list) (x : NpmPlacement.Occupant.t) =
    List.map
      (fun (ed : edge) ->
        let e = ed.e in
        ( Atom
            ( lam,
              e.NpmPlacement.e_dir,
              ed.id,
              e.NpmPlacement.e_peer,
              e.NpmPlacement.e_optional ),
          fun () -> [ ReductionLookup.atomOf lam e ed.acc ] ))
      (edges st x)

  let parts st (n : PName.t) (u : PVersion.t) :
      (part * (unit -> Reduced.Dependee.t list)) list option =
    match (n, u) with
    | Reduction.Name.Root, Reduction.Version.Occ x -> Some (atom_parts st [] x)
    | Reduction.Name.Loc (l, a), Reduction.Version.Occ x ->
        Some (atom_parts st (a :: l) x)
    | _ -> None

  let dependees st (n, u) : Reduced.Dependee.t list =
    match parts st n u with
    | Some ps -> List.concat_map (fun (_, f) -> f ()) ps
    | None -> (
        match (n, u) with
        | Reduction.Name.Walk (l, a), w ->
            Reduced.DependeeSet.elements (Reduction.walkDeps l a w)
        | _ -> [])
end
