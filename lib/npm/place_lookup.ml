open Place_encoding
module P = Npm_parse
module A = Archive
module Tbl = Pac_common.Tbl

type edge = {
  e : Npl.coq_Edge;
  acc : Pl.VSet.t;
  accepts : Npl.Occ.t list;
  id : int;
}

type t = {
  ar : A.t;
  root : string * string;
  optional : bool;
  ovr : (string * Npl.coq_Range) list;
  depth : int;
  dnat : E.nat;
  edge_tbl : (Npl.Occ.t, edge list) Hashtbl.t;
  acc_tbl : (string * Npl.coq_Range, int * Pl.VSet.t) Hashtbl.t;
  repo_at : (string, Npl.RepoSet.t) Hashtbl.t;
  repo_of : (string list, Npl.RepoSet.t) Hashtbl.t;
  real_tbl : (string, Npl.VS.t) Hashtbl.t;
  key_names : (string, string list) Hashtbl.t;
  key_inst : (string, int * Pl.coq_Inst) Hashtbl.t;
  vcache : (PName.t, int * PVersion.t list) Hashtbl.t;
  asked : (PName.t, unit) Hashtbl.t;
}

let create ~optional ~depth ar root =
  let ovr =
    match A.root_meta ar with
    | Some v -> List.map (fun (n, rg) -> (n, xrange rg)) v.P.v_ovr
    | None -> []
  in
  {
    ar;
    root;
    optional;
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
    asked = Hashtbl.create 65536;
  }

let archive st = st.ar
let depth st = st.depth
let names_asked st = Hashtbl.length st.asked

let meta st (x : Npl.Occ.t) =
  match x with
  | Npl.Occ.Top -> A.root_meta st.ar
  | Npl.Occ.Reg (m, v) -> A.meta st.ar (m, v.IVer.s)

let repo_at st (n : string) : Npl.RepoSet.t =
  Tbl.memo st.repo_at n (fun () ->
      Npl.RepoSet.ofList
        (List.map (fun v -> (n, IVer.make v)) (A.versions_of st.ar n)))

let repo_of st (ns : string list) : Npl.RepoSet.t =
  let ns = List.sort_uniq String.compare ns in
  Tbl.memo st.repo_of ns (fun () ->
      Npl.RepoSet.unions (List.map (repo_at st) ns))

(* Dist-tags and npm's reading of "*" shape the range handed to the
   calculus, as in the npm reading (its spec_range). *)
let xdep ar (d : P.dep) : Npl.coq_Dependency =
  {
    Npl.d_dir = d.P.d_dir;
    d_name = d.P.d_name;
    d_range = xrange (Lookup.spec_range ar d.P.d_name d.P.d_spec);
    d_dev = d.P.d_dev;
    d_optional = d.P.d_optional;
  }

let xpeer ar (r : P.peer) : Npl.coq_PeerDependency =
  {
    Npl.p_dir = r.P.p_name;
    p_name = r.P.p_target;
    p_range = xrange (Lookup.spec_range ar r.P.p_target r.P.p_spec);
    p_optional = r.P.p_optional;
  }

let mk_inst st ~repo ~deps ~peers : Npl.coq_Inst =
  {
    Npl.inst_repo = repo;
    inst_deps = deps;
    inst_peers = peers;
    inst_ovr = st.ovr;
    inst_root = fst st.root;
    inst_rootDeps = [];
    inst_rootPeers = [];
  }

(* The occupant's sub-instance for its edges: its package's manifest, and
   the repository at the packages its optional dependencies name once
   overridden, which decides whether each can be met. *)
let occ_inst st (x : Npl.Occ.t) : Npl.coq_Inst =
  let ds, rs =
    match meta st x with
    | None -> ([], [])
    | Some v ->
        ( List.filter_map
            (fun (d : P.dep) ->
              if d.P.d_optional && not st.optional then None
              else Some (xdep st.ar d))
            v.P.v_deps,
          List.map (xpeer st.ar) v.P.v_peers )
  in
  let base = mk_inst st ~repo:Npl.RepoSet.empty ~deps:[] ~peers:[] in
  let repo =
    repo_of st
      (List.filter_map
         (fun (d : Npl.coq_Dependency) ->
           if d.Npl.d_optional then
             Some (Npl.ovrName base d.Npl.d_dir d.Npl.d_name)
           else None)
         ds)
  in
  match x with
  | Npl.Occ.Top ->
      {
        (mk_inst st ~repo ~deps:[] ~peers:[]) with
        Npl.inst_rootDeps = ds;
        inst_rootPeers = rs;
      }
  | Npl.Occ.Reg (m, v) ->
      mk_inst st ~repo
        ~deps:(List.map (fun d -> ((m, v), d)) ds)
        ~peers:(List.map (fun r -> ((m, v), r)) rs)

(* An edge's accepted occupants read only the repository at the package it
   names, so they are computed once per package and range: acceptsIn over
   the name's versions, which are computed once per name. *)
let real_at st (n : string) : Npl.VS.t =
  Tbl.memo st.real_tbl n (fun () -> Npl.realVersions (repo_at st n) n)

let accepted st (e : Npl.coq_Edge) : int * Pl.VSet.t =
  let n = e.Npl.e_name in
  Tbl.memo st.acc_tbl (n, e.Npl.e_range) (fun () ->
      (Hashtbl.length st.acc_tbl, Npl.acceptsIn n e.Npl.e_range (real_at st n)))

let note_key st (k : string) (m : string) =
  let l = Tbl.find_list st.key_names k in
  if not (List.mem m l) then
    Hashtbl.replace st.key_names k (List.sort String.compare (m :: l))

(* seconds spent in each part of the lookups, for PAC_NPM_STATS *)
let prof : (string, float ref) Hashtbl.t = Hashtbl.create 8

let timed name f =
  let t = Unix.gettimeofday () in
  let r = f () in
  let a = Tbl.memo prof name (fun () -> ref 0.) in
  a := !a +. (Unix.gettimeofday () -. t);
  r

let print_prof () =
  Hashtbl.iter (fun k t -> Printf.eprintf "%s %.2fs\n" k !t) prof

let edges st (x : Npl.Occ.t) : edge list =
  Tbl.memo st.edge_tbl x (fun () ->
      timed "edges" (fun () ->
          List.map
            (fun (e : Npl.coq_Edge) ->
              note_key st e.Npl.e_dir e.Npl.e_name;
              let id, acc = accepted st e in
              { e; acc; accepts = Pl.VSet.elements acc; id })
            (Npl.edgesOf (occ_inst st x) x)))

let key_names st k = Tbl.find_list st.key_names k

(* A key's placement sub-instance, as Lookup.versions_lookupLoc reads it:
   every package the manifests loaded so far alias to the key, and their
   versions.  A manifest aliasing another package there grows it, so it is
   rebuilt then; this is the one place the driver's instance is the
   explored part of npm's rather than the whole. *)
let key_inst st (a : string) : Pl.coq_Inst =
  let ns = key_names st a in
  let g = List.length ns in
  match Hashtbl.find_opt st.key_inst a with
  | Some (g', i) when g' = g -> i
  | _ ->
      let i =
        Lk.nameInst
          {
            (mk_inst st ~repo:(repo_of st ns) ~deps:[] ~peers:[]) with
            Npl.inst_rootDeps =
              List.map
                (fun m ->
                  {
                    Npl.d_dir = a;
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
  | R.Name.Root -> [ R.Version.Occ Npl.Occ.Top ]
  | R.Name.Loc (l, a) | R.Name.Walk (l, a) -> (
      let g = List.length (key_names st a) in
      (* a location's versions read only the key and whether it is above
         the bound, so locations share them *)
      let k =
        match n with
        | R.Name.Loc _ ->
            R.Name.Loc ((if List.length l < st.depth then [] else l), a)
        | _ -> n
      in
      Hashtbl.replace st.asked n ();
      match Hashtbl.find_opt st.vcache k with
      | Some (g', vs) when g' = g -> vs
      | _ ->
          let vs =
            timed "versions" (fun () ->
                T.VSet.elements (R.versions (key_inst st a) st.dnat n))
          in
          Hashtbl.replace st.vcache k (g, vs);
          vs)

(* A name's dependees split by what each part reads, so that the parts are
   shared (Lookup.dependees_lookupOcc): the Tree atom reads the parent's
   location and key, and an edge's atom the location, the edge's kind and
   key, and its accepted set.  PubGrub asks for the dependees of every
   version of a location while it widens a decision, and there these
   differ only in some edges. *)
type part =
  | Tree of string list * int
  | Atom of string list * string * int * bool * bool

let atom_parts st (lam : string list) (x : Npl.Occ.t) =
  List.map
    (fun (ed : edge) ->
      let e = ed.e in
      ( Atom (lam, e.Npl.e_dir, ed.id, e.Npl.e_peer, e.Npl.e_opt),
        fun () -> timed "atoms" (fun () -> [ Lk.atomOf lam e ed.acc ]) ))
    (edges st x)

let parts st (n : PName.t) (u : PVersion.t) :
    (part * (unit -> T.Dependees.t list)) list option =
  match (n, u) with
  | R.Name.Root, R.Version.Occ x -> Some (atom_parts st [] x)
  | R.Name.Loc (l, a), R.Version.Occ x ->
      let tree =
        match l with
        | [] -> []
        | b :: _ ->
            [
              ( Tree (l, List.length (key_names st b)),
                fun () ->
                  timed "tree" (fun () ->
                      T.DependeesSet.elements
                        (R.treeAtom (key_inst st b).Pl.inst_repo l)) );
            ]
      in
      Some (tree @ atom_parts st (a :: l) x)
  | _ -> None

let dependees st (n, u) : T.Dependees.t list =
  match parts st n u with
  | Some ps -> List.concat_map (fun (_, f) -> f ()) ps
  | None -> (
      match (n, u) with
      | R.Name.Walk (l, a), w -> T.DependeesSet.elements (R.walkDeps l a w)
      | _ -> [])
