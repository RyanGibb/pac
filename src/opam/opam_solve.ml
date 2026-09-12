(* opam solving over the verified pipeline, deb_solve-style: the archive
   lives in hashtables; the extracted per-package/per-name lookups are
   called on slice instances justified by Opam.dependees_lookup* /
   versions_lookupReal; each package's variable-formula rows are reduced
   to core edges by the extracted VariableFormula reduction on its own
   sub-instance (VF's reduceReal_lookup* precedent); PubGrub solves the
   accumulated core graph lazily.  Trusted here (TCB): the parser, the
   version comparator, the valuation defaults, and the plumbing. *)

module E = Pac

let c2r = function -1 -> E.Lt | 0 -> E.Eq | _ -> E.Gt
let r2c = function E.Eq -> 0 | E.Lt -> -1 | E.Gt -> 1

module SName = struct
  type t = string

  let compare a b = c2r (compare (String.compare a b) 0)
  let eq_dec (a : string) b = String.equal a b
end

module OVerOT = struct
  type t = string

  let compare a b = c2r (compare (Opam_version.compare a b) 0)
  let eq_dec a b = Opam_version.compare a b = 0
end

(* ---- the archive ---- *)

type archive = {
  pkgs : (string, (string * Opam_parse.pkg_meta) list) Hashtbl.t;
  class_idx : (string, (string * string) list) Hashtbl.t;
}

let load_repo dir : archive =
  let pkgs = Hashtbl.create 4096 in
  let class_idx = Hashtbl.create 64 in
  let pkgdir = Filename.concat dir "packages" in
  Array.iter
    (fun name ->
      let ndir = Filename.concat pkgdir name in
      if Sys.is_directory ndir then
        Array.iter
          (fun nv ->
            match String.index_opt nv '.' with
            | Some i when String.sub nv 0 i = name -> (
                let version =
                  String.sub nv (i + 1) (String.length nv - i - 1)
                in
                let opam = Filename.concat (Filename.concat ndir nv) "opam" in
                if Sys.file_exists opam then
                  try
                    let m = Opam_parse.parse_file ~name ~version opam in
                    Hashtbl.replace pkgs name
                      ((version, m)
                      :: (try Hashtbl.find pkgs name with Not_found -> []));
                    List.iter
                      (fun k ->
                        Hashtbl.replace class_idx k
                          ((name, version)
                          ::
                            (try Hashtbl.find class_idx k with Not_found -> [])
                          ))
                      m.classes
                  with _ -> ())
            | _ -> ())
          (Sys.readdir ndir))
    (Sys.readdir pkgdir);
  { pkgs; class_idx }

let versions_of ar n =
  try List.map fst (Hashtbl.find ar.pkgs n) with Not_found -> []

let meta_of ar n v =
  try List.assoc v (Hashtbl.find ar.pkgs n)
  with Not_found ->
    {
      Opam_parse.name = n;
      version = v;
      depends = None;
      conflicts = [];
      classes = [];
      available = Opam_parse.FT;
      depexts = [];
      pindeps = [];
    }

module Make (XV : sig
  val vars : string list
end) =
struct
  module XF = struct
    type t = string

    let compare a b = c2r (compare (String.compare a b) 0)
    let eq_dec (a : string) b = String.equal a b
    let enum = XV.vars
  end

  module Op = E.Opam (SName) (OVerOT) (XF) (OVerOT) (SName)
  module Red = Op.Reduction
  module VF = Red.VF
  module VR = VF.Reduction
  module T = VR.T

  (* ---- valuation: the fixed environment ---- *)

  let globals =
    [
      ("os", "linux");
      ("os-family", "debian");
      ("os-distribution", "debian");
      ("os-version", "12");
      ("arch", "x86_64");
      ("opam-version", "2.2.0");
    ]

  let rho (x : string) : string option =
    match List.assoc_opt x globals with
    | Some v -> Some v
    | None -> (
        match String.index_opt x ':' with
        | None -> None
        | Some i -> (
            let local = String.sub x (i + 1) (String.length x - i - 1) in
            let owner = String.sub x 0 i in
            match local with
            | "build" | "post" -> Some "true"
            | "with-test" | "with-doc" | "with-dev-setup" | "dev" | "pinned" ->
                Some "false"
            | "name" -> Some owner
            | _ -> None))

  (* ---- parse-AST -> extracted terms ---- *)

  let xop : Opam_parse.op -> E.cmpOp = function
    | Opam_parse.Ge -> E.OpGe
    | Gt -> E.OpGt
    | Le -> E.OpLe
    | Lt -> E.OpLt
    | Eq -> E.OpEq
    | Ne -> E.OpNe

  let rec xfilt : Opam_parse.filt -> Op.coq_Filter = function
    | FT -> Op.FlTrue
    | FF -> Op.FlFalse
    | FCmp (o, x, y) -> Op.FlCmp (xop o, x, y)
    | FDef x -> Op.FlDef x
    | FAnd (a, b) -> Op.FlAnd (xfilt a, xfilt b)
    | FOr (a, b) -> Op.FlOr (xfilt a, xfilt b)
    | FNot a -> Op.FlNot (xfilt a)

  let rec xvc : Opam_parse.vc -> Op.coq_VConstraint = function
    | VTop -> Op.VCTop
    | VCmp (o, s) -> Op.VCCmp (xop o, s)
    | VAnd (a, b) -> Op.VCAnd (xvc a, xvc b)
    | VOr (a, b) -> Op.VCOr (xvc a, xvc b)

  let rec xoff : Opam_parse.off -> Op.coq_OFormula = function
    | OAtom (n, g, c) -> Op.OFAtom (n, xfilt g, xvc c)
    | OAnd (a, b) -> Op.OFAnd (xoff a, xoff b)
    | OOr (a, b) -> Op.OFOr (xoff a, xoff b)

  (* ---- slice instances (the shapes the lookup lemmas justify) ---- *)

  let pkgset_of = Op.PkgSet.ofList
  let clsrel_of = Op.ClsRel.ofList

  let repo_and_avail ar (names : string list) =
    let repo = ref [] and avl = ref [] in
    List.iter
      (fun m ->
        List.iter
          (fun v ->
            repo := (m, v) :: !repo;
            let meta = meta_of ar m v in
            if meta.Opam_parse.available <> Opam_parse.FT then
              avl := ((m, v), xfilt meta.Opam_parse.available) :: !avl)
          (versions_of ar m))
      (List.sort_uniq String.compare names);
    (pkgset_of !repo, !avl)

  let dummy = Op.OFAtom ("", Op.FlFalse, Op.VCTop)

  let inst_for ar (p : string * string) : Op.coq_Inst =
    let n, v = p in
    let m = meta_of ar n v in
    let dep_rows =
      match m.Opam_parse.depends with None -> [] | Some f -> [ (p, xoff f) ]
    in
    let cfl_rows =
      List.map
        (fun (cn, (g, c)) -> (p, (cn, (xfilt g, xvc c))))
        m.Opam_parse.conflicts
    in
    let cls_rows =
      List.concat_map
        (fun k ->
          ((n, v), k)
          :: List.map
               (fun q -> (q, k))
               (try Hashtbl.find ar.class_idx k with Not_found -> []))
        m.Opam_parse.classes
    in
    let dxt_rows =
      List.map (fun (e, g) -> (p, (e, xfilt g))) m.Opam_parse.depexts
    in
    let pind_rows =
      List.map (fun (nv, u) -> (p, (nv, u))) m.Opam_parse.pindeps
    in
    let row_names =
      let rec offn acc : Opam_parse.off -> string list = function
        | OAtom (m, _, _) -> m :: acc
        | OAnd (a, b) | OOr (a, b) -> offn (offn acc a) b
      in
      let acc =
        match m.Opam_parse.depends with None -> [] | Some f -> offn [] f
      in
      let acc =
        List.fold_left (fun a (cn, _) -> cn :: a) acc m.Opam_parse.conflicts
      in
      List.fold_left (fun a ((pn, _), _) -> pn :: a) acc m.Opam_parse.pindeps
    in
    let repo, avl = repo_and_avail ar row_names in
    {
      Op.inst_repo = repo;
      inst_dep = dep_rows;
      inst_dpo = [];
      inst_cfl = cfl_rows;
      inst_cls = clsrel_of cls_rows;
      inst_avl = avl;
      inst_dxt = dxt_rows;
      inst_pins = Op.PkgSet.empty;
      inst_pind = pind_rows;
      inst_goal = dummy;
      inst_inv = dummy;
    }

  let root_inst ar (goal : string) : Op.coq_Inst =
    let repo, avl = repo_and_avail ar [ goal ] in
    {
      Op.inst_repo = repo;
      inst_dep = [];
      inst_dpo = [];
      inst_cfl = [];
      inst_cls = Op.ClsRel.empty;
      inst_avl = avl;
      inst_dxt = [];
      inst_pins = Op.PkgSet.empty;
      inst_pind = [];
      inst_goal = Op.OFAtom (goal, Op.FlTrue, Op.VCTop);
      inst_inv = Op.OFAtom (goal, Op.FlFalse, Op.VCTop);
    }

  let name_inst ar (n : string) : Op.coq_Inst =
    let repo, avl = repo_and_avail ar [ n ] in
    {
      Op.inst_repo = repo;
      inst_dep = [];
      inst_dpo = [];
      inst_cfl = [];
      inst_cls = Op.ClsRel.empty;
      inst_avl = avl;
      inst_dxt = [];
      inst_pins = Op.PkgSet.empty;
      inst_pind = [];
      inst_goal = dummy;
      inst_inv = dummy;
    }

  (* The system packages a solution needs.  Depexts never reach the
     solver, so this runs once the resolution is fixed, on an instance
     carrying exactly the selected packages' depext rows; depextsOf, not
     a traversal here, decides which filters fire. *)
  let depexts_of ar (reals : (string * string) list) : string list =
    let dxt_rows =
      List.concat_map
        (fun p ->
          let n, v = p in
          List.map
            (fun (e, g) -> (p, (e, xfilt g)))
            (meta_of ar n v).Opam_parse.depexts)
        reals
    in
    let inst =
      {
        Op.inst_repo = Op.PkgSet.empty;
        inst_dep = [];
        inst_dpo = [];
        inst_cfl = [];
        inst_cls = Op.ClsRel.empty;
        inst_avl = [];
        inst_dxt = dxt_rows;
        inst_pins = Op.PkgSet.empty;
        inst_pind = [];
        inst_goal = dummy;
        inst_inv = dummy;
      }
    in
    Op.ESet.elements (Op.depextsOf rho inst (pkgset_of reals))

  (* ---- lazy core graph from per-package reductions ---- *)

  let yx x = VR.YSet.singleton (Red.pin rho x)

  type state = {
    ar : archive;
    edges : (VR.Name.t * VR.Version.t, T.DependeesSet.t) Hashtbl.t;
    gadget_vers : (VR.Name.t, VR.Version.t list) Hashtbl.t;
    processed : (VF.Pkg.t, unit) Hashtbl.t;
    real_vers : (string, VR.Version.t list) Hashtbl.t;
  }

  let mk_state ar =
    {
      ar;
      edges = Hashtbl.create 65536;
      gadget_vers = Hashtbl.create 65536;
      processed = Hashtbl.create 4096;
      real_vers = Hashtbl.create 4096;
    }

  let record_deprel st (d : T.DepRel.t) =
    List.iter
      (fun ((s, h) : T.DepElt.t) ->
        let prev =
          try Hashtbl.find st.edges s with Not_found -> T.DependeesSet.empty
        in
        Hashtbl.replace st.edges s (T.DependeesSet.add h prev))
      (T.DepRel.elements d)

  let record_real st (r : T.PkgSet.t) =
    List.iter
      (fun ((tn, tv) : T.Pkg.t) ->
        match tn with
        | VR.Name.Orig _ | VR.Name.Var _ -> ()
        | _ ->
            let prev =
              try Hashtbl.find st.gadget_vers tn with Not_found -> []
            in
            if not (List.mem tv prev) then
              Hashtbl.replace st.gadget_vers tn (tv :: prev))
      (T.PkgSet.elements r)

  (* reduce one VF package's rows to core, via the extracted lookups *)
  let verbose = Sys.getenv_opt "PACPROG" <> None
  let nproc = ref 0

  let process st (q : VF.Pkg.t) (inst : Op.coq_Inst) =
    if not (Hashtbl.mem st.processed q) then begin
      Hashtbl.replace st.processed q ();
      incr nproc;
      (if verbose then
         match q with
         | Red.TName.Real n, Red.TVer.RV v ->
             Printf.eprintf "[%d] %s.%s %.1fs\n%!" !nproc n v (Sys.time ())
         | _ -> Printf.eprintf "[%d] root %.1fs\n%!" !nproc (Sys.time ()));
      let forms = Red.dependees rho inst q in
      let d_q =
        VF.DepRel.ofList (List.map (fun f -> (q, f)) (Red.FSet.elements forms))
      in
      let r_q = VF.PkgSet.singleton q in
      record_deprel st (VR.reduceDeps yx d_q);
      record_real st (VR.reduceReal yx r_q d_q)
    end

  (* PubGrub interface *)
  module PName = struct
    type t = VR.Name.t

    let compare a b = r2c (VR.NameOT.compare a b)

    let pp_t fmt (tn : Red.TName.t) =
      match tn with
      | Red.TName.Root -> Format.fprintf fmt "root"
      | Red.TName.Real n -> Format.fprintf fmt "%s" n

    let pp fmt (n : t) =
      match n with
      | VR.Name.Orig tn -> pp_t fmt tn
      | VR.Name.Var x -> Format.fprintf fmt "var:%s" x
      | VR.Name.Disjunct (_, _) -> Format.fprintf fmt "<disj>"
      | VR.Name.NegDep (_, _) -> Format.fprintf fmt "<negdep>"
  end

  module PVersion = struct
    type t = VR.Version.t

    let compare a b = r2c (VR.VersionOT.compare a b)

    let pp fmt (v : t) =
      match v with
      | VR.Version.Orig (Red.TVer.RV v) -> Format.fprintf fmt "%s" v
      | VR.Version.Orig Red.TVer.UnitV -> Format.fprintf fmt "()"
      | VR.Version.Zero -> Format.fprintf fmt "z0"
      | VR.Version.One -> Format.fprintf fmt "z1"
      | VR.Version.VarVal Red.YU.Undef -> Format.fprintf fmt "undef"
      | VR.Version.VarVal (Red.YU.YVal y) -> Format.fprintf fmt "%s" y
  end

  module PG = Pubgrub.Make (PName) (PVersion)

  let solve ?(debug = false) ar (goal : string) =
    Pubgrub.set_debug debug;
    let st = mk_state ar in
    let root_q =
      (VR.Name.Orig Red.TName.Root, VR.Version.Orig Red.TVer.UnitV)
    in
    let versions (tn : VR.Name.t) : VR.Version.t list =
      match tn with
      | VR.Name.Orig (Red.TName.Real n) -> (
          try Hashtbl.find st.real_vers n
          with Not_found ->
            let vs =
              VF.VSet.elements
                (Red.versions rho (name_inst ar n) (Red.TName.Real n))
            in
            let vs = List.map (fun tv -> VR.Version.Orig tv) vs in
            Hashtbl.replace st.real_vers n vs;
            vs)
      | VR.Name.Orig Red.TName.Root -> [ VR.Version.Orig Red.TVer.UnitV ]
      | VR.Name.Var x -> [ VR.Version.VarVal (Red.pin rho x) ]
      | _ -> ( try Hashtbl.find st.gadget_vers tn with Not_found -> [])
    in
    let deps_cache = Hashtbl.create 65536 in
    let nq = ref 0 in
    let dependencies (tn : VR.Name.t) (tv : VR.Version.t) =
      incr nq;
      if verbose && !nq mod 10000 = 0 then
        Printf.eprintf "[q%d] %.1fs\n%!" !nq (Sys.time ());
      try Hashtbl.find deps_cache (tn, tv)
      with Not_found ->
        let r =
          (match (tn, tv) with
          | VR.Name.Orig Red.TName.Root, _ ->
              process st Red.rootPkg (root_inst ar goal)
          | VR.Name.Orig (Red.TName.Real n), VR.Version.Orig (Red.TVer.RV v) ->
              process st (Red.TName.Real n, Red.TVer.RV v) (inst_for ar (n, v))
          | _ -> ());
          let hs =
            try Hashtbl.find st.edges (tn, tv)
            with Not_found -> T.DependeesSet.empty
          in
          List.map
            (fun ((m, vs) : T.Dependees.t) ->
              (m, PG.Ranges.of_list (T.VSet.elements vs)))
            (T.DependeesSet.elements hs)
        in
        Hashtbl.replace deps_cache (tn, tv) r;
        r
    in
    let goal_range = PG.Ranges.of_list (versions (fst root_q)) in
    match PG.solve ~versions ~dependencies [ (fst root_q, goal_range) ] with
    | Error inc ->
        Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
        None
    | Ok sol ->
        let reals =
          List.filter_map
            (fun ((tn, tv) : VR.Name.t * VR.Version.t) ->
              match (tn, tv) with
              | VR.Name.Orig (Red.TName.Real n), VR.Version.Orig (Red.TVer.RV v)
                ->
                  Some (n, v)
              | _ -> None)
            sol
        in
        let reals = List.sort compare reals in
        Some (reals, List.length sol, depexts_of ar reals)
end
