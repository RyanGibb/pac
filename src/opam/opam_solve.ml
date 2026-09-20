(* opam solving over the verified pipeline, deb_solve-style: the archive
   lives in hashtables; the extracted per-package/per-name lookups are
   called on sub-instances justified by Opam.dependees_lookup* /
   Opam.versions_lookup*, which evaluate every filter against [rho] as
   they run; each package's package-formula rows are then reduced to core edges
   by the extracted PackageFormula reduction on its own sub-instance;
   PubGrub solves the accumulated core graph lazily.  Trusted here (TCB):
   the parser, the version comparator, the valuation defaults, and the
   plumbing. *)

module E = Pac

let c2r = function -1 -> E.Lt | 0 -> E.Eq | _ -> E.Gt
let r2c = function E.Eq -> 0 | E.Lt -> -1 | E.Gt -> 1

let rec nat_int (n : E.nat) : int =
  match n with E.O -> 0 | E.S k -> 1 + nat_int k

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
  root : string;
  pkgs : (string, (string * Opam_parse.pkg_meta) list) Hashtbl.t;
  (* class -> its members among the names loaded so far.  Unlike every
     other index here this one is a preimage and so grows as names load;
     see the comment above [Make]. *)
  class_idx : (string, (string * string) list) Hashtbl.t;
  (* the versions a name flags avoid-version or deprecated; indexed
     because the comparator asks this of every version it is handed, and
     because all but a hundred or so names answer no *)
  avoid_idx : (string, string list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  (* wall time inside the parser, which the solve now interleaves with *)
  mutable t_parse : float;
}

let empty_archive root =
  {
    root;
    pkgs = Hashtbl.create 4096;
    class_idx = Hashtbl.create 64;
    avoid_idx = Hashtbl.create 64;
    n_names = 0;
    n_vers = 0;
    t_parse = 0.;
  }

(* A name's versions are one directory listing -- packages/<n>/<n>.<v>/opam
   -- so a name is parsed whole, the first time a sub-instance reads it,
   and a run touches the names the solver asks about and no others. *)
let load_name ar (name : string) : (string * Opam_parse.pkg_meta) list =
  match Hashtbl.find_opt ar.pkgs name with
  | Some vs -> vs
  | None ->
      let t = Unix.gettimeofday () in
      let ndir = Filename.concat (Filename.concat ar.root "packages") name in
      let acc = ref [] in
      if Sys.file_exists ndir && Sys.is_directory ndir then
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
                    acc := (version, m) :: !acc
                  with _ -> ())
            | _ -> ())
          (Sys.readdir ndir);
      let vs = !acc in
      Hashtbl.replace ar.pkgs name vs;
      ar.n_names <- ar.n_names + 1;
      ar.n_vers <- ar.n_vers + List.length vs;
      List.iter
        (fun (version, (m : Opam_parse.pkg_meta)) ->
          List.iter
            (fun k ->
              Hashtbl.replace ar.class_idx k
                ((name, version)
                ::
                (match Hashtbl.find_opt ar.class_idx k with
                | Some x -> x
                | None -> [])))
            m.classes;
          if m.avoid_version || m.deprecated then
            Hashtbl.replace ar.avoid_idx name
              (version
              ::
              (match Hashtbl.find_opt ar.avoid_idx name with
              | Some x -> x
              | None -> [])))
        vs;
      ar.t_parse <- ar.t_parse +. (Unix.gettimeofday () -. t);
      vs

let versions_of ar n = List.map fst (load_name ar n)

(* a package's rows are read only through its name's load, so they are
   never taken from a name parsed in part *)
let meta_of ar n v =
  try List.assoc v (load_name ar n)
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
      avoid_version = false;
      deprecated = false;
    }

(* loads, because the answer decides the class a version sorts into and
   the same version must sort the same way whether it is met in a name's
   candidate list or in a depender's range *)
let avoided ar n v =
  ignore (load_name ar n);
  match Hashtbl.find_opt ar.avoid_idx n with
  | None -> false
  | Some vs -> List.exists (fun w -> Opam_version.equal w v) vs

let class_members ar k =
  match Hashtbl.find_opt ar.class_idx k with Some x -> x | None -> []

(* There is no cone pass: the repository is uncovered as the solver asks
   for it, so each lookup theorem's sub-instance must be complete at the
   moment it answers.  That holds by construction for all but one row:
   versions
   and root_inst read the repository at one name, which load_name takes
   whole; inst_for reads (n, v)'s own dep/conflict/depext/pin-depends
   rows and the repository at rowNames, the names those rows mention, and
   loads every one of them; available filters ride along with the name
   they belong to; depexts_of reads the selected packages' own rows.

   Conflict classes are the exception, and only on one side.  A package's
   class formulas are read off its own declarations, so inst_for stays
   local; what is a preimage is the class package's version list, which is
   every declarer of the class and which no row of any one package names.
   class_idx therefore holds the declarers among the names loaded so far
   and may grow at any point in the run.  Not memoising is enough here,
   where it would not have been under a pairwise encoding: the growing
   answer is a versions answer, and PubGrub re-asks a name for its
   versions at every propagation step, whereas it consumes a node's
   dependency list once.  So cls_inst rebuilds the sub-instance from
   class_idx at every ask and a declarer parsed later is simply there.  A
   class version is also never asked for before its claimant's name has
   loaded, since the claim is that package's own edge. *)

module Make () = struct
  module Op = E.Opam (SName) (OVerOT) (SName) (OVerOT) (SName)
  module Red = Op.Reduction
  module PF = Red.PF
  module PFR = PF.Reduction
  module T = PFR.T

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

  (* ---- sub-instances (the shapes the lookup lemmas justify) ---- *)

  let pkgset_of = Op.PkgSet.ofList
  let clsrel_of = Op.ClsRel.ofList

  let repo_and_avail ar (ns : string list) =
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
      (List.sort_uniq String.compare ns);
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
    (* only this package's own declarations: the class package carries the
       partners, so no partner's rows are read here *)
    let cls_rows = List.map (fun k -> ((n, v), k)) m.Opam_parse.classes in
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

  (* Op.Reduction.classSubInst: the class relation restricted to k, which is
     all the class package's version lookup reads.  Built from class_idx at
     every ask and never held -- see the note above [Make]. *)
  let cls_inst ar (k : string) : Op.coq_Inst =
    {
      Op.inst_repo = Op.PkgSet.empty;
      inst_dep = [];
      inst_dpo = [];
      inst_cfl = [];
      inst_cls = clsrel_of (List.map (fun q -> (q, k)) (class_members ar k));
      inst_avl = [];
      inst_dxt = [];
      inst_pins = Op.PkgSet.empty;
      inst_pind = [];
      inst_goal = dummy;
      inst_inv = dummy;
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

  (* ---- PubGrub interface ---- *)

  module PName = struct
    type t = PFR.Name.t

    (* NameOT is a UsualOrderedType, so a name compares Eq to itself; the
       pointer test only skips the walk on interned names *)
    let compare a b = if a == b then 0 else r2c (PFR.NameOT.compare a b)

    let pp_t fmt (tn : Red.TName.t) =
      match tn with
      | Red.TName.Root -> Format.fprintf fmt "root"
      | Red.TName.Real n -> Format.fprintf fmt "%s" n
      | Red.TName.Cls k -> Format.fprintf fmt "conflict-class:%s" k

    let pp fmt (n : t) =
      match n with
      | PFR.Name.Orig tn -> pp_t fmt tn
      | PFR.Name.Disjunct _ -> Format.fprintf fmt "<disj>"
      | PFR.Name.NegDep (_, _) -> Format.fprintf fmt "<negdep>"
  end

  (* PubGrub decides the compare-maximum candidate, so preference lives
     here.  Newest-first among a name's own versions falls out of the
     encoded order, since V.compare is the opam order.  On top of it, a
     version flagged avoid-version or deprecated is a last resort rather
     than an impossibility, so it sits in a class below every unflagged
     version of its name and newest-first decides within each class --
     what opam does when it numbers a name's versions for the CUDF
     version-lag, avoid-versions after the rest.

     The class is carried on the version rather than read off it: which
     package a version belongs to is what decides, and a comparator sees
     two versions and not their name.  Every version PubGrub holds is
     handed to it by [versions] or by a dependency range, both of which
     know the name, so both tag as they go and the class is a function
     of the (name, version) pair -- keeping this a total order, and one
     consistent with the tags on any range the same name is compared
     against. *)
  module PVersion = struct
    type t = { avoid : bool; v : PFR.Version.t }

    let compare a b =
      match (a.avoid, b.avoid) with
      | true, false -> -1
      | false, true -> 1
      | _ -> if a.v == b.v then 0 else r2c (PFR.VersionOT.compare a.v b.v)

    let pp fmt (x : t) =
      match x.v with
      | PFR.Version.Orig (Red.TVer.RV v) -> Format.fprintf fmt "%s" v
      | PFR.Version.Orig Red.TVer.UnitV -> Format.fprintf fmt "()"
      | PFR.Version.Orig (Red.TVer.NV n) -> Format.fprintf fmt "%s" n
      | PFR.Version.Idx i -> Format.fprintf fmt "z%d" (nat_int i)
  end

  module PG = Pubgrub.Make (PName) (PVersion)

  let tag ar (tn : PFR.Name.t) (tv : PFR.Version.t) : PVersion.t =
    match (tn, tv) with
    | PFR.Name.Orig (Red.TName.Real n), PFR.Version.Orig (Red.TVer.RV v) ->
        { PVersion.avoid = avoided ar n v; v = tv }
    | _ -> { PVersion.avoid = false; v = tv }

  (* ---- lazy core graph from per-package reductions ---- *)

  module NameMap = Map.Make (struct
    type t = PFR.Name.t

    let compare a b = r2c (PFR.NameOT.compare a b)
  end)

  module NameSet = Set.Make (struct
    type t = PFR.Name.t

    let compare = PName.compare
  end)

  (* ---- 0install's decision order ---- *)

  (* The reduction hands a package's dependees back as a set, so the order
     its rows were written in is gone by the time the core graph holds
     them.  Read it back off the parsed formula: opam's CUDF depends list
     is the conjunctive spine in source order (opamSolver.ml,
     [preresolve_deps] then [ands_to_list]), and that is the order
     0install walks. *)
  let dep_index ar (n : string) (v : string) : (string, int) Hashtbl.t =
    let tbl = Hashtbl.create 16 in
    let rec spine acc : Opam_parse.off -> Opam_parse.off list = function
      | OAnd (a, b) -> spine (spine acc a) b
      | f -> f :: acc
    in
    let rec names acc : Opam_parse.off -> string list = function
      | OAtom (m, _, _) -> m :: acc
      | OAnd (a, b) | OOr (a, b) -> names (names acc a) b
    in
    (match (meta_of ar n v).Opam_parse.depends with
    | None -> ()
    | Some f ->
        List.iteri
          (fun i c ->
            List.iter
              (fun m -> if not (Hashtbl.mem tbl m) then Hashtbl.add tbl m i)
              (names [] c))
          (List.rev (spine [] f)));
    tbl

  let rec form_names acc (f : PF.coq_Formula) =
    match f with
    | PF.FDep (Red.TName.Real m, _) -> m :: acc
    | PF.FDep (_, _) -> acc
    | PF.FConj (a, b) | PF.FDisj (a, b) -> form_names (form_names acc a) b
    | PF.FNeg a -> form_names acc a

  (* where a dependee sits on the depender's spine, or None for the
     synthetic packages 0install's decider never reaches: a conflict is a
     `Restricts dependency it skips outright, and a conflict class is an
     at_most_one clause over implementations rather than a role at all
     (solver_core.ml, [Conflict_classes] and [check_dep]). *)
  let zi_rank tbl (m : PFR.Name.t) : int option =
    let best acc s =
      match (Hashtbl.find_opt tbl s, acc) with
      | Some i, Some j -> Some (min i j)
      | Some i, None -> Some i
      | None, a -> a
    in
    match m with
    | PFR.Name.Orig (Red.TName.Real s) -> Hashtbl.find_opt tbl s
    | PFR.Name.Disjunct fs ->
        List.fold_left
          (fun a f -> List.fold_left best a (form_names [] f))
          None fs
    | _ -> None

  let zi_walkable (m : PFR.Name.t) =
    match m with
    | PFR.Name.NegDep (_, _) | PFR.Name.Orig (Red.TName.Cls _) -> false
    | _ -> true

  type state = {
    ar : archive;
    edges : (PFR.Name.t * PFR.Version.t, T.DependeesSet.t) Hashtbl.t;
    synthetic_vers : (PFR.Name.t, PVersion.t list) Hashtbl.t;
    processed : (PF.Pkg.t, unit) Hashtbl.t;
    real_vers : (string, PVersion.t list) Hashtbl.t;
    mutable canon : PFR.Name.t NameMap.t;
  }

  let mk_state ar =
    {
      ar;
      edges = Hashtbl.create 65536;
      synthetic_vers = Hashtbl.create 65536;
      processed = Hashtbl.create 4096;
      real_vers = Hashtbl.create 4096;
      canon = NameMap.empty;
    }

  (* A Disjunct or NegDep name carries its formulas, so comparing
     two equal names walks both in full, and PubGrub does that on every
     dependency-list scan and map hit.  Each version's reduction builds
     its own copy of a synthetic name shared across versions; one
     representative per name lets PName.compare answer equality by
     pointer.  The map is keyed by NameOT itself, so which names unify
     is exactly NameOT equality and PubGrub's ordering is unchanged. *)
  let intern st (m : PFR.Name.t) : PFR.Name.t =
    match NameMap.find_opt m st.canon with
    | Some c -> c
    | None ->
        st.canon <- NameMap.add m m st.canon;
        m

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
        | PFR.Name.Orig _ -> ()
        | _ ->
            let tv = tag st.ar tn tv in
            let prev =
              try Hashtbl.find st.synthetic_vers tn with Not_found -> []
            in
            if not (List.mem tv prev) then
              Hashtbl.replace st.synthetic_vers tn (tv :: prev))
      (T.PkgSet.elements r)

  (* reduce one package-formula package's rows to core, via the extracted
     lookups *)
  let verbose = Sys.getenv_opt "PACPROG" <> None
  let nproc = ref 0

  let process st (q : PF.Pkg.t) (inst : Op.coq_Inst) =
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
        PF.DepRel.ofList (List.map (fun f -> (q, f)) (Red.FSet.elements forms))
      in
      let r_q = PF.PkgSet.singleton q in
      record_deprel st (PFR.reduceDeps d_q);
      record_real st (PFR.reduceReal r_q d_q)
    end

  let solve ?(debug = false) ?(zi_order = false) ar (goal : string) =
    Pubgrub.set_debug debug;
    let root_q =
      (PFR.Name.Orig Red.TName.Root, PFR.Version.Orig Red.TVer.UnitV)
    in
    let st = mk_state ar in
    nproc := 0;
    (* Wall time inside the two callbacks; the rest of PG.solve is
       PubGrub's own search.  Only accumulated when verbose, and with
       gettimeofday rather than Sys.time: the callbacks run ~10^6 times
       per solve and a getrusage syscall each would be seconds. *)
    let t_callbacks = ref 0. in
    let timed f =
      if verbose then begin
        let t0 = Unix.gettimeofday () in
        let r = f () in
        t_callbacks := !t_callbacks +. (Unix.gettimeofday () -. t0);
        r
      end
      else f ()
    in
    let versions (tn : PFR.Name.t) : PVersion.t list =
      timed @@ fun () ->
      match tn with
      | PFR.Name.Orig (Red.TName.Real n) -> (
          try Hashtbl.find st.real_vers n
          with Not_found ->
            let vs =
              PF.VSet.elements
                (Red.versions rho (name_inst ar n) (Red.TName.Real n))
            in
            let vs = List.map (fun tv -> tag ar tn (PFR.Version.Orig tv)) vs in
            Hashtbl.replace st.real_vers n vs;
            vs)
      | PFR.Name.Orig Red.TName.Root ->
          [ { PVersion.avoid = false; v = PFR.Version.Orig Red.TVer.UnitV } ]
      (* The one name that cannot be held: its versions are the whole
         preimage of the class relation at k, so class_idx knows only the
         declarers among the names loaded so far.  Recomputing the handful
         of rows at every ask lets a declarer parsed later simply be
         there, where a cache would freeze the answer mid-run. *)
      | PFR.Name.Orig (Red.TName.Cls k) ->
          List.map
            (fun tv -> tag ar tn (PFR.Version.Orig tv))
            (PF.VSet.elements
               (Red.versions rho (cls_inst ar k) (Red.TName.Cls k)))
      | _ -> ( try Hashtbl.find st.synthetic_vers tn with Not_found -> [])
    in
    let deps_cache = Hashtbl.create 65536 in
    let nq = ref 0 in
    let dependencies (tn : PFR.Name.t) ({ PVersion.v = tv; _ } : PVersion.t) =
      incr nq;
      if verbose && !nq mod 10000 = 0 then
        Printf.eprintf "[q%d] %.1fs\n%!" !nq (Sys.time ());
      timed @@ fun () ->
      try Hashtbl.find deps_cache (tn, tv)
      with Not_found ->
        let r =
          (match (tn, tv) with
          | PFR.Name.Orig Red.TName.Root, _ ->
              process st Red.rootPkg (root_inst ar goal)
          | PFR.Name.Orig (Red.TName.Real n), PFR.Version.Orig (Red.TVer.RV v)
            ->
              process st (Red.TName.Real n, Red.TVer.RV v) (inst_for ar (n, v))
          | _ -> ());
          let hs =
            try Hashtbl.find st.edges (tn, tv)
            with Not_found -> T.DependeesSet.empty
          in
          List.map
            (fun ((m, vs) : T.Dependees.t) ->
              ( intern st m,
                PG.Ranges.of_list (List.map (tag ar m) (T.VSet.elements vs)) ))
            (T.DependeesSet.elements hs)
        in
        Hashtbl.replace deps_cache (tn, tv) r;
        r
    in
    (* the dependees of a decided package, in source order and without the
       synthetic packages 0install has no role for *)
    let order_cache = Hashtbl.create 4096 in
    let zi_deps (tn : PFR.Name.t) (pv : PVersion.t) : PFR.Name.t list =
      ignore (dependencies tn pv);
      let hs =
        try Hashtbl.find st.edges (tn, pv.PVersion.v)
        with Not_found -> T.DependeesSet.empty
      in
      let ds = List.map fst (T.DependeesSet.elements hs) in
      match (tn, pv.PVersion.v) with
      | PFR.Name.Orig (Red.TName.Real n), PFR.Version.Orig (Red.TVer.RV v) ->
          let tbl =
            match Hashtbl.find_opt order_cache (n, v) with
            | Some t -> t
            | None ->
                let t = dep_index ar n v in
                Hashtbl.add order_cache (n, v) t;
                t
          in
          List.filter_map
            (fun m -> Option.map (fun i -> (i, m)) (zi_rank tbl m))
            ds
          |> List.stable_sort (fun (i, _) (j, _) -> compare (i : int) j)
          |> List.map snd
      (* the root, which carries the goal, and a disjunct package, which
         carries the alternative it was decided to: no written order to
         restore either way *)
      | _ -> List.filter zi_walkable ds
    in
    (* 0install's [decider] (solver_core.ml): walk the roles already
       selected depth-first from the root, each one's dependencies in the
       order they are written, and take the first role still undecided.
       PubGrub's [Entailed] is that "undecided" -- forced into the solution
       but not yet decided -- and [Decided] is its "selected". *)
    let zi_next ~assigned (open_names : (PFR.Name.t * int) list) =
      let opens =
        List.fold_left
          (fun s (n, _) -> NameSet.add n s)
          NameSet.empty open_names
      in
      let exception Found of PFR.Name.t in
      let rec visit seen n =
        if NameSet.mem n seen then seen
        else
          let seen = NameSet.add n seen in
          match assigned n with
          | PG.Unselected -> seen
          | PG.Entailed _ ->
              if NameSet.mem n opens then raise (Found n) else seen
          | PG.Decided v -> List.fold_left visit seen (zi_deps n v)
      in
      try
        ignore (visit NameSet.empty (PFR.Name.Orig Red.TName.Root));
        (* nothing on the walk is open: leave the solver's own choice *)
        fst (List.hd open_names)
      with Found n -> n
    in
    let next = if zi_order then Some zi_next else None in
    let goal_range = PG.Ranges.of_list (versions (fst root_q)) in
    let t0 = Unix.gettimeofday () in
    let result =
      PG.solve ?next ~vers:versions ~deps:dependencies
        [ (fst root_q, goal_range) ]
    in
    if verbose then begin
      let total = Unix.gettimeofday () -. t0 in
      Printf.eprintf
        "PG.solve %.2fs: %.2fs in callbacks (%d dependency lookups, %d \
         packages reduced), %.2fs PubGrub\n\
         %!"
        total !t_callbacks !nq !nproc (total -. !t_callbacks)
    end;
    match result with
    | Error inc ->
        Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
        None
    | Ok sol ->
        (* back through the proved decoders, in the two layers the
           reduction composes: the core solution decodes to the package
           formula's packages, and those to opam's.  Reading the reals off
           the solution here instead would be a third, unproved, decoder
           -- and it is what the soundness theorem is stated about. *)
        let core =
          T.PkgSet.ofList
            (List.map
               (fun ((tn, { PVersion.v = tv; _ }) : PFR.Name.t * PVersion.t) ->
                 (tn, tv))
               sol)
        in
        let reals =
          Op.PkgSet.elements (Red.decodeS (PFR.packageFormulaResolution core))
        in
        let reals = List.sort compare reals in
        Some (reals, List.length sol, depexts_of ar reals)
end
