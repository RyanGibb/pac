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
   -- so a name is parsed whole, the first time a slice reads it, and a run
   touches the names the solver asks about and no others. *)
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
   for it, so each lookup theorem's slice must be complete at the moment
   it answers.  That holds by construction for all but one row: versions
   and root_inst read the repository at one name, which load_name takes
   whole; inst_for reads (n, v)'s own dep/conflict/depext/pin-depends
   rows and the repository at rowNames, the names those rows mention, and
   loads every one of them; available filters ride along with the name
   they belong to; depexts_of reads the selected packages' own rows.

   Conflict classes are the exception.  clsForms gives a package one
   negative dependency per same-class partner of a different name, and
   that partner set is the class relation's preimage at the class -- no
   row of any one package names the others -- so class_idx holds the
   members among the names loaded so far and may grow after a package has
   been reduced.  Two things keep that honest.  A class-membership answer
   is never memoised: cls_rows recomputes it from class_idx at every ask,
   so a package parsed later is simply there.  And recomputing is not by
   itself enough, because PubGrub consumes a node's dependency list once
   and need not ask again, so a partner that arrives after the ask would
   never reach the search: Make.solve records, for each package it
   reduces, how many members each of that package's classes had at the
   time, and re-runs the whole search on the now-warmer archive if any of
   those counts grew.  The archive only grows and the repository is
   finite, so the re-runs converge; in practice they do not fire at all,
   because a class's members are the alternatives of one disjunction --
   ocaml-base-compiler | ocaml-variants | ocaml-system | ... -- and
   rowNames loads all of them together, before any of them is reduced. *)

module Make () = struct
  module XF = struct
    type t = string

    let compare a b = c2r (compare (String.compare a b) 0)
    let eq_dec (a : string) b = String.equal a b

    (* X's inhabitants are opam's filter variables, of which there is no
       finite listing to hand: a lazy run does not know which ones the
       rows it has yet to read will mention, and enumerating them would
       mean parsing the archive up front, which is the whole cost this
       driver exists to avoid.  Nothing is lost by leaving it empty.  The
       list has exactly two readers.  varBlock, in reduceReal, declares
       (Var x, VarVal y) a package for each x -- but this driver never
       reads Var candidates off reduceReal (record_real drops Var names);
       the versions callback below answers Var x with yx x directly, for
       every x, which is that block for the full universe rather than for
       a list.  pinsFormula, at the root, conjoins x = pin rho x for each
       x, to force the solved-for assignment to agree with rho; here yx x
       is the singleton {pin rho x}, so every Var edge encodeNNF emits
       already lands inside it and extractAssignment falls back to its
       least element when no Var x node was forced at all -- the
       assignment is rho pointwise whether or not the root says so, and
       each conjunct is a dependency on a name with one candidate that
       equals the pinned value.  Listing the archive's 4942 variables
       therefore only added 4942 tautological root edges, and 4942 nodes
       to the reported core solution size. *)
    let enum = []
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
    (* read afresh, never held: this is the one slice that can grow *)
    let cls_rows =
      List.concat_map
        (fun k ->
          ((n, v), k) :: List.map (fun q -> (q, k)) (class_members ar k))
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

  (* ---- PubGrub interface ---- *)

  module PName = struct
    type t = VR.Name.t

    (* NameOT is a UsualOrderedType, so a name compares Eq to itself; the
       pointer test only skips the walk on interned names *)
    let compare a b = if a == b then 0 else r2c (VR.NameOT.compare a b)

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
    type t = { avoid : bool; v : VR.Version.t }

    let compare a b =
      match (a.avoid, b.avoid) with
      | true, false -> -1
      | false, true -> 1
      | _ -> if a.v == b.v then 0 else r2c (VR.VersionOT.compare a.v b.v)

    let pp fmt (x : t) =
      match x.v with
      | VR.Version.Orig (Red.TVer.RV v) -> Format.fprintf fmt "%s" v
      | VR.Version.Orig Red.TVer.UnitV -> Format.fprintf fmt "()"
      | VR.Version.Zero -> Format.fprintf fmt "z0"
      | VR.Version.One -> Format.fprintf fmt "z1"
      | VR.Version.VarVal Red.YU.Undef -> Format.fprintf fmt "undef"
      | VR.Version.VarVal (Red.YU.YVal y) -> Format.fprintf fmt "%s" y
  end

  module PG = Pubgrub.Make (PName) (PVersion)

  let tag ar (tn : VR.Name.t) (tv : VR.Version.t) : PVersion.t =
    match (tn, tv) with
    | VR.Name.Orig (Red.TName.Real n), VR.Version.Orig (Red.TVer.RV v) ->
        { PVersion.avoid = avoided ar n v; v = tv }
    | _ -> { PVersion.avoid = false; v = tv }

  (* ---- lazy core graph from per-package reductions ---- *)

  let yx x = VR.YSet.singleton (Red.pin rho x)

  module NameMap = Map.Make (struct
    type t = VR.Name.t

    let compare a b = r2c (VR.NameOT.compare a b)
  end)

  type state = {
    ar : archive;
    edges : (VR.Name.t * VR.Version.t, T.DependeesSet.t) Hashtbl.t;
    gadget_vers : (VR.Name.t, PVersion.t list) Hashtbl.t;
    processed : (VF.Pkg.t, unit) Hashtbl.t;
    real_vers : (string, PVersion.t list) Hashtbl.t;
    (* per reduced package, how many members each of its own conflict
       classes had when its rows were read; the one thing a later load can
       invalidate *)
    mutable canon : VR.Name.t NameMap.t;
  }

  let mk_state ar =
    {
      ar;
      edges = Hashtbl.create 65536;
      gadget_vers = Hashtbl.create 65536;
      processed = Hashtbl.create 4096;
      real_vers = Hashtbl.create 4096;
      canon = NameMap.empty;
    }

  (* A Disjunct or NegDep gadget name carries its formulas, so comparing
     two equal names walks both in full, and PubGrub does that on every
     dependency-list scan and map hit.  Each version's reduction builds
     its own copy of a gadget name shared across versions; one
     representative per name lets PName.compare answer equality by
     pointer.  The map is keyed by NameOT itself, so which names unify
     is exactly NameOT equality and PubGrub's ordering is unchanged. *)
  let intern st (m : VR.Name.t) : VR.Name.t =
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
        | VR.Name.Orig _ | VR.Name.Var _ -> ()
        | _ ->
            let tv = tag st.ar tn tv in
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

  let solve ?(debug = false) ar (goal : string) =
    Pubgrub.set_debug debug;
    let root_q =
      (VR.Name.Orig Red.TName.Root, VR.Version.Orig Red.TVer.UnitV)
    in
    (* One pass of the search over the archive as it stands.  PubGrub
       consumes a node's dependencies once, so a conflict-class partner
       that loads after that node was asked never reaches it; the caller
       re-enters here on the warmer archive when that happened. *)
    let attempt () =
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
      let versions (tn : VR.Name.t) : PVersion.t list =
        timed @@ fun () ->
        match tn with
        | VR.Name.Orig (Red.TName.Real n) -> (
            try Hashtbl.find st.real_vers n
            with Not_found ->
              let vs =
                VF.VSet.elements
                  (Red.versions rho (name_inst ar n) (Red.TName.Real n))
              in
              let vs = List.map (fun tv -> tag ar tn (VR.Version.Orig tv)) vs in
              Hashtbl.replace st.real_vers n vs;
              vs)
        | VR.Name.Orig Red.TName.Root ->
            [ { PVersion.avoid = false; v = VR.Version.Orig Red.TVer.UnitV } ]
        | VR.Name.Var x ->
            [
              { PVersion.avoid = false; v = VR.Version.VarVal (Red.pin rho x) };
            ]
        | _ -> ( try Hashtbl.find st.gadget_vers tn with Not_found -> [])
      in
      let deps_cache = Hashtbl.create 65536 in
      let nq = ref 0 in
      let dependencies (tn : VR.Name.t) ({ PVersion.v = tv; _ } : PVersion.t) =
        incr nq;
        if verbose && !nq mod 10000 = 0 then
          Printf.eprintf "[q%d] %.1fs\n%!" !nq (Sys.time ());
        timed @@ fun () ->
        try Hashtbl.find deps_cache (tn, tv)
        with Not_found ->
          let r =
            (match (tn, tv) with
            | VR.Name.Orig Red.TName.Root, _ ->
                process st Red.rootPkg (root_inst ar goal)
            | VR.Name.Orig (Red.TName.Real n), VR.Version.Orig (Red.TVer.RV v)
              ->
                process st
                  (Red.TName.Real n, Red.TVer.RV v)
                  (inst_for ar (n, v))
            | _ -> ());
            let hs =
              try Hashtbl.find st.edges (tn, tv)
              with Not_found -> T.DependeesSet.empty
            in
            List.map
              (fun ((m, vs) : T.Dependees.t) ->
                ( intern st m,
                  PG.Ranges.of_list (List.map (tag ar m) (T.VSet.elements vs))
                ))
              (T.DependeesSet.elements hs)
          in
          Hashtbl.replace deps_cache (tn, tv) r;
          r
      in
      let goal_range = PG.Ranges.of_list (versions (fst root_q)) in
      let t0 = Unix.gettimeofday () in
      let result =
        PG.solve ~versions ~dependencies [ (fst root_q, goal_range) ]
      in
      if verbose then begin
        let total = Unix.gettimeofday () -. t0 in
        Printf.eprintf
          "PG.solve %.2fs: %.2fs in callbacks (%d dependencies queries, %d \
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
           reduction composes: the core solution decodes to the variable
           formula's packages, and those to opam's.  Reading the reals off
           the solution here instead would be a third, unproved, decoder --
           and it is what the soundness theorem is stated about. *)
          let core =
            T.PkgSet.ofList
              (List.map
                 (fun ((tn, { PVersion.v = tv; _ }) : VR.Name.t * PVersion.t) ->
                   (tn, tv))
                 sol)
          in
          let reals =
            Op.PkgSet.elements (Red.decodeS (VR.variableFormulaResolution core))
          in
          let reals = List.sort compare reals in
          Some (reals, List.length sol, depexts_of ar reals)
    in
    attempt ()
end
