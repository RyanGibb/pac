(* opam solving over the verified pipeline, deb_solve-style: the archive
   lives in hashtables; the extracted per-package/per-name lookups are
   called on sub-instances justified by Opam.dependees_lookup* /
   Opam.versions_lookup*, which evaluate every filter against [rho] as
   they run; each package's package-formula dependencies are then reduced
   to core edges by the extracted PackageFormula reduction on its own
   sub-instance -- a conflict included, which is the declarer's own edge
   on the conflicting name admitting absence;
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
     because every version handed to PubGrub is tagged with it, and
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

(* a package's declarations are read only through its name's load, so
   they are never taken from a name parsed in part *)
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

(* opam answers opam-version with its own version unless
   OPAMVAR_opam_version or a global or switch variable overrides it
   (opamPackageVar.ml resolve_switch_raw); the harness leaves opam's own
   and pins us to it instead.  Unasked, the value is the opam
   nix/flake.lock fixes, so that a run outside the harness answers about
   the same opam the recorded baselines did *)
let default_opam_version = "2.5.2"

(* There is no cone pass: the repository is uncovered as the solver asks
   for it, so each lookup theorem's sub-instance must be complete at the
   moment it answers.  That holds by construction for all but one
   lookup: versions reads the repository at one name and root_inst at the
   query's names, each of which load_name takes whole; inst_for reads (n, v)'s own dependency, conflict, depext and
   pin-depends declarations and the repository at declaredNames, the
   names those declarations mention, and loads every one of them;
   available filters ride along with the name they belong to; depexts_of
   reads the selected packages' own declarations.

   Conflict classes are the exception, and only on one side.  A package's
   class formulas are read off its own declarations, so inst_for stays
   local; what is a preimage is the class package's version list, which is
   every declarer of the class and which no declaration of any one
   package names.  A conflict or pin-depends is no exception: the
   package-formula reduction turns a negated atom into the declarer's own
   edge on the target's name, admitting every version the atom does not
   name and the absent version every name has (PF.Reduction.negVS), so
   nothing of who conflicts with a name is read when the name answers
   (PF.Reduction.Lookup.versions_lookupOrig).
   class_idx therefore holds the declarers among the names loaded so far
   and may grow at any point in the run.  Not memoising is enough here,
   where it would not have been under a pairwise encoding: the growing
   answer is a versions answer, and PubGrub re-asks a name for its
   versions at every assignment, whereas a node's dependency list is
   memoised in deps_cache and so fixed at its first ask.  So cls_inst rebuilds the sub-instance from
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
    ]

  (* what the caller asked for, which is all the valuation below needs
     beyond the fixed environment *)
  type request = {
    (* the query's names, which are the names the synthetic root depends
       on: a query is a set of names each with a set of acceptable
       versions, and the valuation reads only the names *)
    names : string list;
    with_test : bool;
    with_doc : bool;
    with_dev_setup : bool;
    opam_version : string;
  }

  (* [build] and [post] are true because opam builds what it installs and
     has no flag to say otherwise; [dev] and [pinned] are false because
     nothing here is pinned.

     with-test, with-doc and with-dev-setup are the three opam does have a
     flag for, and they are query-scoped rather than global: the variable
     is on for every name the synthetic root depends on and off
     everywhere else, which is why each package's with-test is its own
     variable here.  [OpamSwitchState.universe] (opamSwitchState.ml:971-974)
     takes the request's names and expands them back to every version of
     each, and [package_env_t] (opamSwitchState.ml:908-921) then reads
     with-test as [test && OpamPackage.Set.mem nv requested_allpkgs] -- so
     the scope is a set of names, not of versions and not a dependency
     cone.  [--with-test]'s own help text says the same: "This only
     affects packages listed on the command-line" (opamArg.ml:1476-1477). *)
  let rho (rq : request) : string -> string option =
    let globals = ("opam-version", rq.opam_version) :: globals in
    fun x ->
    match List.assoc_opt x globals with
    | Some v -> Some v
    | None -> (
        match String.index_opt x ':' with
        | None -> None
        | Some i -> (
            let local = String.sub x (i + 1) (String.length x - i - 1) in
            let owner = String.sub x 0 i in
            let requested b =
              Some
                (if b && List.exists (String.equal owner) rq.names then "true"
                 else "false")
            in
            match local with
            | "build" | "post" -> Some "true"
            | "with-test" -> requested rq.with_test
            | "with-doc" -> requested rq.with_doc
            | "with-dev-setup" -> requested rq.with_dev_setup
            | "dev" | "pinned" -> Some "false"
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
    let dep_fibre =
      match m.Opam_parse.depends with None -> [] | Some f -> [ (p, xoff f) ]
    in
    let cfl_fibre =
      List.map
        (fun (cn, (g, c)) -> (p, (cn, (xfilt g, xvc c))))
        m.Opam_parse.conflicts
    in
    (* only this package's own declarations: the class package carries the
       partners, so no partner's declarations are read here *)
    let cls_fibre = List.map (fun k -> ((n, v), k)) m.Opam_parse.classes in
    let dxt_fibre =
      List.map (fun (e, g) -> (p, (e, xfilt g))) m.Opam_parse.depexts
    in
    let pind_fibre =
      List.map (fun (nv, u) -> (p, (nv, u))) m.Opam_parse.pindeps
    in
    let declared_names =
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
    let repo, avl = repo_and_avail ar declared_names in
    {
      Op.inst_repo = repo;
      inst_dep = dep_fibre;
      inst_dpo = [];
      inst_cfl = cfl_fibre;
      inst_cls = clsrel_of cls_fibre;
      inst_avl = avl;
      inst_dxt = dxt_fibre;
      inst_pins = Op.PkgSet.empty;
      inst_pind = pind_fibre;
      inst_goal = dummy;
      inst_inv = dummy;
    }

  (* A query is realised as the synthetic root's dependencies: one atom per
     requested name, admitting the versions that name's constraint admits.
     The root's other conjunct is the switch invariant, which is empty here
     -- nothing is installed and nothing is pinned -- and an atom under a
     false guard is how an empty formula is spelled. *)
  let root_inst ar (query : (string * Opam_parse.vc) list) : Op.coq_Inst =
    let repo, avl = repo_and_avail ar (List.map fst query) in
    let goal =
      match List.map (fun (n, c) -> Op.OFAtom (n, Op.FlTrue, xvc c)) query with
      | [] -> dummy
      | a :: rest -> List.fold_left (fun f b -> Op.OFAnd (f, b)) a rest
    in
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
      inst_goal = goal;
      inst_inv = dummy;
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
     carrying exactly the selected packages' depext entries; depextsOf, not
     a traversal here, decides which filters fire. *)
  let depexts_of rho ar (reals : (string * string) list) : string list =
    let dxt_entries =
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
        inst_dxt = dxt_entries;
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
  end

  (* PubGrub decides the compare-maximum candidate, so preference lives
     here.  Newest-first among a name's own versions falls out of the
     encoded order, since V.compare is the opam order, and the absent
     version is the encoded order's greatest, so a name only a conflict
     reaches is left out rather than installed.  On top of it, a
     version flagged avoid-version or deprecated is a last resort rather
     than an impossibility, so it sits in a class below every unflagged
     version of its name and newest-first decides within each class --
     the order builtin-0install sorts a name's candidates in
     (opam_0install_cudf.ml:15-23), opam having marked a deprecated
     version avoid-version too (opamSwitchState.ml:886-895).

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
      | PFR.Version.Bot -> Format.fprintf fmt "⊥"
  end

  module PG = Pubgrub.Make (PName) (PVersion)

  let tag ar (tn : PFR.Name.t) (tv : PFR.Version.t) : PVersion.t =
    match (tn, tv) with
    | PFR.Name.Orig (Red.TName.Real n), PFR.Version.Orig (Red.TVer.RV v) ->
        { PVersion.avoid = avoided ar n v; v = tv }
    | _ -> { PVersion.avoid = false; v = tv }

  (* every original name's absent version *)
  let bot : PVersion.t = { PVersion.avoid = false; v = PFR.Version.Bot }

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
     its dependencies were written in is gone by the time the core graph holds
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
     dependees 0install's decider never reaches: a conflict is a
     `Restricts dependency it skips outright -- here an edge on a name the
     depends formula does not mention, so unranked -- and a conflict class
     is no role either: opam compiles it into CUDF conflicts
     (opamSwitchState.ml:835-878), which 0install skips as it does any
     other. *)
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
    match m with PFR.Name.Orig (Red.TName.Cls _) -> false | _ -> true

  type state = {
    ar : archive;
    edges : (PFR.Name.t * PFR.Version.t, T.DependeesSet.t) Hashtbl.t;
    synthetic_vers : (PFR.Name.t, PVersion.t list) Hashtbl.t;
    processed : (PF.Pkg.t, unit) Hashtbl.t;
    real_vers : (string, PVersion.t list) Hashtbl.t;
    (* the encoder's version oracle at a real name, as the versions
       lookup computes it and before tagging *)
    oracle : (string, PF.VSet.t) Hashtbl.t;
    mutable canon : PFR.Name.t NameMap.t;
  }

  let mk_state ar =
    {
      ar;
      edges = Hashtbl.create 65536;
      synthetic_vers = Hashtbl.create 65536;
      processed = Hashtbl.create 4096;
      real_vers = Hashtbl.create 4096;
      oracle = Hashtbl.create 4096;
      canon = NameMap.empty;
    }

  (* A Disjunct name carries its formulas, so comparing
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

  let verbose = Sys.getenv_opt "PACPROG" <> None
  let nproc = ref 0

  (* Op.versions_lookupReal / versions_lookupCls: what the versions
     callback answers, before the tagging PubGrub sees.  The encoder reads
     this at the names a formula negates
     (PF.Reduction.Lookup.dependees_lookupOrigBy), all of which inst_for
     has loaded. *)
  let oracle rho st (tn : Red.TName.t) : PF.VSet.t =
    match tn with
    | Red.TName.Real m -> (
        match Hashtbl.find_opt st.oracle m with
        | Some vs -> vs
        | None ->
            let vs = Red.versions rho (name_inst st.ar m) tn in
            Hashtbl.replace st.oracle m vs;
            vs)
    | Red.TName.Root -> PF.VSet.singleton Red.TVer.UnitV
    | Red.TName.Cls k -> Red.versions rho (cls_inst st.ar k) tn

  (* reduce one package-formula package's dependencies to core, via the
     extracted lookups *)
  let process rho st (q : PF.Pkg.t) (inst : Op.coq_Inst) =
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
      record_deprel st (PFR.reduceDepsBy (oracle rho st) d_q);
      record_real st (PFR.reduceReal r_q d_q)
    end

  let solve ?(debug = false) ?(zi_order = false) ?(with_test = false)
      ?(with_doc = false) ?(with_dev_setup = false)
      ?(opam_version = default_opam_version) ar
      (query : (string * Opam_parse.vc) list) =
    Pubgrub.set_debug debug;
    let rho =
      rho
        {
          names = List.map fst query;
          with_test;
          with_doc;
          with_dev_setup;
          opam_version;
        }
    in
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
    (* every original name answers its real versions and the absent one
       (PF.Reduction.Lookup.versions_lookupOrig), except the root, whose
       absent version the query rules out before the solve starts and
       whose presence in the list would only widen the ranges PubGrub
       prints for it *)
    let versions (tn : PFR.Name.t) : PVersion.t list =
      timed @@ fun () ->
      match tn with
      | PFR.Name.Orig (Red.TName.Real n) -> (
          try Hashtbl.find st.real_vers n
          with Not_found ->
            let vs = PF.VSet.elements (oracle rho st (Red.TName.Real n)) in
            let vs = List.map (fun tv -> tag ar tn (PFR.Version.Orig tv)) vs in
            let vs = vs @ [ bot ] in
            Hashtbl.replace st.real_vers n vs;
            vs)
      | PFR.Name.Orig Red.TName.Root ->
          [ { PVersion.avoid = false; v = PFR.Version.Orig Red.TVer.UnitV } ]
      (* The one name that cannot be held: its versions are the whole
         preimage of the class relation at k, so class_idx knows only the
         declarers among the names loaded so far.  Recomputing the handful
         of declarers at every ask lets a declarer parsed later simply be
         there, where a cache would freeze the answer mid-run. *)
      | PFR.Name.Orig (Red.TName.Cls k) ->
          List.map
            (fun tv -> tag ar tn (PFR.Version.Orig tv))
            (PF.VSet.elements
               (Red.versions rho (cls_inst ar k) (Red.TName.Cls k)))
          @ [ bot ]
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
              process rho st Red.rootPkg (root_inst ar query)
          | PFR.Name.Orig (Red.TName.Real n), PFR.Version.Orig (Red.TVer.RV v)
            ->
              process rho st
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
                PG.Ranges.of_list (List.map (tag ar m) (T.VSet.elements vs)) ))
            (T.DependeesSet.elements hs)
        in
        Hashtbl.replace deps_cache (tn, tv) r;
        r
    in
    (* the dependees of a decided package, in source order and without the
       synthetic packages 0install has no role for *)
    let order_cache = Hashtbl.create 4096 in
    (* opam's create_spec conses each atom onto the list 0install walks
       (opamBuiltin0install.ml:47-53, 65-67), so the query goes last first *)
    let query_index =
      let tbl = Hashtbl.create 16 in
      List.iteri
        (fun i (n, _) -> if not (Hashtbl.mem tbl n) then Hashtbl.add tbl n i)
        (List.rev query);
      tbl
    in
    let zi_deps (tn : PFR.Name.t) (pv : PVersion.t) : PFR.Name.t list =
      ignore (dependencies tn pv);
      let hs =
        try Hashtbl.find st.edges (tn, pv.PVersion.v)
        with Not_found -> T.DependeesSet.empty
      in
      (* 0install's decider walks requirements, not restrictions: a
         conflict's edge admits ⊥ and opens no role *)
      let ds =
        List.filter_map
          (fun (m, vs) ->
            if T.VSet.mem PFR.Version.Bot vs then None else Some m)
          (T.DependeesSet.elements hs)
      in
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
      (* the root's dependencies are the query, in the order opam hands
         it on *)
      | PFR.Name.Orig Red.TName.Root, _ ->
          let rank m =
            match zi_rank query_index m with Some i -> i | None -> max_int
          in
          List.filter zi_walkable ds
          |> List.stable_sort (fun a b -> compare (rank a) (rank b))
      (* a disjunct package carries the alternative it was decided to, and
         there is no written order to restore *)
      | _ -> List.filter zi_walkable ds
    in
    (* Absence is the greatest version but the last decision.  A name a
       conflict reaches is entailed to a range admitting ⊥ the moment its
       declarer is decided, and PubGrub's own order -- fewest candidates
       first -- would then decide it, to ⊥, before the packages that need
       it positively are decided, narrowing their ranges to the versions
       that do not (lwt 6.1.2 needs dune-configurator; dune's conflict on
       old dune-configurators had it decided absent first, and lwt fell to
       4.2.1).  So a name whose open range still admits ⊥ waits until every
       name that must be present is decided; by then either something needs
       it, and its range excludes ⊥, or nothing does, and ⊥ is right. *)
    let defer_bot ~assigned (open_names : (PFR.Name.t * int) list) =
      (* only an original name has the absent version; asking the partial
         solution about a disjunct would compare its formulas *)
      let admits_bot n =
        match n with
        | PFR.Name.Orig _ -> (
            match assigned n with
            | PG.Entailed r -> PG.Ranges.contains bot r
            | _ -> false)
        | _ -> false
      in
      match List.find_opt (fun (n, _) -> not (admits_bot n)) open_names with
      | Some (n, _) -> n
      | None -> fst (List.hd open_names)
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
        (* nothing on the walk is open: leave the solver's own choice,
           absence last *)
        defer_bot ~assigned open_names
      with Found n -> n
    in
    let next = Some (if zi_order then zi_next else defer_bot) in
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
        Some (reals, List.length sol, depexts_of rho ar reals)
end
