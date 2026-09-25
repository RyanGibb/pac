(* Trusted here (TCB): the parser, the version comparator, the valuation
   defaults, and the plumbing. *)

module E = Pac

let c2r c = if c < 0 then E.Lt else if c > 0 then E.Gt else E.Eq
let r2c = function E.Eq -> 0 | E.Lt -> -1 | E.Gt -> 1

let rec nat_int (n : E.nat) : int =
  match n with E.O -> 0 | E.S k -> 1 + nat_int k

module SName = struct
  type t = string

  let compare a b = c2r (String.compare a b)
  let eq_dec (a : string) b = String.equal a b
end

module OVerOT = struct
  type t = string

  let compare a b = c2r (Opam_version.compare a b)
  let eq_dec a b = Opam_version.compare a b = 0
end

type archive = {
  root : string;
  pkgs : (string, (string * Opam_parse.pkg_meta) list) Hashtbl.t;
  (* class -> its members among the names loaded so far.  Unlike every
     other table here this one is a preimage and so grows as names load;
     see the note above [Op]. *)
  class_table : (string, (string * string) list) Hashtbl.t;
  (* the versions a name flags avoid-version or deprecated; a table
     because every version handed to PubGrub is tagged with it, and
     because all but a hundred or so names answer no *)
  avoid_table : (string, string list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  (* wall time inside the parser, which the solve now interleaves with *)
  mutable t_parse : float;
}

let empty_archive root =
  {
    root;
    pkgs = Hashtbl.create 4096;
    class_table = Hashtbl.create 64;
    avoid_table = Hashtbl.create 64;
    n_names = 0;
    n_vers = 0;
    t_parse = 0.;
  }

let class_members ar k =
  Option.value (Hashtbl.find_opt ar.class_table k) ~default:[]

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
      let listed = Sys.file_exists ndir && Sys.is_directory ndir in
      if listed then
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
                  with
                  | Parsing.Parse_error | OpamLexer.Error _ | Failure _
                  | Sys_error _
                  ->
                    Opam_parse.reject ())
            | _ -> ())
          (Sys.readdir ndir);
      let vs = !acc in
      Hashtbl.replace ar.pkgs name vs;
      if listed then ar.n_names <- ar.n_names + 1;
      ar.n_vers <- ar.n_vers + List.length vs;
      List.iter
        (fun (version, (m : Opam_parse.pkg_meta)) ->
          List.iter
            (fun k ->
              Hashtbl.replace ar.class_table k
                ((name, version) :: class_members ar k))
            m.classes;
          if m.avoid_version || m.deprecated then
            Hashtbl.replace ar.avoid_table name
              (version
              :: Option.value
                   (Hashtbl.find_opt ar.avoid_table name)
                   ~default:[]))
        vs;
      ar.t_parse <- ar.t_parse +. (Unix.gettimeofday () -. t);
      vs

let versions_of ar n = List.map fst (load_name ar n)

(* a package's declarations are read only through its name's load, so
   they are never taken from a name parsed in part *)
let meta_of ar n v =
  Option.value
    (List.assoc_opt v (load_name ar n))
    ~default:Opam_parse.empty_meta

(* loads, because the answer decides the class a version sorts into and
   the same version must sort the same way whether it is met in a name's
   candidate list or in a depender's range *)
let avoided ar n v =
  ignore (load_name ar n);
  match Hashtbl.find_opt ar.avoid_table n with
  | None -> false
  | Some vs -> List.exists (fun w -> Opam_version.equal w v) vs

(* opam answers opam-version with its own version unless
   OPAMVAR_opam_version or a global or switch variable overrides it
   (opamPackageVar.ml resolve_switch_raw); the harness leaves opam's own
   and pins us to it instead.  Unasked, the value is the opam
   nix/flake.lock fixes, so that a run outside the harness answers about
   the same opam the recorded baselines did *)
let default_opam_version = "2.5.2"

(* There is no cone pass: the repository is uncovered as the solver asks
   for it, so each lookup's sub-instance must be complete at the moment it
   answers.  That holds by construction for all but one lookup: versions
   and root_inst read names that load_name takes whole; inst_for reads
   (n, v)'s own declarations and the repository at the names they
   mention, and loads every one of them; depexts_of reads the selected
   packages' own declarations.

   Conflict classes are the exception: the class package's version list
   is every declarer of the class, which no declaration of any one
   package names.  A conflict or pin-depends is no exception: the
   reduction turns a negated atom into the declarer's own edge on the
   target's name, so nothing of who conflicts with a name is read when
   the name answers.  class_table therefore holds the declarers among the
   names loaded so far and may grow at any point in the run.  Not
   memoising is enough: the growing answer is a versions answer, which
   PubGrub re-asks at every assignment, whereas a node's dependency list
   is memoised and so fixed at its first ask.  A class
   version is also never asked for before its claimant's name has loaded,
   since the claim is that package's own edge. *)

module Op = E.Opam (SName) (OVerOT) (SName) (OVerOT) (SName)
module Red = Op.Reduction
module PF = Red.PF
module PFR = PF.Reduction
module T = PFR.T

let globals =
  [
    ("os", "linux");
    ("os-family", "debian");
    ("os-distribution", "debian");
    ("os-version", "12");
    ("arch", "x86_64");
  ]

type request = {
  (* the valuation reads only the query's names, not their versions *)
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

let empty_inst =
  {
    Op.inst_repo = Op.PkgSet.empty;
    inst_dep = [];
    inst_dpo = [];
    inst_cfl = [];
    inst_cls = Op.ClsRel.empty;
    inst_avl = [];
    inst_dxt = [];
    inst_pins = Op.PkgSet.empty;
    inst_pind = [];
    inst_goal = dummy;
    inst_inv = dummy;
  }

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
    let acc =
      match m.Opam_parse.depends with
      | None -> []
      | Some f -> Opam_parse.off_names [] f
    in
    let acc =
      List.fold_left (fun a (cn, _) -> cn :: a) acc m.Opam_parse.conflicts
    in
    List.fold_left (fun a ((pn, _), _) -> pn :: a) acc m.Opam_parse.pindeps
  in
  let repo, avl = repo_and_avail ar declared_names in
  {
    empty_inst with
    Op.inst_repo = repo;
    inst_dep = dep_fibre;
    inst_cfl = cfl_fibre;
    inst_cls = clsrel_of cls_fibre;
    inst_avl = avl;
    inst_dxt = dxt_fibre;
    inst_pind = pind_fibre;
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
  { empty_inst with Op.inst_repo = repo; inst_avl = avl; inst_goal = goal }

(* the class relation restricted to k, which is all the class package's
   version lookup reads.  Built from class_table at every ask and never
   held -- see the note above [Op]. *)
let cls_inst ar (k : string) : Op.coq_Inst =
  {
    empty_inst with
    Op.inst_cls = clsrel_of (List.map (fun q -> (q, k)) (class_members ar k));
  }

let name_inst ar (n : string) : Op.coq_Inst =
  let repo, avl = repo_and_avail ar [ n ] in
  { empty_inst with Op.inst_repo = repo; inst_avl = avl }

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
  Op.ESet.elements
    (Op.depextsOf rho
       { empty_inst with Op.inst_dxt = dxt_entries }
       (pkgset_of reals))

let pp_name fmt (n : PFR.Name.t) =
  match n with
  | PFR.Name.Orig Red.TName.Root -> Format.fprintf fmt "root"
  | PFR.Name.Orig (Red.TName.Real n) -> Format.fprintf fmt "%s" n
  | PFR.Name.Orig (Red.TName.Cls k) -> Format.fprintf fmt "conflict-class:%s" k
  | PFR.Name.Disjunct _ -> Format.fprintf fmt "<disj>"

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

  let v (x : t) = x.v
  let bot = { avoid = false; v = PFR.Version.Bot }

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

module L =
  Package_formula.Make (Red.TNOT) (Red.TVOT) (PF) (PVersion)
    (struct
      let pp_name = pp_name
    end)

module PG = L.PG

let tag ar (tn : PFR.Name.t) (tv : PFR.Version.t) : PVersion.t =
  match (tn, tv) with
  | PFR.Name.Orig (Red.TName.Real n), PFR.Version.Orig (Red.TVer.RV v) ->
      { PVersion.avoid = avoided ar n v; v = tv }
  | _ -> { PVersion.avoid = false; v = tv }

(* the encoder reads this at the names a formula negates, all of which
   inst_for has loaded; a class package's versions are its declarers
   among the names loaded so far, and so are never held *)
let oracle rho ar (tn : Red.TName.t) : PF.VSet.t =
  match tn with
  | Red.TName.Real m -> Red.versions rho (name_inst ar m) tn
  | Red.TName.Root -> PF.VSet.singleton Red.TVer.UnitV
  | Red.TName.Cls k -> Red.versions rho (cls_inst ar k) tn

let lookups rho ar : L.t =
  L.create ~root:(Red.TName.Root, Red.TVer.UnitV) ~tag:(tag ar)
    ~oracle:(oracle rho ar)
    ~volatile:(function Red.TName.Cls _ -> true | _ -> false)
    ()

let touch rho ar query st ((tn, tv) : T.Pkg.t) =
  let process q inst =
    L.process st q (fun () -> Red.FSet.elements (Red.dependees rho (inst ()) q))
  in
  match (tn, tv) with
  | PFR.Name.Orig Red.TName.Root, _ ->
      process Red.rootPkg (fun () -> root_inst ar query)
  | PFR.Name.Orig (Red.TName.Real n), PFR.Version.Orig (Red.TVer.RV v) ->
      process (Red.TName.Real n, Red.TVer.RV v) (fun () -> inst_for ar (n, v))
  | _ -> ()

