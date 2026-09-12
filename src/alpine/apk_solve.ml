(* Alpine solving over the verified pipeline, opam_solve/deb_solve-style:
   the APKINDEX lives in hashtables; every query is answered from a small
   Inst slice in the shape one of Alpine.v's four lookup theorems
   justifies, pushed through the Alpine encoder into PackageFormula and
   then through its proved reduction to Core; PubGrub solves the
   accumulated core graph lazily, and the solution comes back through
   packageFormulaResolution and alpineResolution.  Trusted here (TCB):
   the parser, the version comparator, the policy constants below, and
   the plumbing. *)

module E = Pac
module P = Apk_parse

let c2r c = if c < 0 then E.Lt else if c > 0 then E.Gt else E.Eq
let r2c = function E.Lt -> -1 | E.Eq -> 0 | E.Gt -> 1

module StringOT = struct
  type t = string

  let compare a b = c2r (String.compare a b)
  let eq_dec (a : string) b = String.equal a b
end

module AVerOT = struct
  type t = string

  let compare a b = c2r (Apk_version.compare a b)
  let eq_dec a b = Apk_version.compare a b = 0
end

(* ApkVerMatch: the two constraints V.compare cannot express.  Both take
   the candidate version first and the constraint's operand second. *)
module PM = struct
  let prefix v c = Apk_version.prefix_match v c
  let hash v c = Apk_version.hash_match v c
end

module Alp = E.Alpine (StringOT) (AVerOT) (PM)
module Red = Alp.Reduction
module PF = Red.PF
module PFR = PF.Reduction
module T = PFR.T

(* ---- policy ------------------------------------------------------------

   Each is a decision the calculus leaves to the frontend; none is forced
   by the theory. *)

(* The world is the demo's goal arguments and nothing else: this resolves
   from an empty root rather than from an existing /etc/apk/world. *)

(* Architecture is fixed by the index that was loaded.  A repository's
   APKINDEX is per-arch, so no A: filtering is applied and no
   cross-arch reasoning is possible here. *)

(* provider_priority is carried as data but not applied.  It is apk's
   preference among unversioned providers of a name, and preference in
   this pipeline lives in PVersion.compare; the calculus records it in
   inst_prio precisely because it does not constrain which sets are
   resolutions.  The slices below leave inst_prio empty for that reason. *)

(* replaces (r:/q:) never appears in a repository index -- it is an
   installed-db field -- so inst_repl is empty. *)

(* ---- archive ---------------------------------------------------------- *)

type archive = {
  by_name : (string, P.pkg list) Hashtbl.t;
  meta : (string * string, P.pkg) Hashtbl.t;
  (* provided name -> the rows claiming it *)
  providers : (string, ((string * string) * string option) list) Hashtbl.t;
  trigs : (P.pkg * P.dep list) list;
  prio : (string * string, int) Hashtbl.t;
  mutable n_pkgs : int;
  mutable n_provs : int;
  mutable n_trigs : int;
}

let push tbl k v =
  let prev = match Hashtbl.find_opt tbl k with Some l -> l | None -> [] in
  Hashtbl.replace tbl k (v :: prev)

let load_index (path : string) : archive =
  let pkgs = P.parse_file path in
  let ar =
    {
      by_name = Hashtbl.create 16384;
      meta = Hashtbl.create 16384;
      providers = Hashtbl.create 16384;
      trigs = [];
      prio = Hashtbl.create 1024;
      n_pkgs = 0;
      n_provs = 0;
      n_trigs = 0;
    }
  in
  let trigs = ref [] in
  List.iter
    (fun (p : P.pkg) ->
      push ar.by_name p.P.name p;
      Hashtbl.replace ar.meta (p.P.name, p.P.version) p;
      ar.n_pkgs <- ar.n_pkgs + 1;
      List.iter
        (fun (pr : P.prov) ->
          push ar.providers pr.P.p_name ((p.P.name, p.P.version), pr.P.p_ver);
          ar.n_provs <- ar.n_provs + 1)
        p.P.provides;
      (match p.P.priority with
      | Some k -> Hashtbl.replace ar.prio (p.P.name, p.P.version) k
      | None -> ());
      if p.P.install_if <> [] then (
        trigs := (p, p.P.install_if) :: !trigs;
        ar.n_trigs <- ar.n_trigs + 1))
    pkgs;
  { ar with trigs = List.rev !trigs }

let versions_of ar n =
  match Hashtbl.find_opt ar.by_name n with Some l -> l | None -> []

let providers_of ar n =
  match Hashtbl.find_opt ar.providers n with Some l -> l | None -> []

(* ---- encoding into the calculus ---------------------------------------- *)

let xconstr (c : P.constr) : Alp.coq_Constr =
  match c with
  | P.Any -> Alp.CAny
  | P.Op (Apk_version.Eq, v) -> Alp.COp (E.OpEq, v)
  | P.Op (Apk_version.Lt, v) -> Alp.COp (E.OpLt, v)
  | P.Op (Apk_version.Gt, v) -> Alp.COp (E.OpGt, v)
  | P.Op (Apk_version.Le, v) -> Alp.COp (E.OpLe, v)
  | P.Op (Apk_version.Ge, v) -> Alp.COp (E.OpGe, v)
  | P.Op (Apk_version.Fuzzy, v) -> Alp.CPrefix v
  | P.Op (Apk_version.Gt_fuzzy, v) -> Alp.CGtPrefix v
  | P.Op (Apk_version.Lt_fuzzy, v) -> Alp.CLtPrefix v
  | P.Op (Apk_version.Hash, v) -> Alp.CHash v

let xatom (d : P.dep) : Alp.Atom.t = (d.P.d_name, xconstr d.P.d_constr)

let xdep (d : P.dep) : Alp.coq_Dep =
  if d.P.d_neg then Alp.DNeg (xatom d) else Alp.DPos (xatom d)

let ptag (v : string option) : Alp.coq_PTag =
  match v with Some pv -> Alp.PVer pv | None -> Alp.PVirt

let condset_of ds = Alp.CondSet.ofList (List.map xatom ds)

(* ---- slices ------------------------------------------------------------

   repoSlice I ns keeps the repository rows at a name in ns together with
   the packages providing one of them; provSlice I ns keeps the provide
   rows landing on a name in ns.  Both are built from the indexes rather
   than by filtering a whole-archive instance, which is the only reason a
   per-query slice is cheap. *)

let empty_inst =
  {
    Alp.inst_repo = Alp.PkgSet.empty;
    inst_deps = Alp.Deps.empty;
    inst_prov = Alp.Prov.empty;
    inst_trig = Alp.Trig.empty;
    inst_world = Alp.WSet.empty;
    inst_prio = Alp.Prio.empty;
    inst_repl = Alp.Repl.empty;
  }

let slice_at ar (names : string list) =
  let repo = ref [] and prov = ref [] in
  List.iter
    (fun n ->
      List.iter
        (fun (p : P.pkg) -> repo := (p.P.name, p.P.version) :: !repo)
        (versions_of ar n);
      List.iter
        (fun (owner, pv) ->
          repo := owner :: !repo;
          prov := (owner, (n, ptag pv)) :: !prov)
        (providers_of ar n))
    (List.sort_uniq String.compare names);
  (Alp.PkgSet.ofList !repo, Alp.Prov.ofList !prov)

(* Lookup.nameSlice *)
let name_inst ar (n : string) : Alp.coq_Inst =
  let repo, prov = slice_at ar [ n ] in
  { empty_inst with Alp.inst_repo = repo; inst_prov = prov }

(* Lookup.pkgSlice: the package's own dependency and provide rows, and
   the repository at the names those dependencies mention *)
let pkg_inst ar ((n, v) : string * string) : Alp.coq_Inst =
  match Hashtbl.find_opt ar.meta (n, v) with
  | None -> empty_inst
  | Some m ->
      let ns = List.map (fun (d : P.dep) -> d.P.d_name) m.P.depends in
      let repo, prov = slice_at ar ns in
      let deps =
        Alp.Deps.ofList (List.map (fun d -> ((n, v), xdep d)) m.P.depends)
      in
      let prov =
        Alp.Prov.union prov
          (Alp.Prov.ofList
             (List.map
                (fun (pr : P.prov) -> ((n, v), (pr.P.p_name, ptag pr.P.p_ver)))
                m.P.provides))
      in
      {
        empty_inst with
        Alp.inst_repo = repo;
        inst_deps = deps;
        inst_prov = prov;
      }

(* Lookup.rootSlice: the whole world set and the whole trigger table, and
   the repository at rootNames -- every name they mention *)
let root_inst ar (world : P.dep list) : Alp.coq_Inst =
  let ns = ref (List.map (fun (d : P.dep) -> d.P.d_name) world) in
  List.iter
    (fun ((p : P.pkg), conds) ->
      ns := p.P.name :: !ns;
      List.iter (fun (d : P.dep) -> ns := d.P.d_name :: !ns) conds)
    ar.trigs;
  let repo, prov = slice_at ar !ns in
  let trig =
    Alp.Trig.ofList
      (List.filter_map
         (fun ((p : P.pkg), conds) ->
           (* a CondSet is positive-only, so a negated install_if condition
              cannot be represented; dropping the sign would invert it, so the
              whole trigger is dropped and counted instead *)
           if List.exists (fun (d : P.dep) -> d.P.d_neg) conds then (
             P.reject ();
             None)
           else Some ((p.P.name, p.P.version), condset_of conds))
         ar.trigs)
  in
  let wset = Alp.WSet.ofList (List.map xdep world) in
  {
    empty_inst with
    Alp.inst_repo = repo;
    inst_prov = prov;
    inst_trig = trig;
    inst_world = wset;
  }

(* ---- the lazy core graph ----------------------------------------------- *)

type state = {
  ar : archive;
  world : P.dep list;
  edges : (T.Pkg.t, T.DependeesSet.t) Hashtbl.t;
  gadget_vers : (PFR.Name.t, PFR.Version.t list) Hashtbl.t;
  processed : (PF.Pkg.t, unit) Hashtbl.t;
  real_vers : (string, PFR.Version.t list) Hashtbl.t;
  mutable n_proc : int;
}

let mk_state ar world =
  {
    ar;
    world;
    edges = Hashtbl.create 65536;
    gadget_vers = Hashtbl.create 65536;
    processed = Hashtbl.create 16384;
    real_vers = Hashtbl.create 16384;
    n_proc = 0;
  }

let verbose = Sys.getenv_opt "PACPROG" <> None

let record_deprel st (d : T.DepRel.t) =
  List.iter
    (fun ((s, h) : T.DepElt.t) ->
      let prev =
        match Hashtbl.find_opt st.edges s with
        | Some x -> x
        | None -> T.DependeesSet.empty
      in
      Hashtbl.replace st.edges s (T.DependeesSet.add h prev))
    (T.DepRel.elements d)

(* Only the gadget names PackageFormula mints are harvested; the Orig
   names are answered by versions_lookupName below. *)
let record_real st (r : T.PkgSet.t) =
  List.iter
    (fun ((tn, tv) : T.Pkg.t) ->
      match tn with
      | PFR.Name.Orig _ -> ()
      | _ ->
          let prev =
            match Hashtbl.find_opt st.gadget_vers tn with
            | Some x -> x
            | None -> []
          in
          if not (List.mem tv prev) then
            Hashtbl.replace st.gadget_vers tn (tv :: prev))
    (T.PkgSet.elements r)

(* one Alpine package's dependee formulas, reduced to core edges *)
let process st (q : PF.Pkg.t) (inst : Alp.coq_Inst) =
  if not (Hashtbl.mem st.processed q) then begin
    Hashtbl.replace st.processed q ();
    st.n_proc <- st.n_proc + 1;
    if verbose && st.n_proc mod 500 = 0 then
      Printf.eprintf "[%d] %.1fs\n%!" st.n_proc (Sys.time ());
    let forms = Red.dependees inst q in
    let d_q =
      PF.DepRel.ofList (List.map (fun f -> (q, f)) (Red.FSet.elements forms))
    in
    let r_q = PF.PkgSet.singleton q in
    record_deprel st (PFR.reduceDeps d_q);
    record_real st (PFR.reduceReal r_q d_q)
  end

let touch st ((tn, tv) : T.Pkg.t) =
  match (tn, tv) with
  | PFR.Name.Orig Red.Name.Root, PFR.Version.Orig Red.Version.RootV ->
      (* Lookup.dependees_lookupRoot *)
      process st Red.rootPkg (root_inst st.ar st.world)
  | PFR.Name.Orig (Red.Name.Orig n), PFR.Version.Orig (Red.Version.Orig v) ->
      (* Lookup.dependees_lookupOrig *)
      process st (Red.Name.Orig n, Red.Version.Orig v) (pkg_inst st.ar (n, v))
  | ( PFR.Name.Orig (Red.Name.Orig m),
      PFR.Version.Orig (Red.Version.Prov (q0, pv)) ) ->
      (* Lookup.dependees_lookupProv: an alias row reads no instance *)
      process st (Red.Name.Orig m, Red.Version.Prov (q0, pv)) empty_inst
  | _ ->
      (* a gadget's edges were harvested when its owner was processed *)
      ()

let versions st (tn : PFR.Name.t) : PFR.Version.t list =
  match tn with
  | PFR.Name.Orig Red.Name.Root -> [ PFR.Version.Orig Red.Version.RootV ]
  | PFR.Name.Orig (Red.Name.Orig n) -> (
      match Hashtbl.find_opt st.real_vers n with
      | Some vs -> vs
      | None ->
          (* Lookup.versions_lookupName *)
          let vs =
            List.map
              (fun w -> PFR.Version.Orig w)
              (PF.VSet.elements (Red.versions (name_inst st.ar n) n))
          in
          Hashtbl.replace st.real_vers n vs;
          vs)
  | _ -> (
      match Hashtbl.find_opt st.gadget_vers tn with Some vs -> vs | None -> [])

(* ---- PubGrub ----------------------------------------------------------- *)

let rec pp_formula depth fmt (f : PF.coq_Formula) =
  if depth <= 0 then Format.fprintf fmt "..."
  else
    match f with
    | PF.FDep (n, vs) ->
        Format.fprintf fmt "%a{%d}" pp_alp_name n
          (List.length (PF.VSet.elements vs))
    | PF.FConj (a, b) ->
        Format.fprintf fmt "(%a&%a)"
          (pp_formula (depth - 1))
          a
          (pp_formula (depth - 1))
          b
    | PF.FDisj (a, b) ->
        Format.fprintf fmt "(%a|%a)"
          (pp_formula (depth - 1))
          a
          (pp_formula (depth - 1))
          b
    | PF.FNeg a -> Format.fprintf fmt "!%a" (pp_formula (depth - 1)) a

and pp_alp_name fmt (n : Red.Name.name) =
  match n with
  | Red.Name.Root -> Format.fprintf fmt "@root"
  | Red.Name.Orig s -> Format.fprintf fmt "%s" s

module PName = struct
  type t = PFR.Name.t

  let compare a b = r2c (PFR.NameOT.compare a b)

  let pp fmt (n : t) =
    match n with
    | PFR.Name.Orig m -> pp_alp_name fmt m
    | PFR.Name.Disjunct (a, b) ->
        Format.fprintf fmt "<%a|%a>" (pp_formula 2) a (pp_formula 2) b
    | PFR.Name.NegDep (m, vs) ->
        Format.fprintf fmt "<!%a{%d}>" pp_alp_name m
          (List.length (PF.VSet.elements vs))
end

module PVersion = struct
  type t = PFR.Version.t

  let pp fmt (v : t) =
    match v with
    | PFR.Version.Orig Red.Version.RootV -> Format.fprintf fmt "()"
    | PFR.Version.Orig (Red.Version.Orig s) -> Format.fprintf fmt "%s" s
    | PFR.Version.Orig (Red.Version.Prov ((n, w), pv)) ->
        Format.fprintf fmt "%s=%s(%s-%s)" "provided" pv n w
    | PFR.Version.Zero -> Format.fprintf fmt "0"
    | PFR.Version.One -> Format.fprintf fmt "1"

  (* PubGrub decides the compare-maximum candidate, so preference lives
     here.  Newest-first among a name's own versions falls out of the
     encoded order, since V.compare is the apk order.  Two choices are
     made on top of it.

     A real package of a name beats an alias claiming it, which is apk's
     own preference and the reason provider_priority only ever arbitrates
     between unversioned providers.

     Zero selects a disjunction's left alternative and One its right, and
     the two encoded disjunctions want opposite branches.  trigForm nests
     the negated install_if conditions on the left and the triggered
     package last, so Zero is apk's rule that a trigger fires only when
     its conditions already hold -- without it every install_if row in
     the index is discharged by installing its target.  encPos nests the
     unversioned providers of a name on the left and its real packages
     last, so Zero takes the first such provider instead; in the loaded
     index exactly one name (rng-tools) has both an unversioned provider
     and a real package, so that is the only row where the two readings
     disagree.  A name-dependent preference is not expressible: PubGrub
     ranks candidates by this comparison alone. *)
  let compare a b =
    match (a, b) with
    | ( PFR.Version.Orig (Red.Version.Orig _),
        PFR.Version.Orig (Red.Version.Prov _) ) ->
        1
    | ( PFR.Version.Orig (Red.Version.Prov _),
        PFR.Version.Orig (Red.Version.Orig _) ) ->
        -1
    | PFR.Version.Zero, PFR.Version.One -> 1
    | PFR.Version.One, PFR.Version.Zero -> -1
    | _ -> r2c (PFR.VersionOT.compare a b)
end

module PG = Pubgrub.Make (PName) (PVersion)

type result = { pkgs : (string * string) list; nodes : int; processed : int }

let solve ?(debug = false) (ar : archive) (world : P.dep list) : result option =
  Pubgrub.set_debug debug;
  let st = mk_state ar world in
  let versions nm = versions st nm in
  (* the decisive memoization: PubGrub asks for the same node's
     dependencies over and over during propagation *)
  let cache = Hashtbl.create 65536 in
  let dependencies nm (u : PFR.Version.t) =
    match Hashtbl.find_opt cache (nm, u) with
    | Some r -> r
    | None ->
        touch st (nm, u);
        let hs =
          match Hashtbl.find_opt st.edges (nm, u) with
          | Some x -> x
          | None -> T.DependeesSet.empty
        in
        let r =
          List.map
            (fun ((m, vs) : T.Dependees.t) ->
              (m, PG.Ranges.of_list (T.VSet.elements vs)))
            (T.DependeesSet.elements hs)
        in
        Hashtbl.replace cache (nm, u) r;
        r
  in
  let root = PFR.Name.Orig Red.Name.Root in
  let root_range = PG.Ranges.of_list [ PFR.Version.Orig Red.Version.RootV ] in
  match PG.solve ~versions ~dependencies [ (root, root_range) ] with
  | Error inc ->
      Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
      None
  | Ok sol ->
      let s = T.PkgSet.ofList sol in
      (* back through the two proved decoders *)
      let s_pf = PFR.packageFormulaResolution s in
      let pkgs = Alp.PkgSet.elements (Red.alpineResolution s_pf) in
      Some
        {
          pkgs = List.sort compare pkgs;
          nodes = List.length sol;
          processed = st.n_proc;
        }

(* A goal argument is an /etc/apk/world line: a dependency atom. *)
let world_of_args (args : string list) : P.dep list =
  List.filter_map
    (fun a ->
      match P.parse_atom a with
      | Some d -> Some d
      | None ->
          Printf.eprintf "cannot parse goal %S\n%!" a;
          None)
    args
