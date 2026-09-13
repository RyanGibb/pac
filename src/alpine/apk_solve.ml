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

(* provider_priority is apk's preference among the unversioned providers
   of a name, and preference in this pipeline lives in PVersion.compare,
   which is where it is applied -- off the archive, not off an instance.
   The calculus records it in inst_prio precisely because it does not
   constrain which sets are resolutions, so the slices below leave
   inst_prio empty and no resolution turns on a k: line. *)

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

(* apk-package(5): "By default a non-versioned provides will not be
   selected automatically for installation.  But specifying
   provider-priority enables this automatic selection".  So a bare
   provides without k: is not a low-ranked candidate, it is not a
   candidate: its row never enters the instance, which is an
   availability cut on the alias rather than on its owner -- the owner
   stays installable when the world names it directly. *)
let auto_selectable ar (owner : string * string) (pv : string option) =
  pv <> None || Hashtbl.mem ar.prio owner

let providers_of ar n =
  match Hashtbl.find_opt ar.providers n with
  | Some l -> List.filter (fun (owner, pv) -> auto_selectable ar owner pv) l
  | None -> []

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
             (List.filter_map
                (fun (pr : P.prov) ->
                  if auto_selectable ar (n, v) pr.P.p_ver then
                    Some ((n, v), (pr.P.p_name, ptag pr.P.p_ver))
                  else None)
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

(* The rank a provider disjunction's two branches are compared on: the
   k: line where a provider carries one, [rank_unranked] below all of
   them where it does not, since apk-package(5) says a provides without
   a provider-priority is not selected automatically at all and the
   nearest a preference can come to that is last place; [rank_pkg] for a
   package claiming the name with a version, above every provider; and
   [rank_none] for a branch that offers nothing. *)
let rank_pkg = max_int
let rank_unranked = -1
let rank_none = min_int

let prov_rank ar (q : string * string) : int =
  match Hashtbl.find_opt ar.prio q with Some k -> k | None -> rank_unranked

(* encPos nests the unversioned providers of a name into a right-leaning
   disjunction whose last alternative is the name's own versions, so one
   link's left branch is a lone provider and its right branch is every
   remaining alternative.  A trigger disjunction and a negated dependency
   both nest FNeg on the left, so a left branch naming a single package
   identifies a provider chain. *)
let chain_head (f : PF.coq_Formula) : (string * string) option =
  match f with
  | PF.FDep (Red.Name.Orig m, vs) -> (
      match PF.VSet.elements vs with
      | [ Red.Version.Orig w ] -> Some (m, w)
      | _ -> None)
  | _ -> None

let rec chain_rank ar (f : PF.coq_Formula) : int =
  match f with
  | PF.FDisj (a, b) -> (
      match chain_head a with
      | Some q -> max (prov_rank ar q) (chain_rank ar b)
      | None -> rank_none)
  | PF.FDep (_, vs) -> if PF.VSet.elements vs = [] then rank_none else rank_pkg
  | _ -> rank_none

(* PubGrub decides the compare-maximum candidate, so preference lives
   here.  Newest-first among a name's own versions falls out of the
   encoded order, since V.compare is the apk order.  Two choices are
   made on top of it.

   A real package of a name beats an alias claiming it, which is apk's
   own preference and the reason provider_priority only ever arbitrates
   between unversioned providers.

   Zero selects a disjunction's left alternative and One its right, and
   which branch is wanted depends on the disjunction.  trigForm nests the
   negated install_if conditions on the left and the triggered package
   last, so Zero is apk's rule that a trigger fires only when its
   conditions already hold -- without it every install_if row in the
   index is discharged by installing its target.  encPos nests the
   unversioned providers of a name on the left and its own versions last,
   so there Zero takes a provider and One defers to the rest, and apk
   ranks those by provider_priority with a package of the name itself
   above all of them.

   The rank is carried on the version rather than read off it: which
   disjunction a Zero belongs to is what decides, and a comparator sees
   two versions and not their name.  Every version PubGrub holds is
   handed to it by [versions] or by a dependency range, both of which
   know the name, so both tag as they go and the rank is a function of
   the (name, version) pair -- keeping this a total order, and one
   consistent with the tags on any range the same name is compared
   against.  Ranks order Zero against One and break no other tie, so the
   versions of a name that has no provider disjunction are unaffected. *)
module PVersion = struct
  type t = { rank : int; v : PFR.Version.t }

  let pp fmt ({ v; _ } : t) =
    match v with
    | PFR.Version.Orig Red.Version.RootV -> Format.fprintf fmt "()"
    | PFR.Version.Orig (Red.Version.Orig s) -> Format.fprintf fmt "%s" s
    | PFR.Version.Orig (Red.Version.Prov ((n, w), pv)) ->
        Format.fprintf fmt "%s=%s(%s-%s)" "provided" pv n w
    | PFR.Version.Zero -> Format.fprintf fmt "0"
    | PFR.Version.One -> Format.fprintf fmt "1"

  let compare a b =
    match (a.v, b.v) with
    | ( PFR.Version.Orig (Red.Version.Orig _),
        PFR.Version.Orig (Red.Version.Prov _) ) ->
        1
    | ( PFR.Version.Orig (Red.Version.Prov _),
        PFR.Version.Orig (Red.Version.Orig _) ) ->
        -1
    | PFR.Version.Zero, PFR.Version.One ->
        if a.rank = b.rank then 1 else Stdlib.compare a.rank b.rank
    | PFR.Version.One, PFR.Version.Zero ->
        if a.rank = b.rank then -1 else Stdlib.compare a.rank b.rank
    | _ ->
        let c = r2c (PFR.VersionOT.compare a.v b.v) in
        if c <> 0 then c else Stdlib.compare a.rank b.rank
end

let tag ar (tn : PFR.Name.t) (tv : PFR.Version.t) : PVersion.t =
  match (tn, tv) with
  | PFR.Name.Disjunct (a, b), (PFR.Version.Zero | PFR.Version.One) -> (
      match chain_head a with
      | None -> { PVersion.rank = 0; v = tv }
      | Some q ->
          let rank =
            match tv with
            | PFR.Version.Zero -> prov_rank ar q
            | _ -> chain_rank ar b
          in
          { PVersion.rank; v = tv })
  | _ -> { PVersion.rank = 0; v = tv }

module PG = Pubgrub.Make (PName) (PVersion)

(* ---- the lazy core graph ----------------------------------------------- *)

type state = {
  ar : archive;
  world : P.dep list;
  edges : (T.Pkg.t, T.DependeesSet.t) Hashtbl.t;
  gadget_vers : (PFR.Name.t, PVersion.t list) Hashtbl.t;
  processed : (PF.Pkg.t, unit) Hashtbl.t;
  real_vers : (string, PVersion.t list) Hashtbl.t;
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
          let tv = tag st.ar tn tv in
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

let versions st (tn : PFR.Name.t) : PVersion.t list =
  match tn with
  | PFR.Name.Orig Red.Name.Root ->
      [ tag st.ar tn (PFR.Version.Orig Red.Version.RootV) ]
  | PFR.Name.Orig (Red.Name.Orig n) -> (
      match Hashtbl.find_opt st.real_vers n with
      | Some vs -> vs
      | None ->
          (* Lookup.versions_lookupName *)
          let vs =
            List.map
              (fun w -> tag st.ar tn (PFR.Version.Orig w))
              (PF.VSet.elements (Red.versions (name_inst st.ar n) n))
          in
          Hashtbl.replace st.real_vers n vs;
          vs)
  | _ -> (
      match Hashtbl.find_opt st.gadget_vers tn with Some vs -> vs | None -> [])

type result = { pkgs : (string * string) list; nodes : int; processed : int }

let solve ?(debug = false) (ar : archive) (world : P.dep list) : result option =
  Pubgrub.set_debug debug;
  let st = mk_state ar world in
  let versions nm = versions st nm in
  (* the decisive memoization: PubGrub asks for the same node's
     dependencies over and over during propagation *)
  let cache = Hashtbl.create 65536 in
  let dependencies nm ({ PVersion.v = u; _ } : PVersion.t) =
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
              (m, PG.Ranges.of_list (List.map (tag ar m) (T.VSet.elements vs))))
            (T.DependeesSet.elements hs)
        in
        Hashtbl.replace cache (nm, u) r;
        r
  in
  let root = PFR.Name.Orig Red.Name.Root in
  let root_range = PG.Ranges.of_list (versions root) in
  match PG.solve ~versions ~dependencies [ (root, root_range) ] with
  | Error inc ->
      Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
      None
  | Ok sol ->
      let s =
        T.PkgSet.ofList (List.map (fun (m, { PVersion.v; _ }) -> (m, v)) sol)
      in
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
