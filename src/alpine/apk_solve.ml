(* Alpine solving over the verified pipeline, opam_solve/deb_solve-style:
   the APKINDEX lives in hashtables; every lookup is answered from a small
   Inst sub-instance in the shape one of Alpine.v's four lookup theorems
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

let rec nat_int (n : E.nat) : int =
  match n with E.O -> 0 | E.S k -> 1 + nat_int k

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

(* Which condition a rule designates is free, and is a performance
   choice: the rule is materialised only once that condition is selected.
   Alpine writes the switch name (docs, openrc) first and nothing depends
   on those, where CondSet.choose's alphabetical pick lands on a name most
   of the archive carries -- so the first-listed atom is recorded as the
   set is built, keyed by the element list, which is canonical where the
   set's own representation need not be.  The fallback keeps designation total,
   discharging designation_spec: a TCB obligation here, as ApkVerMatch's
   prefix/hash are. *)
let designation_tbl : (Alp.Atom.t list, Alp.Atom.t) Hashtbl.t =
  Hashtbl.create 4096

module FirstDesignation = struct
  let designation (conds : Alp.CondSet.t) : Alp.Atom.t option =
    match Hashtbl.find_opt designation_tbl (Alp.CondSet.elements conds) with
    | Some _ as a -> a
    | None -> Alp.CondSet.choose conds
end

module Red = Alp.Reduct (FirstDesignation)
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

(* provider_priority is apk's preference among the providers of a name,
   versioned ones included, and preference in this pipeline lives in
   PVersion.compare, which is where it is applied -- off the archive, not
   off an instance.
   The calculus records it in inst_prio precisely because it does not
   constrain which sets are resolutions, so the sub-instances below leave
   inst_prio empty and no resolution turns on a k: line. *)

(* replaces (r:/q:) never appears in a repository index -- it is an
   installed-db field -- so inst_repl is empty. *)

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

(* building the set is also where the row's first-listed atom is offered
   to [FirstDesignation]; an earlier row keeps the designation when two rows
   share a set, so the table does not depend on when it is read *)
let condset_of ds =
  let atoms = List.map xatom ds in
  let cs = Alp.CondSet.ofList atoms in
  (match atoms with
  | a :: _ ->
      let key = Alp.CondSet.elements cs in
      if not (Hashtbl.mem designation_tbl key) then
        Hashtbl.add designation_tbl key a
  | [] -> ());
  cs

(* ---- archive ---------------------------------------------------------- *)

type iif_rule = {
  t_pkg : string * string;
  t_conds : Alp.CondSet.t;
  t_designation : Alp.Atom.t;
}

type archive = {
  by_name : (string, P.pkg list) Hashtbl.t;
  meta : (string * string, P.pkg) Hashtbl.t;
  (* provided name -> the rows claiming it *)
  providers : (string, ((string * string) * string option) list) Hashtbl.t;
  (* install-if rows by their designated condition's name: only a package
     bearing that name, or providing it, can carry the rule *)
  iif_by_cond : (string, iif_rule list) Hashtbl.t;
  prio : (string * string, int) Hashtbl.t;
  mutable n_pkgs : int;
  mutable n_provs : int;
  mutable n_iif : int;
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
      iif_by_cond = Hashtbl.create 1024;
      prio = Hashtbl.create 1024;
      n_pkgs = 0;
      n_provs = 0;
      n_iif = 0;
    }
  in
  let iifs = ref [] in
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
        ar.n_iif <- ar.n_iif + 1;
        (* a CondSet is positive-only, so a negated install_if condition
           cannot be represented; dropping the sign would invert it, so
           the whole rule is dropped and counted instead *)
        if List.exists (fun (d : P.dep) -> d.P.d_neg) p.P.install_if then
          P.reject ()
        else
          iifs := ((p.P.name, p.P.version), condset_of p.P.install_if) :: !iifs))
    pkgs;
  (* keyed only once every set has offered its designation, so the key a
     row is filed under is the one [attachDesignation] will ask about *)
  List.iter
    (fun (z, conds) ->
      match FirstDesignation.designation conds with
      | Some a ->
          push ar.iif_by_cond (fst a)
            { t_pkg = z; t_conds = conds; t_designation = a }
      | None -> ())
    (List.rev !iifs);
  ar

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

(* ---- sub-instances -----------------------------------------------------

   repoPreimage I ns keeps the repository rows at a name in ns together
   with the packages providing one of them; provPreimage I ns keeps the
   provide rows landing on a name in ns.  Both are built from the indexes
   rather than by filtering a whole-archive instance, which is the only
   reason a per-lookup sub-instance is cheap. *)

let empty_inst =
  {
    Alp.inst_repo = Alp.PkgSet.empty;
    inst_deps = Alp.Deps.empty;
    inst_prov = Alp.Prov.empty;
    inst_installIf = Alp.InstallIf.empty;
    inst_world = Alp.WSet.empty;
    inst_prio = Alp.Prio.empty;
    inst_repl = Alp.Repl.empty;
  }

let preimages_at ar (ns : string list) =
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
    (List.sort_uniq String.compare ns);
  (Alp.PkgSet.ofList !repo, Alp.Prov.ofList !prov)

(* Lookup.nameSubInst *)
let name_inst ar (n : string) : Alp.coq_Inst =
  let repo, prov = preimages_at ar [ n ] in
  { empty_inst with Alp.inst_repo = repo; inst_prov = prov }

(* Lookup.installIfFibre: of the rows designating a name this package
   bears or provides, the ones whose designated condition it actually
   satisfies.  attachAt reads the package itself and the provide rows it
   heads and nothing else, so deciding it against an instance carrying
   just those rows is the whole archive's answer (attachAt_subInst). *)
let rows_at ar ((n, v) : string * string) (own : Alp.Prov.t) : iif_rule list =
  let inst = { empty_inst with Alp.inst_prov = own } in
  let at m =
    match Hashtbl.find_opt ar.iif_by_cond m with Some l -> l | None -> []
  in
  let cands =
    List.fold_left
      (fun acc ((_, (m, _)) : Alp.ProvElt.t) -> List.rev_append (at m) acc)
      (at n) (Alp.Prov.elements own)
  in
  List.filter (fun r -> Red.attachAt inst (n, v) r.t_designation) cands

(* Lookup.pkgSubInst: the package's own dependency, provide and install-if
   rows, and the repository at the names those dependencies mention --
   together with, per install-if rule the package carries, the rule's
   declaring name and the names of the conditions it did not designate *)
let pkg_inst ar ((n, v) : string * string) : Alp.coq_Inst =
  match Hashtbl.find_opt ar.meta (n, v) with
  | None -> empty_inst
  | Some m ->
      let own =
        Alp.Prov.ofList
          (List.filter_map
             (fun (pr : P.prov) ->
               if auto_selectable ar (n, v) pr.P.p_ver then
                 Some ((n, v), (pr.P.p_name, ptag pr.P.p_ver))
               else None)
             m.P.provides)
      in
      let rows = rows_at ar (n, v) own in
      let ns =
        List.fold_left
          (fun acc r ->
            fst r.t_pkg
            :: List.rev_append
                 (List.map fst (Alp.CondSet.elements (Red.condRest r.t_conds)))
                 acc)
          (List.map (fun (d : P.dep) -> d.P.d_name) m.P.depends)
          rows
      in
      let repo, prov = preimages_at ar ns in
      let deps =
        Alp.Deps.ofList (List.map (fun d -> ((n, v), xdep d)) m.P.depends)
      in
      {
        empty_inst with
        Alp.inst_repo = repo;
        inst_deps = deps;
        inst_prov = Alp.Prov.union prov own;
        inst_installIf =
          Alp.InstallIf.ofList (List.map (fun r -> (r.t_pkg, r.t_conds)) rows);
      }

(* Lookup.rootSubInst: the world set and the repository at the names it
   mentions.  Every install-if rule is carried by a package, so the root
   reads no part of the rule table. *)
let root_inst ar (world : P.dep list) : Alp.coq_Inst =
  let repo, prov =
    preimages_at ar (List.map (fun (d : P.dep) -> d.P.d_name) world)
  in
  {
    empty_inst with
    Alp.inst_repo = repo;
    inst_prov = prov;
    inst_world = Alp.WSet.ofList (List.map xdep world);
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

  (* NameOT is a UsualOrderedType, so a name compares Eq to itself; the
     pointer test only skips the walk on interned names (see [intern]),
     and leaves the order PubGrub sees exactly as NameOT gives it *)
  let compare a b = if a == b then 0 else r2c (PFR.NameOT.compare a b)

  let pp fmt (n : t) =
    match n with
    | PFR.Name.Orig m -> pp_alp_name fmt m
    | PFR.Name.Disjunct fs ->
        Format.fprintf fmt "<%a>"
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "|")
             (pp_formula 2))
          fs
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

(* encPos lists the unversioned providers of a name as a disjunction whose
   last alternative is the name's own versions, so every alternative but
   the last is a lone provider.  An install-if disjunction and a negated
   dependency both list FNeg alternatives, so an alternative naming a
   single package identifies a provider list. *)
let chain_head (f : PF.coq_Formula) : (string * string) option =
  match f with
  | PF.FDep (Red.Name.Orig m, vs) -> (
      match PF.VSet.elements vs with
      | [ Red.Version.Orig w ] -> Some (m, w)
      | _ -> None)
  | _ -> None

(* The alternative a synthetic version selects, and whether it is the last
   one -- the last alternative is the only one that is not a provider. *)
let rec alt_at (fs : PF.coq_Formula list) (i : E.nat) :
    (PF.coq_Formula * bool) option =
  match (fs, i) with
  | [ f ], E.O -> Some (f, true)
  | f :: _, E.O -> Some (f, false)
  | _ :: fs', E.S k -> alt_at fs' k
  | [], _ -> None

(* The rank of one alternative: a provider by its k: line, the last
   alternative -- the name's own versions -- above every provider. *)
let alt_rank ar (last : bool) (f : PF.coq_Formula) : int =
  if last then
    match f with
    | PF.FDep (_, vs) ->
        if PF.VSet.elements vs = [] then rank_none else rank_pkg
    | _ -> rank_none
  else match chain_head f with Some q -> prov_rank ar q | None -> rank_none

(* PubGrub decides the compare-maximum candidate, so preference lives
   here.  Newest-first among a name's own versions falls out of the
   encoded order, since V.compare is the apk order.  Two choices are
   made on top of it.

   A real package of a name beats an alias claiming it, which is apk's
   own preference.  Among the aliases themselves provider_priority
   decides, the versioned ones included: apk-package(5) reserves only
   automatic selection for the unversioned case, not the ranking.

   A synthetic version selects one alternative of its disjunction by
   position, and which alternative is wanted depends on the disjunction.
   installIfForm lists the negated install_if conditions first and the
   augmented package last, so preferring the earliest alternative is
   apk's rule that an install-if fires only when its conditions already hold
   -- without it every install_if row in the index is discharged by
   installing its target.  encPos lists the unversioned providers of a
   name first and its own versions last, and apk ranks those by
   provider_priority with a package of the name itself above all of them.

   The rank is carried on the version rather than read off it: which
   disjunction a position belongs to is what decides, and a comparator
   sees two versions and not their name.  Every version PubGrub holds is
   handed to it by [versions] or by a dependency range, both of which
   know the name, so both tag as they go and the rank is a function of
   the (name, version) pair -- keeping this a total order, and one
   consistent with the tags on any range the same name is compared
   against.  Ranks order a disjunction's alternatives against each other
   and break no other tie, so the versions of a name that has no provider
   disjunction are unaffected; an untagged disjunction leaves every
   alternative at rank 0, where the earliest one wins. *)
module PVersion = struct
  type t = { rank : int; v : PFR.Version.t }

  let pp fmt ({ v; _ } : t) =
    match v with
    | PFR.Version.Orig Red.Version.RootV -> Format.fprintf fmt "()"
    | PFR.Version.Orig (Red.Version.Orig s) -> Format.fprintf fmt "%s" s
    | PFR.Version.Orig (Red.Version.Prov ((n, w), pv)) ->
        Format.fprintf fmt "%s=%s(%s-%s)" "provided" pv n w
    | PFR.Version.Idx i -> Format.fprintf fmt "%d" (nat_int i)

  let compare a b =
    match (a.v, b.v) with
    | ( PFR.Version.Orig (Red.Version.Orig _),
        PFR.Version.Orig (Red.Version.Prov _) ) ->
        1
    | ( PFR.Version.Orig (Red.Version.Prov _),
        PFR.Version.Orig (Red.Version.Orig _) ) ->
        -1
    | ( PFR.Version.Orig (Red.Version.Prov _),
        PFR.Version.Orig (Red.Version.Prov _) ) ->
        let c = Stdlib.compare a.rank b.rank in
        if c <> 0 then c else r2c (PFR.VersionOT.compare a.v b.v)
    | PFR.Version.Idx _, PFR.Version.Idx _ ->
        let c = Stdlib.compare a.rank b.rank in
        if c <> 0 then c else -r2c (PFR.VersionOT.compare a.v b.v)
    | _ ->
        let c = r2c (PFR.VersionOT.compare a.v b.v) in
        if c <> 0 then c else Stdlib.compare a.rank b.rank
end

let tag ar (tn : PFR.Name.t) (tv : PFR.Version.t) : PVersion.t =
  match (tn, tv) with
  | PFR.Name.Disjunct (f0 :: _ as fs), PFR.Version.Idx i
    when chain_head f0 <> None -> (
      match alt_at fs i with
      | None -> { PVersion.rank = 0; v = tv }
      | Some (f, last) -> { PVersion.rank = alt_rank ar last f; v = tv })
  (* a versioned provides is auto-selected with or without a k:, so a
     missing one is apk's default of 0 and not [rank_unranked] *)
  | _, PFR.Version.Orig (Red.Version.Prov (q, _)) ->
      let rank =
        match Hashtbl.find_opt ar.prio q with Some k -> k | None -> 0
      in
      { PVersion.rank; v = tv }
  | _ -> { PVersion.rank = 0; v = tv }

module PG = Pubgrub.Make (PName) (PVersion)

let greatest = function
  | [] -> invalid_arg "greatest"
  | c :: cs ->
      List.fold_left (fun a b -> if PVersion.compare b a > 0 then b else a) c cs

(* only installIfForm's disjuncts open on FNeg: encDep negates whole
   formulas *)
let is_install_if (tn : PFR.Name.t) =
  match tn with PFR.Name.Disjunct (PF.FNeg _ :: _) -> true | _ -> false

let carried_at ~assigned tn tvs =
  match assigned tn with
  | PG.Unselected -> false
  | PG.Decided u -> List.exists (fun v -> PVersion.compare u v = 0) tvs
  | PG.Entailed r -> List.exists (fun v -> PG.Ranges.contains v r) tvs

let rec neg_leaves ar (f : PF.coq_Formula) : (PFR.Name.t * PVersion.t list) list
    =
  match f with
  | PF.FDep (m, vs) ->
      let tn = PFR.Name.Orig m in
      [
        ( tn,
          List.map
            (fun w -> tag ar tn (PFR.Version.Orig w))
            (PF.VSet.elements vs) );
      ]
  | PF.FDisj (a, b) | PF.FConj (a, b) -> neg_leaves ar a @ neg_leaves ar b
  | PF.FNeg _ -> []

(* apk never asserts a condition package absent: it installs the
   augmented package when all the conditions hold and otherwise does
   nothing at all.  PubGrub has to decide the disjunct either way, so the
   nearest thing is to discharge it on a condition the solution does not
   carry -- free, constraining nothing -- and to take the augmented
   package only when it carries them all. *)
let choose ar ~assigned (tn : PFR.Name.t) (cands : PVersion.t list) =
  match tn with
  | PFR.Name.Disjunct fs when is_install_if tn -> (
      let free = ref [] and pos = ref [] in
      List.iter
        (fun (pv : PVersion.t) ->
          match pv.PVersion.v with
          | PFR.Version.Idx i -> (
              match alt_at fs i with
              | Some (PF.FNeg f, _) ->
                  if
                    not
                      (List.exists
                         (fun (m, tvs) -> carried_at ~assigned m tvs)
                         (neg_leaves ar f))
                  then free := pv :: !free
              | Some (f, last) -> pos := (alt_rank ar last f, pv) :: !pos
              | None -> ())
          | _ -> ())
        cands;
      match !free with
      | _ :: _ as free -> greatest free
      | [] -> (
          match !pos with
          | [] -> greatest cands
          | p :: ps ->
              snd
                (List.fold_left
                   (fun ((ra, a) as best) ((rb, b) as cand) ->
                     if rb > ra || (rb = ra && PVersion.compare b a > 0) then
                       cand
                     else best)
                   p ps)))
  | _ -> greatest cands

(* An install-if disjunct exists only once its designated condition has
   been selected, so the conditions it discharges on have largely settled
   by the time [choose] sees it.  Deferring it behind every other open
   name settles the rest of them; measured on this index the deferral no
   longer changes the answer, but it is the invariant [choose] wants and
   it costs nothing. *)
let next ~assigned:_ (opens : (PFR.Name.t * int) list) =
  match List.find_opt (fun (tn, _) -> not (is_install_if tn)) opens with
  | Some (tn, _) -> tn
  | None -> fst (List.hd opens)

(* ---- the lazy core graph ----------------------------------------------- *)

module NameMap = Map.Make (struct
  type t = PFR.Name.t

  let compare a b = r2c (PFR.NameOT.compare a b)
end)

type state = {
  ar : archive;
  world : P.dep list;
  edges : (T.Pkg.t, T.DependeesSet.t) Hashtbl.t;
  synthetic_vers : (PFR.Name.t, PVersion.t list) Hashtbl.t;
  processed : (PF.Pkg.t, unit) Hashtbl.t;
  real_vers : (string, PVersion.t list) Hashtbl.t;
  mutable canon : PFR.Name.t NameMap.t;
  mutable n_proc : int;
}

let mk_state ar world =
  {
    ar;
    world;
    edges = Hashtbl.create 65536;
    synthetic_vers = Hashtbl.create 65536;
    processed = Hashtbl.create 16384;
    real_vers = Hashtbl.create 16384;
    canon = NameMap.empty;
    n_proc = 0;
  }

(* A Disjunct or NegDep name carries its formulas, so comparing
   two equal names walks both in full, and PubGrub does that on every
   dependency-list scan and map hit.  Each version's reduction builds its
   own copy of a synthetic name shared across versions; one representative
   per name lets PName.compare answer equality by pointer.  The map is
   keyed by NameOT itself, so which names unify is exactly NameOT
   equality and the order PubGrub sees -- [next]'s pick included -- is
   unchanged. *)
let intern st (m : PFR.Name.t) : PFR.Name.t =
  match NameMap.find_opt m st.canon with
  | Some c -> c
  | None ->
      st.canon <- NameMap.add m m st.canon;
      m

let verbose = Sys.getenv_opt "PACPROG" <> None

(* A package designated by many install-if rules carries one dependee per
   rule -- 1023 of them for docs -- so inserting them one at a time into
   a sorted-list set is quadratic: group by source first and build each
   source's set in a single pass. *)
let record_deprel st (d : T.DepRel.t) =
  let by_src = Hashtbl.create 64 in
  List.iter (fun ((s, h) : T.DepElt.t) -> push by_src s h) (T.DepRel.elements d);
  Hashtbl.iter
    (fun s hs ->
      let fresh = T.DependeesSet.ofList hs in
      Hashtbl.replace st.edges s
        (match Hashtbl.find_opt st.edges s with
        | Some prev -> T.DependeesSet.union prev fresh
        | None -> fresh))
    by_src

(* Only the synthetic names PackageFormula introduces are harvested; the Orig
   names are answered by versions_lookupName below. *)
let record_real st (r : T.PkgSet.t) =
  List.iter
    (fun ((tn, tv) : T.Pkg.t) ->
      match tn with
      | PFR.Name.Orig _ -> ()
      | _ ->
          let tv = tag st.ar tn tv in
          let prev =
            match Hashtbl.find_opt st.synthetic_vers tn with
            | Some x -> x
            | None -> []
          in
          if not (List.mem tv prev) then
            Hashtbl.replace st.synthetic_vers tn (tv :: prev))
    (T.PkgSet.elements r)

(* one Alpine package's dependee formulas, reduced to core edges *)
let process st (q : PF.Pkg.t) (inst : unit -> Alp.coq_Inst) =
  if not (Hashtbl.mem st.processed q) then begin
    Hashtbl.replace st.processed q ();
    st.n_proc <- st.n_proc + 1;
    if verbose && st.n_proc mod 500 = 0 then
      Printf.eprintf "[%d] %.1fs\n%!" st.n_proc (Sys.time ());
    let fs = Red.FSet.elements (Red.dependees (inst ()) q) in
    let d_q = PF.DepRel.ofList (List.map (fun f -> (q, f)) fs) in
    let r_q = PF.PkgSet.singleton q in
    record_deprel st (PFR.reduceDeps d_q);
    record_real st (PFR.reduceReal r_q d_q)
  end

let touch st ((tn, tv) : T.Pkg.t) =
  match (tn, tv) with
  | PFR.Name.Orig Red.Name.Root, PFR.Version.Orig Red.Version.RootV ->
      (* Lookup.dependees_lookupRoot *)
      process st Red.rootPkg (fun () -> root_inst st.ar st.world)
  | PFR.Name.Orig (Red.Name.Orig n), PFR.Version.Orig (Red.Version.Orig v) ->
      (* Lookup.dependees_lookupOrig *)
      process st (Red.Name.Orig n, Red.Version.Orig v) (fun () ->
          pkg_inst st.ar (n, v))
  | ( PFR.Name.Orig (Red.Name.Orig m),
      PFR.Version.Orig (Red.Version.Prov (q0, pv)) ) ->
      (* Lookup.dependees_lookupProv: an alias row reads no instance *)
      process st
        (Red.Name.Orig m, Red.Version.Prov (q0, pv))
        (fun () -> empty_inst)
  | _ ->
      (* a synthetic package's edges were harvested when its owner was
         processed *)
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
      match Hashtbl.find_opt st.synthetic_vers tn with
      | Some vs -> vs
      | None -> [])

type result = { pkgs : (string * string) list; nodes : int; processed : int }

let solve ?(debug = false) (ar : archive) (world : P.dep list) : result option =
  Pubgrub.set_debug debug;
  let st = mk_state ar world in
  let versions n = versions st n in
  (* the decisive memoization: PubGrub asks for the same node's
     dependencies over and over during propagation *)
  let cache = Hashtbl.create 65536 in
  let dependencies n ({ PVersion.v = u; _ } : PVersion.t) =
    match Hashtbl.find_opt cache (n, u) with
    | Some r -> r
    | None ->
        touch st (n, u);
        let hs =
          match Hashtbl.find_opt st.edges (n, u) with
          | Some x -> x
          | None -> T.DependeesSet.empty
        in
        let r =
          List.map
            (fun ((m, vs) : T.Dependees.t) ->
              let m = intern st m in
              (m, PG.Ranges.of_list (List.map (tag ar m) (T.VSet.elements vs))))
            (T.DependeesSet.elements hs)
        in
        Hashtbl.replace cache (n, u) r;
        r
  in
  let root = PFR.Name.Orig Red.Name.Root in
  let root_range = PG.Ranges.of_list (versions root) in
  match
    PG.solve ~next ~choose:(choose ar) ~vers:versions ~deps:dependencies
      [ (root, root_range) ]
  with
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
