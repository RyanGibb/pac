module Ot = Pac_common.Ot
module Tbl = Pac_common.Tbl

module ApkVersionOT = Ot.Make (struct
  type t = string

  let compare = Apk_version.compare
end)

module PM = struct
  let prefix v c = Apk_version.prefix_match v c
  let hash v c = Apk_version.hash_match v c
end

module Alpine = Pac.Alpine (Ot.Str) (ApkVersionOT) (PM)

let first_pos (ds : Alpine.coq_Dep list) : Alpine.Atom.t option =
  List.find_map (function Alpine.DPos a -> Some a | Alpine.DNeg _ -> None) ds

type stats = {
  names : int;
  versions : int;
  provides : int;
  install_ifs : int;
  dropped : int;
}

module type S = sig
  module FirstDesignation : sig
    val designation : Alpine.ConditionSet.t -> Alpine.Atom.t option
  end

  module Reduction : module type of Alpine.ReductionUnder (FirstDesignation)
  module PackageFormula = Reduction.PackageFormula
  module PackageFormulaReduction = PackageFormula.Reduction

  type archive

  val stats : archive -> stats
  val load_index : string -> archive
  val no_such_package : archive -> Apk_parse.dep list -> string list
  val lone_provider : PackageFormula.coq_Formula -> (string * string) option

  val alt_at :
    PackageFormula.coq_Formula list ->
    Pac.nat ->
    (PackageFormula.coq_Formula * bool) option

  val alt_rank : archive -> bool -> PackageFormula.coq_Formula -> int

  module PVersion : sig
    type t = {
      pv : string option;
      rank : int;
      ord : int;
      v : PackageFormulaReduction.Version.t;
    }

    val v : t -> PackageFormulaReduction.Version.t
    val bot : t
    val pp : Format.formatter -> t -> unit
    val compare : t -> t -> int
  end

  val tag :
    archive ->
    PackageFormulaReduction.Name.t ->
    PackageFormulaReduction.Version.t ->
    PVersion.t

  val pp_name : Format.formatter -> PackageFormulaReduction.Name.t -> unit

  module FormulaLookups :
      module type of
        Package_formula.Make (Reduction.NameOT) (Reduction.VersionOT)
          (PackageFormula)
          (PVersion)
          (struct
            let pp_name = pp_name
          end)

  module Resolver = FormulaLookups.Resolver

  val lookups : archive -> FormulaLookups.t

  val touch :
    archive ->
    Apk_parse.dep list ->
    FormulaLookups.t ->
    PackageFormulaReduction.Reduced.Package.t ->
    unit
end

module Make () : S = struct
  (* Which condition a rule designates is free, and is a performance
     choice: the rule is materialised only once that condition is selected.
     Alpine writes the switch name (docs, openrc) first and almost nothing
     depends on those, where the least positive condition lands on a name
     most of the archive carries -- so the first-listed positive condition
     is recorded as the set is built, keyed by the element list, which is
     canonical where the set's own representation need not be.  The
     reduction takes the designation as a module, so the table is built
     with it. *)
  let designations : (Alpine.coq_Dep list, Alpine.Atom.t) Hashtbl.t =
    Hashtbl.create 4096

  (* the fallback keeps designation total on sets with a positive condition,
     discharging designation_spec, which is trusted, as ApkVersionMatch's
     prefix/hash are *)
  module FirstDesignation = struct
    let designation (conds : Alpine.ConditionSet.t) : Alpine.Atom.t option =
      let key = Alpine.ConditionSet.elements conds in
      match Hashtbl.find_opt designations key with
      | Some _ as a -> a
      | None -> first_pos key
  end

  module Reduction = Alpine.ReductionUnder (FirstDesignation)
  module PackageFormula = Reduction.PackageFormula
  module PackageFormulaReduction = PackageFormula.Reduction
  module Reduced = PackageFormulaReduction.Reduced

  let xconstr (c : Apk_parse.constr) : Alpine.coq_Constr =
    match c with
    | Apk_parse.Any -> Alpine.CAny
    | Apk_parse.Op (Apk_version.Eq, v) -> Alpine.COp (Pac.OpEq, v)
    | Apk_parse.Op (Apk_version.Lt, v) -> Alpine.COp (Pac.OpLt, v)
    | Apk_parse.Op (Apk_version.Gt, v) -> Alpine.COp (Pac.OpGt, v)
    | Apk_parse.Op (Apk_version.Le, v) -> Alpine.COp (Pac.OpLe, v)
    | Apk_parse.Op (Apk_version.Ge, v) -> Alpine.COp (Pac.OpGe, v)
    | Apk_parse.Op (Apk_version.Fuzzy, v) -> Alpine.CPrefix v
    | Apk_parse.Op (Apk_version.Gt_fuzzy, v) -> Alpine.CGtPrefix v
    | Apk_parse.Op (Apk_version.Lt_fuzzy, v) -> Alpine.CLtPrefix v
    | Apk_parse.Op (Apk_version.Hash, v) -> Alpine.CHash v

  let xatom (d : Apk_parse.dep) : Alpine.Atom.t =
    (d.Apk_parse.d_name, xconstr d.Apk_parse.d_constr)

  let xdep (d : Apk_parse.dep) : Alpine.coq_Dep =
    if d.Apk_parse.d_neg then Alpine.DNeg (xatom d) else Alpine.DPos (xatom d)

  let ptag (v : string option) : Alpine.coq_PTag =
    match v with Some pv -> Alpine.PVer pv | None -> Alpine.PBare

  (* building the set is also where the rule's first-listed positive
     condition is offered to [FirstDesignation]; an earlier rule keeps the
     designation when two rules share a set, so the table does not depend on
     when it is read *)
  let condset_of ds =
    let conds = List.map xdep ds in
    let cs = Alpine.ConditionSet.ofList conds in
    (match first_pos conds with
    | Some a ->
        let key = Alpine.ConditionSet.elements cs in
        if not (Hashtbl.mem designations key) then
          Hashtbl.add designations key a
    | None -> ());
    cs

  type iif_rule = {
    pkg : string * string;
    conds : Alpine.ConditionSet.t;
    designation : Alpine.Atom.t;
  }

  type archive = {
    by_name : (string, Apk_parse.pkg list) Hashtbl.t;
    meta : (string * string, Apk_parse.pkg) Hashtbl.t;
    providers : (string, ((string * string) * string option) list) Hashtbl.t;
    (* install-if rules by their designated condition's name: only a package
       bearing that name, or providing it, can carry the rule *)
    iif_by_cond : (string, iif_rule list) Hashtbl.t;
    prio : (string * string, int) Hashtbl.t;
    (* where each package stands in the index: apk_db_pkg_add appends to a
       name's provider list in the order the index is read *)
    pos : (string * string, int) Hashtbl.t;
    mutable n_pkgs : int;
    mutable n_provs : int;
    mutable n_iif : int;
    n_dropped : int;
    (* the names only a stanza the parser dropped holds a provider of *)
    uninstallable : (string, unit) Hashtbl.t;
  }

  let stats ar =
    {
      names = Hashtbl.length ar.by_name;
      versions = ar.n_pkgs;
      provides = ar.n_provs;
      install_ifs = ar.n_iif;
      dropped = ar.n_dropped;
    }

  (* Architecture is fixed by the index that was loaded.  A repository's
     APKINDEX is per-arch, so no A: filtering is applied and no cross-arch
     reasoning is possible here. *)
  let load_index (path : string) : archive =
    let dropped = ref 0 and uninstallable = Hashtbl.create 16 in
    let pkgs =
      Apk_parse.parse_file
        ~reject:(fun () -> incr dropped)
        ~broken:(List.iter (fun n -> Hashtbl.replace uninstallable n ()))
        path
    in
    let ar =
      {
        by_name = Hashtbl.create 16384;
        meta = Hashtbl.create 16384;
        providers = Hashtbl.create 16384;
        iif_by_cond = Hashtbl.create 1024;
        prio = Hashtbl.create 1024;
        pos = Hashtbl.create 16384;
        n_pkgs = 0;
        n_provs = 0;
        n_iif = 0;
        n_dropped = !dropped;
        uninstallable;
      }
    in
    let iifs = ref [] in
    List.iter
      (fun (p : Apk_parse.pkg) ->
        Tbl.push ar.by_name p.Apk_parse.name p;
        Hashtbl.replace ar.meta (p.Apk_parse.name, p.Apk_parse.version) p;
        Hashtbl.replace ar.pos (p.Apk_parse.name, p.Apk_parse.version) ar.n_pkgs;
        ar.n_pkgs <- ar.n_pkgs + 1;
        List.iter
          (fun (pr : Apk_parse.prov) ->
            Tbl.push ar.providers pr.Apk_parse.p_name
              ((p.Apk_parse.name, p.Apk_parse.version), pr.Apk_parse.p_ver);
            ar.n_provs <- ar.n_provs + 1)
          p.Apk_parse.provides;
        (match p.Apk_parse.priority with
        | Some k ->
            Hashtbl.replace ar.prio (p.Apk_parse.name, p.Apk_parse.version) k
        | None -> ());
        if p.Apk_parse.install_if <> [] then (
          ar.n_iif <- ar.n_iif + 1;
          (* a rule with no positive condition is left out, and nothing is
             lost -- apk reaches a rule only from an installed
             package bearing or providing a condition's name, which falsifies
             a negated condition unless it is the rule's own package *)
          if
            List.exists
              (fun (d : Apk_parse.dep) -> not d.Apk_parse.d_neg)
              p.Apk_parse.install_if
          then
            iifs :=
              ( (p.Apk_parse.name, p.Apk_parse.version),
                condset_of p.Apk_parse.install_if )
              :: !iifs))
      pkgs;
    (* keyed only once every set has offered its designation, so the key a
       rule is filed under is the one [attachDesignation] will ask about *)
    List.iter
      (fun (z, conds) ->
        match FirstDesignation.designation conds with
        | Some a ->
            Tbl.push ar.iif_by_cond (fst a) { pkg = z; conds; designation = a }
        | None -> ())
      (List.rev !iifs);
    ar

  let versions_of ar n = Tbl.find_list ar.by_name n
  let providers_of ar n = Tbl.find_list ar.providers n

  let empty_inst =
    {
      Alpine.inst_real = Alpine.PackageSet.empty;
      inst_deps = Alpine.DependencyRel.empty;
      inst_prov = Alpine.ProvidesRel.empty;
      inst_installIf = Alpine.InstallIfRuleRel.empty;
      inst_world = Alpine.WorldSet.empty;
      inst_prio = Alpine.PriorityRel.empty;
    }

  (* repoPreimage and provPreimage, built from the archive's tables rather
     than by filtering a whole-archive instance, which is the only reason a
     per-lookup sub-instance is cheap.  Lookup.subInst's inst_prio is the k:
     lines of its repository: provider_priority is apk's preference among
     the providers of a name, versioned ones included, and preference in
     this pipeline lives in PVersion.compare, off the archive, but whether
     it is non-zero also decides whether a provides without a version is
     selected automatically, which the calculus reads off inst_prio. *)
  let preimages_at ar (ns : string list) =
    let repo = ref [] and prov = ref [] in
    List.iter
      (fun n ->
        List.iter
          (fun (p : Apk_parse.pkg) ->
            repo := (p.Apk_parse.name, p.Apk_parse.version) :: !repo)
          (versions_of ar n);
        List.iter
          (fun (owner, pv) ->
            repo := owner :: !repo;
            prov := (owner, (n, ptag pv)) :: !prov)
          (providers_of ar n))
      (List.sort_uniq String.compare ns);
    let prio =
      List.filter_map
        (fun q ->
          match Hashtbl.find_opt ar.prio q with
          | Some k -> Some (q, Ot.int_nat k)
          | None -> None)
        !repo
    in
    ( Alpine.PackageSet.ofList !repo,
      Alpine.ProvidesRel.ofList !prov,
      Alpine.PriorityRel.ofList prio )

  (* Lookup.nameSubInst *)
  let name_inst ar (n : string) : Alpine.coq_Inst =
    let repo, prov, prio = preimages_at ar [ n ] in
    {
      empty_inst with
      Alpine.inst_real = repo;
      inst_prov = prov;
      inst_prio = prio;
    }

  (* Lookup.installIfFibre: of the rules designating a name this package
     bears or provides, the ones whose designated condition it actually
     satisfies.  attachAt reads the package itself and the provides entries
     it heads and nothing else, so deciding it against an instance carrying
     just those entries is the whole archive's answer
     (attachAt_subInst). *)
  let install_if_at ar ((n, v) : string * string) (own : Alpine.ProvidesRel.t) :
      iif_rule list =
    let inst = { empty_inst with Alpine.inst_prov = own } in
    let at = Tbl.find_list ar.iif_by_cond in
    let cands =
      List.fold_left
        (fun acc ((_, (m, _)) : Alpine.ProvidesElt.t) ->
          List.rev_append (at m) acc)
        (at n)
        (Alpine.ProvidesRel.elements own)
    in
    List.filter (fun r -> Reduction.attachAt inst (n, v) r.designation) cands

  (* Lookup.pkgSubInst: the package's own dependencies, provides entries
     and install-if rules, and the repository at the names those
     dependencies mention --
     together with, per install-if rule the package carries, the rule's
     declaring name and the names of the conditions it did not designate,
     and the world, which names the providers without k: it lets be selected *)
  let pkg_inst ar (world : Apk_parse.dep list) ((n, v) : string * string) :
      Alpine.coq_Inst =
    match Hashtbl.find_opt ar.meta (n, v) with
    | None -> empty_inst
    | Some m ->
        let own =
          Alpine.ProvidesRel.ofList
            (List.map
               (fun (pr : Apk_parse.prov) ->
                 ((n, v), (pr.Apk_parse.p_name, ptag pr.Apk_parse.p_ver)))
               m.Apk_parse.provides)
        in
        let rules = install_if_at ar (n, v) own in
        let ns =
          List.fold_left
            (fun acc r ->
              fst r.pkg
              :: List.rev_append
                   (List.map
                      (function Alpine.DPos (m, _) | Alpine.DNeg (m, _) -> m)
                      (Alpine.ConditionSet.elements
                         (Reduction.condRest r.conds)))
                   acc)
            (List.map
               (fun (d : Apk_parse.dep) -> d.Apk_parse.d_name)
               m.Apk_parse.depends)
            rules
        in
        let repo, prov, prio = preimages_at ar ns in
        let deps =
          Alpine.DependencyRel.ofList
            (List.map (fun d -> ((n, v), xdep d)) m.Apk_parse.depends)
        in
        {
          Alpine.inst_real = repo;
          inst_deps = deps;
          inst_prov = Alpine.ProvidesRel.union prov own;
          inst_installIf =
            Alpine.InstallIfRuleRel.ofList
              (List.map (fun r -> (r.pkg, r.conds)) rules);
          (* apk also takes a k:-less one whose owner has a requirer
             (solver.c:381) *)
          inst_world = Alpine.WorldSet.ofList (List.map xdep world);
          inst_prio = prio;
        }

  (* Lookup.rootSubInst: the world set and the repository at the names it
     mentions.  Every install-if rule is carried by a package, so the root
     reads no part of the rule table.  The world is the query's
     arguments and nothing else: this resolves from an empty root rather
     than from an existing /etc/apk/world. *)
  let root_inst ar (world : Apk_parse.dep list) : Alpine.coq_Inst =
    let repo, prov, prio =
      preimages_at ar
        (List.map (fun (d : Apk_parse.dep) -> d.Apk_parse.d_name) world)
    in
    {
      empty_inst with
      Alpine.inst_real = repo;
      inst_prov = prov;
      inst_world = Alpine.WorldSet.ofList (List.map xdep world);
      inst_prio = prio;
    }

  let no_such_package ar (world : Apk_parse.dep list) : string list =
    List.filter_map
      (fun (d : Apk_parse.dep) ->
        let n = d.Apk_parse.d_name in
        if
          (not d.Apk_parse.d_neg)
          && versions_of ar n = []
          && providers_of ar n = []
          && not (Hashtbl.mem ar.uninstallable n)
        then Some n
        else None)
      world

  let rec pp_formula depth fmt (f : PackageFormula.coq_Formula) =
    if depth <= 0 then Format.fprintf fmt "..."
    else
      match f with
      | PackageFormula.FAtom (n, vs) ->
          Format.fprintf fmt "%a{%d}" pp_alp_name n
            (List.length (PackageFormula.VSet.elements vs))
      | PackageFormula.FConj (a, b) ->
          Format.fprintf fmt "(%a&%a)"
            (pp_formula (depth - 1))
            a
            (pp_formula (depth - 1))
            b
      | PackageFormula.FDisj (a, b) ->
          Format.fprintf fmt "(%a|%a)"
            (pp_formula (depth - 1))
            a
            (pp_formula (depth - 1))
            b
      | PackageFormula.FNeg a ->
          Format.fprintf fmt "!%a" (pp_formula (depth - 1)) a

  and pp_alp_name fmt (n : Reduction.Name.name) =
    match n with
    | Reduction.Name.Root -> Format.fprintf fmt "@root"
    | Reduction.Name.Orig s -> Format.fprintf fmt "%s" s

  (* The rank an unversioned-provider disjunction's branches are compared
     on: the k: line where a provider carries one; [rank_unranked] below
     all of them where it does not, since apk-package(5) says such a
     provider is not selected automatically and encReq admits it only when
     the world names its owner; [rank_pkg] for the branch holding the
     name's own versions, above every unversioned provider because those
     offer no version at the name and apk's first key between providers it
     has not disqualified is the offered version; and [rank_none] for a
     branch that offers nothing. *)
  let rank_pkg = max_int
  let rank_unranked = -1
  let rank_none = min_int

  let prov_rank ar (q : string * string) : int =
    match Hashtbl.find_opt ar.prio q with Some k -> k | None -> rank_unranked

  (* apk's provider_priority defaults to 0 for a package with no k: line,
     and the field is the package's own, read off whichever package offers
     the name -- a provider and a package claiming the name itself alike. *)
  let prio_of ar (q : string * string) : int =
    match Hashtbl.find_opt ar.prio q with Some k -> k | None -> 0

  (* encReq and encPos list the unversioned providers of a name as a
     disjunction whose last alternative is the name's own versions, so every
     alternative but the last is a lone provider.  An install-if disjunction
     opens on an FNeg alternative and a negated dependency makes no
     disjunction at all, so an alternative naming a single package
     identifies a provider list. *)
  let lone_provider (f : PackageFormula.coq_Formula) : (string * string) option
      =
    match f with
    | PackageFormula.FAtom (Reduction.Name.Orig m, vs) -> (
        match PackageFormula.VSet.elements vs with
        | [ Reduction.Version.Orig w ] -> Some (m, w)
        | _ -> None)
    | _ -> None

  (* The alternative a synthetic version selects, and whether it is the last
     one -- the last alternative is the only one that is not a provider. *)
  let rec alt_at (fs : PackageFormula.coq_Formula list) (i : Pac.nat) :
      (PackageFormula.coq_Formula * bool) option =
    match (fs, i) with
    | [ f ], Pac.O -> Some (f, true)
    | f :: _, Pac.O -> Some (f, false)
    | _ :: fs', Pac.S k -> alt_at fs' k
    | [], _ -> None

  let alt_rank ar (last : bool) (f : PackageFormula.coq_Formula) : int =
    if last then
      match f with
      | PackageFormula.FAtom (_, vs) ->
          if PackageFormula.VSet.elements vs = [] then rank_none else rank_pkg
      | _ -> rank_none
    else
      match lone_provider f with Some q -> prov_rank ar q | None -> rank_none

  (* apk's compare_providers (solver.c): the version offered at the name
     [pv], provider_priority [rank], then index order [ord], as
     select_package keeps the first provider it meets; the newer-own-version
     key (solver.c:651-661) never separates packages an index lists once,
     and the solver-state keys (solver.c:578-595) only rank a provider apk
     has not disqualified above one it has, which PubGrub's ranges and
     backtracking do.  Among other
     [Idx] alternatives the earliest wins, so an install-if fires only once
     its conditions hold.  The keys ride on the version, as a comparator
     sees no name.  [tag] sets them from the (name, version) pair for the
     versions lookup and every range alike, so the order stays total and
     agrees with any range's tags.  [bot] is greatest, so a name only a
     negated requirement reaches is left out. *)
  module PVersion = struct
    type t = {
      pv : string option;
      rank : int;
      ord : int;
      v : PackageFormulaReduction.Version.t;
    }

    let v (x : t) = x.v

    let bot =
      {
        pv = None;
        rank = 0;
        ord = max_int;
        v = PackageFormulaReduction.Version.Bot;
      }

    let pp fmt ({ v; _ } : t) =
      match v with
      | PackageFormulaReduction.Version.Orig Reduction.Version.UnitV ->
          Format.fprintf fmt "()"
      | PackageFormulaReduction.Version.Orig (Reduction.Version.Orig s) ->
          Format.fprintf fmt "%s" s
      | PackageFormulaReduction.Version.Orig
          (Reduction.Version.Prov ((n, w), pv)) ->
          Format.fprintf fmt "provided=%s(%s-%s)" pv n w
      | PackageFormulaReduction.Version.Idx i ->
          Format.fprintf fmt "%d" (Ot.nat_int i)
      | PackageFormulaReduction.Version.Bot -> Format.fprintf fmt "⊥"

    let compare a b =
      match (a.v, b.v) with
      | ( PackageFormulaReduction.Version.Idx _,
          PackageFormulaReduction.Version.Idx _ ) ->
          let c = Stdlib.compare a.rank b.rank in
          if c <> 0 then c
          else
            let c = Stdlib.compare b.ord a.ord in
            if c <> 0 then c
            else -Ot.r2c (PackageFormulaReduction.VersionOT.compare a.v b.v)
      | _ -> (
          match (a.pv, b.pv) with
          | Some x, Some y ->
              let c = Apk_version.compare x y in
              if c <> 0 then c
              else
                let c = Stdlib.compare a.rank b.rank in
                if c <> 0 then c
                else
                  let c = Stdlib.compare b.ord a.ord in
                  if c <> 0 then c
                  else
                    Ot.r2c (PackageFormulaReduction.VersionOT.compare a.v b.v)
          | _ ->
              let c =
                Ot.r2c (PackageFormulaReduction.VersionOT.compare a.v b.v)
              in
              if c <> 0 then c else Stdlib.compare a.rank b.rank)
  end

  let ord_of ar (q : string * string) : int =
    match Hashtbl.find_opt ar.pos q with Some i -> i | None -> max_int

  let tag ar (tn : PackageFormulaReduction.Name.t)
      (tv : PackageFormulaReduction.Version.t) : PVersion.t =
    match (tn, tv) with
    | ( PackageFormulaReduction.Name.Disjunct (f0 :: _ as fs),
        PackageFormulaReduction.Version.Idx i )
      when lone_provider f0 <> None -> (
        match alt_at fs i with
        | None -> { PVersion.pv = None; rank = 0; ord = max_int; v = tv }
        | Some (f, last) ->
            let ord =
              match lone_provider f with
              | Some q -> ord_of ar q
              | None -> max_int
            in
            { PVersion.pv = None; rank = alt_rank ar last f; ord; v = tv })
    | _, PackageFormulaReduction.Version.Orig (Reduction.Version.Prov (q, pv))
      ->
        {
          PVersion.pv = Some pv;
          rank = prio_of ar q;
          ord = ord_of ar q;
          v = tv;
        }
    (* a package claiming the name itself offers its own version there *)
    | ( PackageFormulaReduction.Name.Orig (Reduction.Name.Orig n),
        PackageFormulaReduction.Version.Orig (Reduction.Version.Orig w) ) ->
        {
          PVersion.pv = Some w;
          rank = prio_of ar (n, w);
          ord = ord_of ar (n, w);
          v = tv;
        }
    | _ -> { PVersion.pv = None; rank = 0; ord = max_int; v = tv }

  let pp_name fmt (n : PackageFormulaReduction.Name.t) =
    match n with
    | PackageFormulaReduction.Name.Orig m -> pp_alp_name fmt m
    | PackageFormulaReduction.Name.Disjunct fs ->
        Format.fprintf fmt "<%a>"
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "|")
             (pp_formula 2))
          fs

  module FormulaLookups =
    Package_formula.Make (Reduction.NameOT) (Reduction.VersionOT)
      (PackageFormula)
      (PVersion)
      (struct
        let pp_name = pp_name
      end)

  module Resolver = FormulaLookups.Resolver

  (* Lookup.versions_lookupOrig: what the versions callback answers, before
     the tagging PubGrub sees -- the name's own versions and its provides.
     The encoder reads this at the names a formula negates: a negated
     requirement's complement ranges over the versions offered at the name,
     provides included. *)
  let oracle ar (tn : Reduction.Name.name) : PackageFormula.VSet.t =
    match tn with
    | Reduction.Name.Orig n -> Reduction.versions (name_inst ar n) n
    | Reduction.Name.Root ->
        PackageFormula.VSet.singleton Reduction.Version.UnitV

  let lookups ar : FormulaLookups.t =
    FormulaLookups.create
      ~root:(Reduction.Name.Root, Reduction.Version.UnitV)
      ~tag:(tag ar) ~oracle:(oracle ar) ()

  let dependees inst q =
    Reduction.PackageFormulaSet.elements (Reduction.dependees inst q)

  let touch ar world st ((tn, tv) : Reduced.Package.t) =
    match (tn, tv) with
    | ( PackageFormulaReduction.Name.Orig Reduction.Name.Root,
        PackageFormulaReduction.Version.Orig Reduction.Version.UnitV ) ->
        (* Lookup.dependees_lookupRoot *)
        FormulaLookups.process st Reduction.rootPkg (fun () ->
            dependees (root_inst ar world) Reduction.rootPkg)
    | ( PackageFormulaReduction.Name.Orig (Reduction.Name.Orig n),
        PackageFormulaReduction.Version.Orig (Reduction.Version.Orig v) ) ->
        (* Lookup.dependees_lookupOrig *)
        let q = (Reduction.Name.Orig n, Reduction.Version.Orig v) in
        FormulaLookups.process st q (fun () ->
            dependees (pkg_inst ar world (n, v)) q)
    | ( PackageFormulaReduction.Name.Orig (Reduction.Name.Orig m),
        PackageFormulaReduction.Version.Orig (Reduction.Version.Prov (q0, pv)) )
      ->
        (* Lookup.dependees_lookupProv: a provides reads no instance *)
        let q = (Reduction.Name.Orig m, Reduction.Version.Prov (q0, pv)) in
        FormulaLookups.process st q (fun () -> dependees empty_inst q)
    | _ -> ()
end
