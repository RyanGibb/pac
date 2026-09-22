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
   PVersion.compare, which is where its value is applied -- off the
   archive, not off an instance.  Whether it is non-zero also decides
   whether a provides without a version can be selected at all, which the
   calculus reads off inst_prio, so a sub-instance carries the k: lines
   of the unversioned providers it asks about. *)

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

(* building the set is also where the rule's first-listed atom is offered
   to [FirstDesignation]; an earlier rule keeps the designation when two
   rules share a set, so the table does not depend on when it is read *)
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
  (* provided name -> the provides entries claiming it *)
  providers : (string, ((string * string) * string option) list) Hashtbl.t;
  (* install-if rules by their designated condition's name: only a package
     bearing that name, or providing it, can carry the rule *)
  iif_by_cond : (string, iif_rule list) Hashtbl.t;
  (* each package's own install-if rule, as it entered the instance *)
  iif_own : (string * string, Alp.CondSet.t) Hashtbl.t;
  (* name -> the packages depending on it positively, with the atom.
     Only an unversioned provider without k: needs it, so a graph without
     one never builds it. *)
  rdeps : (string, ((string * string) * P.dep) list) Hashtbl.t Lazy.t;
  prio : (string * string, int) Hashtbl.t;
  mutable supp : Alp.PkgSet.t option;
  mutable n_pkgs : int;
  mutable n_provs : int;
  mutable n_iif : int;
}

let push tbl k v =
  let prev = match Hashtbl.find_opt tbl k with Some l -> l | None -> [] in
  Hashtbl.replace tbl k (v :: prev)

let reverse_deps (pkgs : P.pkg list) =
  let t = Hashtbl.create 16384 in
  List.iter
    (fun (p : P.pkg) ->
      List.iter
        (fun (d : P.dep) ->
          if not d.P.d_neg then push t d.P.d_name ((p.P.name, p.P.version), d))
        p.P.depends)
    pkgs;
  t

let load_index (path : string) : archive =
  let pkgs = P.parse_file path in
  let ar =
    {
      by_name = Hashtbl.create 16384;
      meta = Hashtbl.create 16384;
      providers = Hashtbl.create 16384;
      iif_by_cond = Hashtbl.create 1024;
      iif_own = Hashtbl.create 1024;
      rdeps = lazy (reverse_deps pkgs);
      prio = Hashtbl.create 1024;
      supp = None;
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
          let cs = condset_of p.P.install_if in
          Hashtbl.replace ar.iif_own (p.P.name, p.P.version) cs;
          iifs := ((p.P.name, p.P.version), cs) :: !iifs))
    pkgs;
  (* keyed only once every set has offered its designation, so the key a
     rule is filed under is the one [attachDesignation] will ask about *)
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

let providers_of ar n =
  match Hashtbl.find_opt ar.providers n with Some l -> l | None -> []

(* ---- sub-instances -----------------------------------------------------

   repoPreimage I ns keeps the repository's packages at a name in ns
   together with the packages providing one of them; provPreimage I ns
   keeps the provides entries landing on a name in ns.  Both are built
   from the indexes rather than by filtering a whole-archive instance,
   which is the only reason a per-lookup sub-instance is cheap. *)

let empty_inst =
  {
    Alp.inst_repo = Alp.PkgSet.empty;
    inst_deps = Alp.Deps.empty;
    inst_prov = Alp.Prov.empty;
    inst_installIf = Alp.InstallIf.empty;
    inst_world = Alp.WSet.empty;
    inst_prio = Alp.Prio.empty;
    inst_repl = Alp.Repl.empty;
    inst_supp = Alp.PkgSet.empty;
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

let rec nat_of_int (k : int) : E.nat =
  if k <= 0 then E.O else E.S (nat_of_int (k - 1))

(* k > 0 rather than k <> 0, since nat_of_int sends a negative k: to 0 *)
let has_priority ar (q : string * string) =
  match Hashtbl.find_opt ar.prio q with Some k -> k > 0 | None -> false

(* Lookup.selectableAlts_lookup: the k: lines of the unversioned providers
   of the bare dependencies being encoded, and for those without one, their
   provides, the dependencies and world atoms naming what they provide with
   a version or are named, their install-if rules and those rules'
   condition names.  Returning early when every provider has a k: is what
   leaves the reverse-dependency table unbuilt. *)
type selectable = {
  g_prio : Alp.Prio.t;
  g_prov : Alp.Prov.t;
  g_deps : Alp.Deps.t;
  g_world : Alp.WSet.t;
  g_rules : Alp.InstallIf.t;
  g_names : string list;
}

let selectable_tables ar (world : P.dep list) (any : string list) : selectable =
  let vs =
    List.sort_uniq compare
      (List.concat_map
         (fun n ->
           List.filter_map
             (fun (owner, pv) -> if pv = None then Some owner else None)
             (providers_of ar n))
         (List.sort_uniq String.compare any))
  in
  let prio =
    List.filter_map
      (fun q ->
        match Hashtbl.find_opt ar.prio q with
        | Some k -> Some (q, nat_of_int k)
        | None -> None)
      vs
  in
  let gs = List.filter (fun q -> not (has_priority ar q)) vs in
  if gs = [] then
    {
      g_prio = Alp.Prio.ofList prio;
      g_prov = Alp.Prov.empty;
      g_deps = Alp.Deps.empty;
      g_world = Alp.WSet.empty;
      g_rules = Alp.InstallIf.empty;
      g_names = [];
    }
  else
    let provides q =
      match Hashtbl.find_opt ar.meta q with
      | Some m -> m.P.provides
      | None -> []
    in
    let prov =
      List.concat_map
        (fun q ->
          List.map
            (fun (pr : P.prov) -> (q, (pr.P.p_name, ptag pr.P.p_ver)))
            (provides q))
        gs
    in
    let claimed =
      List.sort_uniq String.compare
        (List.concat_map
           (fun q ->
             fst q
             :: List.filter_map
                  (fun (pr : P.prov) ->
                    if pr.P.p_ver <> None then Some pr.P.p_name else None)
                  (provides q))
           gs)
    in
    let rdeps = Lazy.force ar.rdeps in
    let deps =
      List.concat_map
        (fun m ->
          match Hashtbl.find_opt rdeps m with
          | Some l -> List.map (fun (r, d) -> (r, xdep d)) l
          | None -> [])
        claimed
    in
    let world_on =
      List.filter
        (fun (d : P.dep) -> (not d.P.d_neg) && List.mem d.P.d_name claimed)
        world
    in
    let rules =
      List.filter_map
        (fun q ->
          match Hashtbl.find_opt ar.iif_own q with
          | Some cs -> Some (q, cs)
          | None -> None)
        gs
    in
    {
      g_prio = Alp.Prio.ofList prio;
      g_prov = Alp.Prov.ofList prov;
      g_deps = Alp.Deps.ofList deps;
      g_world = Alp.WSet.ofList (List.map xdep world_on);
      g_rules = Alp.InstallIf.ofList rules;
      g_names =
        List.concat_map
          (fun (_, cs) -> List.map fst (Alp.CondSet.elements cs))
          rules;
    }

(* inst_supp: the requirers and install_if triggers that could make an
   unversioned provider without k: selectable, and whatever could lead to
   one of them, since a package added to support one needs support too.
   PAC_SUPPORT_ALL demands it of every package instead. *)
let supp_of ar =
  match ar.supp with
  | Some s -> s
  | None ->
      let rdeps = Lazy.force ar.rdeps in
      let requirers name =
        match Hashtbl.find_opt rdeps name with
        | Some l -> List.map fst l
        | None -> []
      in
      let offerers name =
        List.map
          (fun (p : P.pkg) -> (p.P.name, p.P.version))
          (versions_of ar name)
        @ List.map fst (providers_of ar name)
      in
      let provides q =
        match Hashtbl.find_opt ar.meta q with
        | Some m -> m.P.provides
        | None -> []
      in
      let conds q =
        match Hashtbl.find_opt ar.iif_own q with
        | Some cs -> List.map fst (Alp.CondSet.elements cs)
        | None -> []
      in
      let seen = Hashtbl.create 64 and queue = Queue.create () in
      let add q =
        if not (Hashtbl.mem seen q) then (
          Hashtbl.replace seen q ();
          Queue.add q queue)
      in
      if Sys.getenv_opt "PAC_SUPPORT_ALL" <> None then
        Hashtbl.iter (fun q _ -> add q) ar.meta
      else
        Hashtbl.iter
          (fun q (m : P.pkg) ->
            if
              (not (has_priority ar q))
              && List.exists
                   (fun (pr : P.prov) -> pr.P.p_ver = None)
                   m.P.provides
            then (
              List.iter
                (fun n -> List.iter add (requirers n))
                (fst q
                :: List.filter_map
                     (fun (pr : P.prov) ->
                       if pr.P.p_ver <> None then Some pr.P.p_name else None)
                     m.P.provides);
              List.iter (fun n -> List.iter add (offerers n)) (conds q)))
          ar.meta;
      while not (Queue.is_empty queue) do
        let x = Queue.pop queue in
        List.iter
          (fun n -> List.iter add (requirers n))
          (fst x :: List.map (fun (pr : P.prov) -> pr.P.p_name) (provides x));
        List.iter (fun n -> List.iter add (offerers n)) (conds x)
      done;
      let s =
        Alp.PkgSet.ofList (Hashtbl.fold (fun q () acc -> q :: acc) seen [])
      in
      ar.supp <- Some s;
      s

(* Lookup.nameSubInst *)
let name_inst ar (n : string) : Alp.coq_Inst =
  let repo, prov = preimages_at ar [ n ] in
  {
    empty_inst with
    Alp.inst_repo = repo;
    inst_prov = prov;
    inst_supp = supp_of ar;
  }

(* What supportForm reads for one package: the dependencies naming
   anything it provides, its own install-if rule and that rule's condition
   names, and its k: line. *)
type support = {
  s_deps : Alp.Deps.t;
  s_rules : Alp.InstallIf.t;
  s_prio : Alp.Prio.t;
  s_names : string list;
}

let support_tables ar ((n, v) : string * string) (m : P.pkg) : support =
  let offered =
    List.sort_uniq String.compare
      (n :: List.map (fun (pr : P.prov) -> pr.P.p_name) m.P.provides)
  in
  let deps =
    if not (Alp.PkgSet.mem (n, v) (supp_of ar)) then []
    else
      let rdeps = Lazy.force ar.rdeps in
      List.concat_map
        (fun name ->
          match Hashtbl.find_opt rdeps name with
          | Some l -> List.map (fun (r, d) -> (r, xdep d)) l
          | None -> [])
        offered
  in
  let rules =
    match Hashtbl.find_opt ar.iif_own (n, v) with
    | Some cs -> [ ((n, v), cs) ]
    | None -> []
  in
  {
    s_deps = Alp.Deps.ofList deps;
    s_rules = Alp.InstallIf.ofList rules;
    s_prio =
      (match Hashtbl.find_opt ar.prio (n, v) with
      | Some k -> Alp.Prio.singleton ((n, v), nat_of_int k)
      | None -> Alp.Prio.empty);
    s_names =
      List.concat_map
        (fun (_, cs) -> List.map fst (Alp.CondSet.elements cs))
        rules;
  }

let any_names (ds : P.dep list) =
  List.filter_map
    (fun (d : P.dep) ->
      if (not d.P.d_neg) && d.P.d_constr = P.Any then Some d.P.d_name else None)
    ds

(* Lookup.installIfFibre: of the rules designating a name this package
   bears or provides, the ones whose designated condition it actually
   satisfies.  attachAt reads the package itself and the provides entries
   it heads and nothing else, so deciding it against an instance carrying
   just those entries is the whole archive's answer
   (attachAt_subInst). *)
let install_if_at ar ((n, v) : string * string) (own : Alp.Prov.t) :
    iif_rule list =
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

(* Lookup.pkgSubInst: the package's own dependencies, provides entries
   and install-if rules, and the repository at the names those
   dependencies mention --
   together with, per install-if rule the package carries, the rule's
   declaring name and the names of the conditions it did not designate,
   and the selectable_tables of its bare dependencies *)
let pkg_inst ar (world : P.dep list) ((n, v) : string * string) : Alp.coq_Inst =
  match Hashtbl.find_opt ar.meta (n, v) with
  | None -> empty_inst
  | Some m ->
      let own =
        Alp.Prov.ofList
          (List.map
             (fun (pr : P.prov) -> ((n, v), (pr.P.p_name, ptag pr.P.p_ver)))
             m.P.provides)
      in
      let rules = install_if_at ar (n, v) own in
      let ns =
        List.fold_left
          (fun acc r ->
            fst r.t_pkg
            :: List.rev_append
                 (List.map fst (Alp.CondSet.elements (Red.condRest r.t_conds)))
                 acc)
          (List.map (fun (d : P.dep) -> d.P.d_name) m.P.depends)
          rules
      in
      let g = selectable_tables ar world (any_names m.P.depends) in
      let sp = support_tables ar (n, v) m in
      let repo, prov =
        preimages_at ar
          (List.rev_append sp.s_names (List.rev_append g.g_names ns))
      in
      let deps =
        Alp.Deps.ofList (List.map (fun d -> ((n, v), xdep d)) m.P.depends)
      in
      {
        empty_inst with
        Alp.inst_repo = repo;
        inst_deps = Alp.Deps.union deps (Alp.Deps.union g.g_deps sp.s_deps);
        inst_prov = Alp.Prov.union (Alp.Prov.union own g.g_prov) prov;
        inst_installIf =
          Alp.InstallIf.union
            (Alp.InstallIf.ofList
               (List.map (fun r -> (r.t_pkg, r.t_conds)) rules))
            (Alp.InstallIf.union g.g_rules sp.s_rules);
        inst_world = Alp.WSet.ofList (List.map xdep world);
        inst_prio = Alp.Prio.union g.g_prio sp.s_prio;
        inst_supp = supp_of ar;
      }

(* Lookup.rootSubInst: the world set, the repository at the names it
   mentions, and the selectable_tables of its bare atoms. *)
let root_inst ar (world : P.dep list) : Alp.coq_Inst =
  let g = selectable_tables ar world (any_names world) in
  let repo, prov =
    preimages_at ar
      (List.rev_append g.g_names
         (List.map (fun (d : P.dep) -> d.P.d_name) world))
  in
  {
    empty_inst with
    Alp.inst_repo = repo;
    inst_deps = g.g_deps;
    inst_prov = Alp.Prov.union g.g_prov prov;
    inst_installIf = g.g_rules;
    inst_world = Alp.WSet.ofList (List.map xdep world);
    inst_prio = g.g_prio;
    inst_supp = supp_of ar;
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

(* The rank an unversioned-provider disjunction's branches are compared
   on: the k: line where a provider carries one, [rank_unranked] below
   all of them where it does not, since apk-package(5) says a provides
   without a provider-priority is not selected automatically at all and
   the nearest a preference can come to that is last place; [rank_pkg]
   for the branch holding the name's own versions, above every
   unversioned provider because those offer no version at the name and
   apk's first key is the offered version; and [rank_none] for a branch
   that offers nothing. *)
let rank_pkg = max_int
let rank_unranked = -1
let rank_none = min_int

let prov_rank ar (q : string * string) : int =
  match Hashtbl.find_opt ar.prio q with Some k -> k | None -> rank_unranked

(* apk's provider_priority defaults to 0 for a package with no k: line,
   and the field is the package's own, read off whichever package offers
   the name -- an alias and a package claiming the name itself alike. *)
let prio_of ar (q : string * string) : int =
  match Hashtbl.find_opt ar.prio q with Some k -> k | None -> 0

(* encPos and encReq list the unversioned providers of a name as a
   disjunction whose last alternative is the name's own versions, so every
   alternative but the last selects one provider: the alternative itself,
   or the last conjunct of one of selectableAlts' conjunctions.  An install-if
   disjunction and a negated dependency both list FNeg alternatives, so an
   alternative ending in a single package identifies a provider list. *)
let rec chain_head (f : PF.coq_Formula) : (string * string) option =
  match f with
  | PF.FDep (Red.Name.Orig m, vs) -> (
      match PF.VSet.elements vs with
      | [ Red.Version.Orig w ] -> Some (m, w)
      | _ -> None)
  | PF.FConj (_, b) -> chain_head b
  | _ -> None

(* what a selectableAlts alternative needs besides its provider *)
let rec alt_needs (f : PF.coq_Formula) : PF.coq_Formula list =
  match f with PF.FConj (a, b) -> a :: alt_needs b | _ -> []

(* The alternative a synthetic version selects, and whether it is the last
   one -- the last alternative is the only one that is not a provider. *)
let rec alt_at (fs : PF.coq_Formula list) (i : E.nat) :
    (PF.coq_Formula * bool) option =
  match (fs, i) with
  | [ f ], E.O -> Some (f, true)
  | f :: _, E.O -> Some (f, false)
  | _ :: fs', E.S k -> alt_at fs' k
  | [], _ -> None

(* The rank of one alternative: an unversioned provider by its k: line,
   the last alternative -- the name's own versions -- above every one of
   them, because an unversioned provides offers no version at the name
   and apk's first key is the offered version. *)
let alt_rank ar (last : bool) (f : PF.coq_Formula) : int =
  if last then
    match f with
    | PF.FDep (_, vs) ->
        if PF.VSet.elements vs = [] then rank_none else rank_pkg
    | _ -> rank_none
  else match chain_head f with Some q -> prov_rank ar q | None -> rank_none

(* PubGrub decides the compare-maximum candidate, so preference lives
   here, and what it has to reproduce is apk's compare_providers over
   the providers of the name being decided.  Most of that comparator's
   keys read the partial solution or the installed db and are dead
   against a fresh root; the two that survive are, in order, the version
   the provider offers *at the requested name* and then
   provider_priority, with the repository order below both and a single
   repository here.

   What a provider offers at a name is its own version where it claims
   the name itself, the p: operand where it is a versioned alias, and
   nothing at all where the provides carries no version.  So a package
   of a name is not privileged over an alias of it: the two are compared
   on the versions they offer, and an alias offering the newer one wins.
   An unversioned provides is the one case where a real package always
   wins, and not by privilege either -- it offers no version, and no
   version loses to every version.  provider_priority is read off
   whichever package offers the name, alias or not, and so decides only
   once the offered versions tie.

   A synthetic version selects one alternative of its disjunction by
   position, and which alternative is wanted depends on the disjunction.
   installIfForm lists the negated install_if conditions first and the
   augmented package last, so preferring the earliest alternative is
   apk's rule that an install-if fires only when its conditions already hold
   -- without it every install_if rule in the index is discharged by
   installing its target.  encPos folds the versioned aliases of a name
   into the name's own version set, where the comparison above settles
   them, and lists only the unversioned providers as separate
   alternatives ahead of it -- so that disjunction is exactly the case
   where the name's own versions win outright, with k: ordering the
   unversioned providers among themselves.

   The offered version and the k: are carried on the version rather than
   read off it: which disjunction a position belongs to is what decides
   an [Idx], and a comparator sees two versions and not their name.
   Every version PubGrub holds is handed to it by [versions] or by a
   dependency range, both of which know the name, so both tag as they go
   and both fields are a function of the (name, version) pair -- keeping
   this a total order, and one consistent with the tags on any range the
   same name is compared against. *)
module PVersion = struct
  (* [pv] is the version offered at the name being decided, absent for a
     version that is not a provider candidate at a name (the root, and a
     disjunction's positional [Idx]). *)
  type t = { pv : string option; rank : int; v : PFR.Version.t }

  let pp fmt ({ v; _ } : t) =
    match v with
    | PFR.Version.Orig Red.Version.RootV -> Format.fprintf fmt "()"
    | PFR.Version.Orig (Red.Version.Orig s) -> Format.fprintf fmt "%s" s
    | PFR.Version.Orig (Red.Version.Prov ((n, w), pv)) ->
        Format.fprintf fmt "%s=%s(%s-%s)" "provided" pv n w
    | PFR.Version.Idx i -> Format.fprintf fmt "%d" (nat_int i)

  let compare a b =
    match (a.v, b.v) with
    | PFR.Version.Idx _, PFR.Version.Idx _ ->
        let c = Stdlib.compare a.rank b.rank in
        if c <> 0 then c else -r2c (PFR.VersionOT.compare a.v b.v)
    | _ -> (
        match (a.pv, b.pv) with
        | Some x, Some y ->
            let c = Apk_version.compare x y in
            if c <> 0 then c
            else
              let c = Stdlib.compare a.rank b.rank in
              (* two providers apk cannot separate; the encoded order
                 keeps the pick deterministic *)
              if c <> 0 then c else r2c (PFR.VersionOT.compare a.v b.v)
        | _ ->
            let c = r2c (PFR.VersionOT.compare a.v b.v) in
            if c <> 0 then c else Stdlib.compare a.rank b.rank)
end

let tag ar (tn : PFR.Name.t) (tv : PFR.Version.t) : PVersion.t =
  match (tn, tv) with
  | PFR.Name.Disjunct (f0 :: _ as fs), PFR.Version.Idx i
    when chain_head f0 <> None -> (
      match alt_at fs i with
      | None -> { PVersion.pv = None; rank = 0; v = tv }
      | Some (f, last) ->
          { PVersion.pv = None; rank = alt_rank ar last f; v = tv })
  | _, PFR.Version.Orig (Red.Version.Prov (q, pv)) ->
      { PVersion.pv = Some pv; rank = prio_of ar q; v = tv }
  (* a package claiming the name itself offers its own version there *)
  | PFR.Name.Orig (Red.Name.Orig n), PFR.Version.Orig (Red.Version.Orig w) ->
      { PVersion.pv = Some w; rank = prio_of ar (n, w); v = tv }
  | _ -> { PVersion.pv = None; rank = 0; v = tv }

module PG = Pubgrub.Make (PName) (PVersion)

let greatest = function
  | [] -> invalid_arg "greatest"
  | c :: cs ->
      List.fold_left (fun a b -> if PVersion.compare b a > 0 then b else a) c cs

(* only installIfForm's disjuncts open on FNeg: encDep negates whole
   formulas *)
let is_install_if (tn : PFR.Name.t) =
  match tn with PFR.Name.Disjunct (PF.FNeg _ :: _) -> true | _ -> false

let has_selectable_alts (tn : PFR.Name.t) =
  match tn with
  | PFR.Name.Disjunct (f0 :: _ as fs) ->
      chain_head f0 <> None
      && List.exists (function PF.FConj _ -> true | _ -> false) fs
  | _ -> false

module NameMap = Map.Make (struct
  type t = PFR.Name.t

  let compare a b = r2c (PFR.NameOT.compare a b)
end)

(* the disjuncts supportForm introduced, recorded as [process] builds them *)
let support_names : unit NameMap.t ref = ref NameMap.empty
let is_support tn = NameMap.mem tn !support_names

let carried_at ~assigned tn tvs =
  match assigned tn with
  | PG.Unselected -> false
  | PG.Decided u -> List.exists (fun v -> PVersion.compare u v = 0) tvs
  | PG.Entailed r -> List.exists (fun v -> PG.Ranges.contains v r) tvs

(* whether f already holds of the decisions made so far, reading a
   negation as holding whenever its operand does not yet *)
let rec holds ar ~assigned (f : PF.coq_Formula) : bool =
  match f with
  | PF.FDep (m, vs) ->
      let tn = PFR.Name.Orig m in
      carried_at ~assigned tn
        (List.map
           (fun w -> tag ar tn (PFR.Version.Orig w))
           (PF.VSet.elements vs))
  | PF.FConj (a, b) -> holds ar ~assigned a && holds ar ~assigned b
  | PF.FDisj (a, b) -> holds ar ~assigned a || holds ar ~assigned b
  | PF.FNeg a -> not (holds ar ~assigned a)

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
  (* a supporter is never installed to support: one the solution already
     carries, or else anything, which fails and backtracks *)
  | PFR.Name.Disjunct fs when is_support tn -> (
      let carried =
        List.filter
          (fun (pv : PVersion.t) ->
            match pv.PVersion.v with
            | PFR.Version.Idx i -> (
                match alt_at fs i with
                | Some (f, _) -> holds ar ~assigned f
                | None -> false)
            | _ -> false)
          cands
      in
      match carried with [] -> greatest cands | _ -> greatest carried)
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
  (* apk selects such a provider only once a requirer or a trigger is
     already there, and never installs one to make it selectable; an
     alternative whose support the solution does not yet carry is taken
     only when nothing else is left *)
  | PFR.Name.Disjunct fs when has_selectable_alts tn -> (
      let ready =
        List.filter
          (fun (pv : PVersion.t) ->
            match pv.PVersion.v with
            | PFR.Version.Idx i -> (
                match alt_at fs i with
                | Some (f, _) -> List.for_all (holds ar ~assigned) (alt_needs f)
                | None -> true)
            | _ -> true)
          cands
      in
      match ready with [] -> greatest cands | _ -> greatest ready)
  | _ -> greatest cands

(* An install-if disjunct exists only once its designated condition has
   been selected, so the conditions it discharges on have largely settled
   by the time [choose] sees it.  Deferring it behind every other open
   name settles the rest of them; measured on this index the deferral no
   longer changes the answer, but it is the invariant [choose] wants and
   it costs nothing.  A provider list with conjunctive alternatives waits the
   same way, behind every name but those, since the requirers and triggers
   its [choose] looks for are decided elsewhere. *)
let next ~assigned:_ (opens : (PFR.Name.t * int) list) =
  let rank (tn, _) =
    if is_support tn then 3
    else if is_install_if tn then 2
    else if has_selectable_alts tn then 1
    else 0
  in
  let best =
    List.fold_left
      (fun ((_, br) as b) o ->
        let r = rank o in
        if r < br then (fst o, r) else b)
      (fst (List.hd opens), rank (List.hd opens))
      (List.tl opens)
  in
  fst best

(* ---- the lazy core graph ----------------------------------------------- *)

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
    let i = inst () in
    (match q with
    | Red.Name.Orig n, Red.Version.Orig v -> (
        match Red.supportForm i (n, v) with
        | Some (PF.FDisj (a, b)) ->
            let rec spine f =
              match f with PF.FDisj (x, y) -> x :: spine y | _ -> [ f ]
            in
            support_names :=
              NameMap.add (PFR.Name.Disjunct (a :: spine b)) () !support_names
        | _ -> ())
    | _ -> ());
    let fs = Red.FSet.elements (Red.dependees i q) in
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
          pkg_inst st.ar st.world (n, v))
  | ( PFR.Name.Orig (Red.Name.Orig m),
      PFR.Version.Orig (Red.Version.Prov (q0, pv)) ) ->
      (* Lookup.dependees_lookupProv: an alias reads no instance *)
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
