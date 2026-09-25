(* Every lookup is answered from a small sub-instance in the shape one of
   Alpine.v's lookup theorems justifies.  Trusted here (TCB): PubGrub,
   whose answer is decoded without a check, the parser, the version
   comparator, the preference below, and the plumbing. *)

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
   Alpine writes the switch name (docs, openrc) first and almost nothing
   depends on those, where the least positive condition lands on a name
   most of the archive carries -- so the first-listed positive condition is
   recorded as the set is built, keyed by the element list, which is
   canonical where the set's own representation need not be.  The
   fallback keeps designation total on sets with a positive condition,
   discharging designation_spec: a TCB obligation here, as ApkVerMatch's
   prefix/hash are. *)
let designation_tbl : (Alp.coq_Dep list, Alp.Atom.t) Hashtbl.t =
  Hashtbl.create 4096

let first_pos (ds : Alp.coq_Dep list) : Alp.Atom.t option =
  List.find_map (function Alp.DPos a -> Some a | Alp.DNeg _ -> None) ds

module FirstDesignation = struct
  let designation (conds : Alp.CondSet.t) : Alp.Atom.t option =
    let key = Alp.CondSet.elements conds in
    match Hashtbl.find_opt designation_tbl key with
    | Some _ as a -> a
    | None -> first_pos key
end

module Red = Alp.Reduct (FirstDesignation)
module PF = Red.PF
module PFR = PF.Reduction
module T = PFR.T

(* The world is the demo's goal arguments and nothing else: this resolves
   from an empty root rather than from an existing /etc/apk/world. *)

(* Architecture is fixed by the index that was loaded.  A repository's
   APKINDEX is per-arch, so no A: filtering is applied and no
   cross-arch reasoning is possible here. *)

(* provider_priority is apk's preference among the providers of a name,
   versioned ones included, and preference in this pipeline lives in
   PVersion.compare, which is where its value is applied -- off the
   archive, not off an instance.  Whether it is non-zero also decides
   whether a provides without a version is selected automatically, which
   the calculus reads off inst_prio, so every sub-instance carries the k:
   lines of the packages in its repository. *)

(* replaces (r:/q:) never appears in a repository index -- it is an
   installed-db field -- so inst_repl is empty. *)

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

(* building the set is also where the rule's first-listed positive
   condition is offered to [FirstDesignation]; an earlier rule keeps the
   designation when two rules share a set, so the table does not depend on
   when it is read *)
let condset_of ds =
  let conds = List.map xdep ds in
  let cs = Alp.CondSet.ofList conds in
  (match first_pos conds with
  | Some a ->
      let key = Alp.CondSet.elements cs in
      if not (Hashtbl.mem designation_tbl key) then
        Hashtbl.add designation_tbl key a
  | None -> ());
  cs

type iif_rule = {
  t_pkg : string * string;
  t_conds : Alp.CondSet.t;
  t_designation : Alp.Atom.t;
}

type archive = {
  by_name : (string, P.pkg list) Hashtbl.t;
  meta : (string * string, P.pkg) Hashtbl.t;
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
      pos = Hashtbl.create 16384;
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
      Hashtbl.replace ar.pos (p.P.name, p.P.version) ar.n_pkgs;
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
        (* a rule with no positive condition is left out, and nothing is
           lost -- apk reaches a rule only from an installed
           package bearing or providing a condition's name, which falsifies
           a negated condition unless it is the rule's own package *)
        if List.exists (fun (d : P.dep) -> not d.P.d_neg) p.P.install_if then
          iifs := ((p.P.name, p.P.version), condset_of p.P.install_if) :: !iifs))
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

let rec nat_of_int (k : int) : E.nat =
  if k <= 0 then E.O else E.S (nat_of_int (k - 1))

(* repoPreimage and provPreimage, built from the archive's tables rather than by
   filtering a whole-archive instance, which is the only reason a
   per-lookup sub-instance is cheap.  Lookup.subInst's inst_prio is the k:
   lines of its repository. *)
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
  let prio =
    List.filter_map
      (fun q ->
        match Hashtbl.find_opt ar.prio q with
        | Some k -> Some (q, nat_of_int k)
        | None -> None)
      !repo
  in
  (Alp.PkgSet.ofList !repo, Alp.Prov.ofList !prov, Alp.Prio.ofList prio)

(* Lookup.nameSubInst *)
let name_inst ar (n : string) : Alp.coq_Inst =
  let repo, prov, prio = preimages_at ar [ n ] in
  { empty_inst with Alp.inst_repo = repo; inst_prov = prov; inst_prio = prio }

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
   and the world, which names the providers without k: it lets be selected *)
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
                 (List.map
                    (function Alp.DPos (m, _) | Alp.DNeg (m, _) -> m)
                    (Alp.CondSet.elements (Red.condRest r.t_conds)))
                 acc)
          (List.map (fun (d : P.dep) -> d.P.d_name) m.P.depends)
          rules
      in
      let repo, prov, prio = preimages_at ar ns in
      let deps =
        Alp.Deps.ofList (List.map (fun d -> ((n, v), xdep d)) m.P.depends)
      in
      {
        empty_inst with
        Alp.inst_repo = repo;
        inst_deps = deps;
        inst_prov = Alp.Prov.union prov own;
        inst_installIf =
          Alp.InstallIf.ofList (List.map (fun r -> (r.t_pkg, r.t_conds)) rules);
        (* apk also takes a k:-less one whose owner has a requirer (solver.c:381) *)
        inst_world = Alp.WSet.ofList (List.map xdep world);
        inst_prio = prio;
      }

(* Lookup.rootSubInst: the world set and the repository at the names it
   mentions.  Every install-if rule is carried by a package, so the root
   reads no part of the rule table. *)
let root_inst ar (world : P.dep list) : Alp.coq_Inst =
  let repo, prov, prio =
    preimages_at ar (List.map (fun (d : P.dep) -> d.P.d_name) world)
  in
  {
    empty_inst with
    Alp.inst_repo = repo;
    inst_prov = prov;
    inst_world = Alp.WSet.ofList (List.map xdep world);
    inst_prio = prio;
  }

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
let lone_provider (f : PF.coq_Formula) : (string * string) option =
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

let alt_rank ar (last : bool) (f : PF.coq_Formula) : int =
  if last then
    match f with
    | PF.FDep (_, vs) ->
        if PF.VSet.elements vs = [] then rank_none else rank_pkg
    | _ -> rank_none
  else match lone_provider f with Some q -> prov_rank ar q | None -> rank_none

(* PubGrub decides the compare-maximum candidate, so preference lives
   here, and what it has to reproduce is apk's compare_providers over
   the providers of the name being decided.  Against a fresh root and one
   repository its installed-db and pinning keys are dead, and its
   solver-state keys (solver.c:578-595) only rank a provider apk has not
   disqualified -- for an applied constraint it misses, or a dependency
   it can no longer meet -- above one it has, which is left to PubGrub's
   ranges and backtracking.  Of the rest, two are kept, in order, the
   version the provider offers *at the requested name* and then
   provider_priority, with the repository order below both and a single
   repository here.  The one live key between them, the newer version by
   the provider's own name (solver.c:651-661), is omitted: it separates
   only two versions of one package, and an index that lists each
   package once has no such pair.  Past its last key select_package keeps
   the provider it met first, since it takes a later one only when compare_providers
   says strictly better, and it meets them in index order -- so [ord],
   the provider's place in the index, is the final key, and the encoded
   order only keeps the comparison total.

   What a provider offers at a name is its own version where it claims
   the name itself, the p: operand where it is a versioned provides, and
   nothing at all where the provides carries no version.  So a package
   of a name is not privileged over a provider of it: the two are compared
   on the versions they offer, and a provider offering the newer one wins.
   An unversioned provides is the one case where this order puts a real
   package first, and not by privilege either -- it offers no version, and
   no version loses to every version.  provider_priority is read off
   whichever package offers the name, provider or not, and so decides only
   once the offered versions tie.

   A synthetic version selects one alternative of its disjunction by
   position, and which alternative is wanted depends on the disjunction.
   installIfForm lists the negations of the install_if conditions first
   and the augmented package last, so preferring the earliest alternative is
   apk's rule that an install-if fires only when its conditions already hold
   -- without it every install_if rule in the index is discharged by
   installing its target.  encPos folds the versioned provides of a name
   into the name's own version set, where the comparison above settles
   them, and lists only the unversioned providers as separate
   alternatives ahead of it -- so that disjunction is exactly the case
   where the name's own versions rank highest, with k: ordering the
   unversioned providers among themselves.

   The offered version and the k: are carried on the version rather than
   read off it: which disjunction a position belongs to is what decides
   an [Idx], and a comparator sees two versions and not their name.
   Every version PubGrub holds is handed to it by [versions] or by a
   dependency range, both of which know the name, so both tag as they go
   and both fields are a function of the (name, version) pair -- keeping
   this a total order, and one consistent with the tags on any range the
   same name is compared against.

   The absent version every original name has offers nothing at the name
   and is the encoded order's greatest, so it wins wherever it is
   admitted: a name only a negated requirement reaches is left out rather
   than installed. *)
module PVersion = struct
  (* [pv] is the version offered at the name being decided, absent for a
     version that is not a provider candidate at a name (the root, and a
     disjunction's positional [Idx]). *)
  type t = { pv : string option; rank : int; ord : int; v : PFR.Version.t }

  let v (x : t) = x.v
  let bot = { pv = None; rank = 0; ord = max_int; v = PFR.Version.Bot }

  let pp fmt ({ v; _ } : t) =
    match v with
    | PFR.Version.Orig Red.Version.RootV -> Format.fprintf fmt "()"
    | PFR.Version.Orig (Red.Version.Orig s) -> Format.fprintf fmt "%s" s
    | PFR.Version.Orig (Red.Version.Prov ((n, w), pv)) ->
        Format.fprintf fmt "%s=%s(%s-%s)" "provided" pv n w
    | PFR.Version.Idx i -> Format.fprintf fmt "%d" (nat_int i)
    | PFR.Version.Bot -> Format.fprintf fmt "⊥"

  let compare a b =
    match (a.v, b.v) with
    | PFR.Version.Idx _, PFR.Version.Idx _ ->
        let c = Stdlib.compare a.rank b.rank in
        if c <> 0 then c
        else
          let c = Stdlib.compare b.ord a.ord in
          if c <> 0 then c else -r2c (PFR.VersionOT.compare a.v b.v)
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
                if c <> 0 then c else r2c (PFR.VersionOT.compare a.v b.v)
        | _ ->
            let c = r2c (PFR.VersionOT.compare a.v b.v) in
            if c <> 0 then c else Stdlib.compare a.rank b.rank)
end

let ord_of ar (q : string * string) : int =
  match Hashtbl.find_opt ar.pos q with Some i -> i | None -> max_int

let tag ar (tn : PFR.Name.t) (tv : PFR.Version.t) : PVersion.t =
  match (tn, tv) with
  | PFR.Name.Disjunct (f0 :: _ as fs), PFR.Version.Idx i
    when lone_provider f0 <> None -> (
      match alt_at fs i with
      | None -> { PVersion.pv = None; rank = 0; ord = max_int; v = tv }
      | Some (f, last) ->
          let ord =
            match lone_provider f with Some q -> ord_of ar q | None -> max_int
          in
          { PVersion.pv = None; rank = alt_rank ar last f; ord; v = tv })
  | _, PFR.Version.Orig (Red.Version.Prov (q, pv)) ->
      { PVersion.pv = Some pv; rank = prio_of ar q; ord = ord_of ar q; v = tv }
  (* a package claiming the name itself offers its own version there *)
  | PFR.Name.Orig (Red.Name.Orig n), PFR.Version.Orig (Red.Version.Orig w) ->
      {
        PVersion.pv = Some w;
        rank = prio_of ar (n, w);
        ord = ord_of ar (n, w);
        v = tv;
      }
  | _ -> { PVersion.pv = None; rank = 0; ord = max_int; v = tv }

let pp_name fmt (n : PFR.Name.t) =
  match n with
  | PFR.Name.Orig m -> pp_alp_name fmt m
  | PFR.Name.Disjunct fs ->
      Format.fprintf fmt "<%a>"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "|")
           (pp_formula 2))
        fs

module L =
  Package_formula.Make (Red.NameOT) (Red.VersionOT) (PF) (PVersion)
    (struct
      let pp_name = pp_name
    end)

module PG = L.PG

(* Lookup.versions_lookupName: what the versions callback answers, before
   the tagging PubGrub sees -- the name's own versions and its provides.
   The encoder reads this at the names a formula negates: a negated
   requirement's complement ranges over the versions offered at the name,
   provides included. *)
let oracle ar (tn : Red.Name.name) : PF.VSet.t =
  match tn with
  | Red.Name.Orig n -> Red.versions (name_inst ar n) n
  | Red.Name.Root -> PF.VSet.singleton Red.Version.RootV

let lookups ar : L.t =
  L.create ~root:(Red.Name.Root, Red.Version.RootV) ~tag:(tag ar)
    ~oracle:(oracle ar) ()

let dependees inst q = Red.FSet.elements (Red.dependees inst q)

let touch ar world st ((tn, tv) : T.Pkg.t) =
  match (tn, tv) with
  | PFR.Name.Orig Red.Name.Root, PFR.Version.Orig Red.Version.RootV ->
      (* Lookup.dependees_lookupRoot *)
      L.process st Red.rootPkg (fun () ->
          dependees (root_inst ar world) Red.rootPkg)
  | PFR.Name.Orig (Red.Name.Orig n), PFR.Version.Orig (Red.Version.Orig v) ->
      (* Lookup.dependees_lookupOrig *)
      let q = (Red.Name.Orig n, Red.Version.Orig v) in
      L.process st q (fun () -> dependees (pkg_inst ar world (n, v)) q)
  | ( PFR.Name.Orig (Red.Name.Orig m),
      PFR.Version.Orig (Red.Version.Prov (q0, pv)) ) ->
      (* Lookup.dependees_lookupProv: a provides reads no instance *)
      let q = (Red.Name.Orig m, Red.Version.Prov (q0, pv)) in
      L.process st q (fun () -> dependees empty_inst q)
  | _ -> ()

