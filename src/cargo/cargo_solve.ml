(* Cargo solving over the verified pipeline, deb_solve/opam_solve-style:
   the index is parsed into hashtables a crate at a time, as the solver
   first asks for each; every lookup is answered from a small
   sub-instance in the shape one of Cargo.v's lookup theorems justifies
   (own fibres, and the repository restricted to the names those fibres
   read, or to a link's declarers), pushed through the Cargo encoder straight to
   Core; PubGrub solves the accumulated core graph lazily and the solution
   comes back through the proved decoders.  Trusted here (TCB): the parser,
   the version comparator, the policy defaults below, and the plumbing. *)

module E = Pac
module P = Cargo_parse

let c2r c = if c < 0 then E.Lt else if c > 0 then E.Gt else E.Eq
let r2c = function E.Lt -> -1 | E.Eq -> 0 | E.Gt -> 1

module StringOT = struct
  type t = string

  let compare a b = c2r (String.compare a b)
  let eq_dec (a : string) b = String.equal a b
end

module CVerOT = struct
  type t = string

  let compare a b = c2r (Cargo_version.compare a b)
  let eq_dec a b = Cargo_version.compare a b = 0
end

(* SemverMatch: the two tests V.compare cannot express.  Both take the
   candidate version first and the comparator's constant second. *)
module PM = struct
  let isPre = Cargo_version.is_prerelease
  let sameCore = Cargo_version.same_core
end

(* ---- policy defaults ---------------------------------------------------

   Each is a decision the calculus leaves to the frontend; none is forced
   by the theory, and each is a place where this driver may disagree with
   cargo. *)

(* the feature every dependency requests unless it opts out with
   default-features = false *)
let default_feature = "default"

(* rootFeats when the caller names no features: every key of the root
   crate's own feature table, which is the instantiation Cargo.lock is.
   Cargo resolves twice.  The lock comes from resolve_with_registry, which
   passes CliFeatures::new_all(true) and HasDevUnits::Yes, and
   build_requirements turns all_features into require_feature for each key
   of the root summary's feature map; with_implicit_features has already
   put an optional dependency's implicit feature into that table, so every
   optional row the root declares is reachable.  The build is a second
   resolve handed the lock, so it is the same versions filtered by the
   features actually asked for -- which is what --features selects here.

   The flag reaches workspace members only: ws.members_with_features
   hands CliFeatures to the root alone, and every other summary arrives as
   RequestedFeatures::DepFeatures carrying whatever its declaring row
   asked for, past resolve_features' [if dep.is_optional() && !reqs.deps
   .contains_key(..) { continue }].  So a *transitive* crate's unactivated
   optionals stay out of the lock, which is sOptional's guard, and nothing
   here forces them in. *)
let root_feats (m : P.ver) : string list = List.map fst m.P.v_feats

(* dev dependencies participate only from the root crate: that is
   slotActive's rule in the theory, not a choice made here. *)

(* rustVersion: the toolchain resolver v3 ranks candidates against.  None
   leaves the preference off, which is cargo's own guard -- sort_summaries
   consults msrv_compat_count only under [if !self.rust_versions.is_empty()]
   -- so with no toolchain configured every candidate ties and the order is
   the plain newest-first that v1 and v2 use. *)
let rust_version : string option = None

(* cargo's RustVersion::is_compatible_with: the declared MSRV read as a
   caret requirement and matched against the toolchain with its missing
   components zeroed and any pre-release dropped.  The index writes an
   MSRV as a partial version ("1.71"), and caret expansion is defined on
   exactly that, so nothing has to pad it.

   A crate declaring no MSRV is compatible with every toolchain, not with
   none: msrv_compat_count returns self.rust_versions.len() -- the
   maximum -- when summary.rust_version() is None, so the field's absence
   ranks a candidate up. *)
let msrv_ok (rustc : string) (msrv : string option) : bool =
  match msrv with
  | None -> true
  | Some m ->
      let p = Cargo_version.parse rustc in
      let rustc =
        Printf.sprintf "%d.%d.%d" p.Cargo_version.major p.Cargo_version.minor
          p.Cargo_version.patch
      in
      Cargo_version.holds rustc (Cargo_version.comparator ("^" ^ m))

(* Build and normal edges share one feature-unified graph here.  Resolver
   v2 decouples them, and v3 inherits that, but cargo decouples in
   FeatureResolver, which runs over an already-fixed resolution: it
   decides which features each unit is compiled with and cannot move a
   version.  So the decoupling is not part of what a resolution is, and
   the only half of v3 that reaches version selection is the MSRV
   preference above. *)

(* Pre-release versions stay in the index.  The calculus admits one only
   inside a comparator set that names a pre-release at the same release
   core, so no filtering is needed here; yanked versions are dropped by
   the parser instead, which is a repository fact rather than a policy. *)

(* ---- the archive ---- *)

type archive = {
  index : string;
  crates : (string, P.ver list) Hashtbl.t;
  entry : (string * string, P.ver) Hashtbl.t;
  links_idx : (string, (string * string) list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  (* wall time inside the parser, which the solve now interleaves with *)
  mutable t_parse : float;
}

let empty_archive index =
  {
    index;
    crates = Hashtbl.create 4096;
    entry = Hashtbl.create 65536;
    links_idx = Hashtbl.create 256;
    n_names = 0;
    n_vers = 0;
    t_parse = 0.;
  }

let load_name ar (n : string) : P.ver list =
  match Hashtbl.find_opt ar.crates n with
  | Some vs -> vs
  | None ->
      let t = Unix.gettimeofday () in
      let vs = P.load_crate ~index:ar.index n in
      ar.t_parse <- ar.t_parse +. (Unix.gettimeofday () -. t);
      Hashtbl.replace ar.crates n vs;
      ar.n_names <- ar.n_names + 1;
      ar.n_vers <- ar.n_vers + List.length vs;
      List.iter
        (fun (v : P.ver) ->
          Hashtbl.replace ar.entry (n, v.P.v_vers) v;
          match v.P.v_links with
          | None -> ()
          | Some l ->
              Hashtbl.replace ar.links_idx l
                ((n, v.P.v_vers)
                ::
                (match Hashtbl.find_opt ar.links_idx l with
                | Some x -> x
                | None -> [])))
        vs;
      vs

let versions_of ar n = List.map (fun (v : P.ver) -> v.P.v_vers) (load_name ar n)

(* a manifest is read only through its name's load, so a crate version's
   declarations are never taken from a name parsed in part *)
let meta ar n v : P.ver option =
  ignore (load_name ar n);
  Hashtbl.find_opt ar.entry (n, v)

(* There is no cone pass: a crate is parsed the first time a sub-instance
   reads its name, as cargo's sparse protocol fetches it, so a run touches
   the crates the solver asks about and no others.  Because the instance is
   still being uncovered, the sub-instance a lookup theorem names must be
   complete at the moment the lookup answers.  Cargo.v's Lookup module has
   one theorem per shape asked below, in the components passed here.
   versions_lookup{Crate,FeatP}Sub read the repository, and the support
   relation, at the name alone; versions_lookup{Slot,Decision}Sub and
   dependees_lookup{Crate,FeatP,Slot,Decision}Sub read the owner's fibres
   and the repository at Lookup.reads, the owner's name and its slots'
   targets.  Each of those is complete by construction: name_set,
   support_of_name and repo_preimage load every name they read whole, and
   meta loads the owner.  versions_lookupLinkSub is the exception.  Its
   sub-instance is the preimage of the link relation at l -- every crate
   version declaring l -- and no declaration of any one crate names the
   other declarers, so nothing a loaded crate carries can bring them in:
   links_idx holds the declarers among the names loaded so far, and may
   grow after CLink l has answered.  Make.solve answers it afresh each
   time rather than memoizing it. *)

module Make () = struct
  module Cg =
    E.Cargo (StringOT) (CVerOT) (StringOT) (CVerOT) (StringOT) (StringOT) (PM)

  module T = Cg.T

  (* ---- granularity: at most one version per semver compatibility class,
     the leftmost-nonzero component ----

     The label is the class's least version rather than a tag like "^1",
     and G is ordered as versions are, because the encoding hands PubGrub
     a class where the version would otherwise go: what the solver
     maximises is the label, so an order on labels that disagrees with the
     order on versions silently reverses the preference.  Lexical order on
     "0.9" against "0.10" is exactly that disagreement. *)
  let compat_class (v : string) : string =
    let p = Cargo_version.parse v in
    if p.Cargo_version.major > 0 then Printf.sprintf "%d.0.0" p.Cargo_version.major
    else if p.Cargo_version.minor > 0 then
      Printf.sprintf "0.%d.0" p.Cargo_version.minor
    else Printf.sprintf "0.0.%d" p.Cargo_version.patch

  (* ---- parse-AST -> extracted terms ---- *)

  let xop : Cargo_version.op -> E.cmpOp = function
    | Cargo_version.Ge -> E.OpGe
    | Gt -> E.OpGt
    | Le -> E.OpLe
    | Lt -> E.OpLt
    | Eq -> E.OpEq

  (* a cargo requirement is a single comparator set -- the comma-separated
     conjunction -- which is also the unit the pre-release rule is scoped
     to; the empty set is "*", and admits no pre-release *)
  let xreq (r : Cargo_version.req) : Cg.coq_Range =
    [ List.map (fun (o, v) -> Cg.COp (xop o, v)) r ]

  let xkind : P.kind -> Cg.Kind.t = function
    | P.Normal -> Cg.Kind.KNormal
    | P.Build -> Cg.Kind.KBuild
    | P.Dev -> Cg.Kind.KDev

  let fset_of = Cg.FSet.ofList

  let xentry : P.fentry -> Cg.FEntry.t = function
    | P.FFeat f -> Cg.FEntry.EFeat f
    | P.FDep a -> Cg.FEntry.EDep a
    | P.FDepFeat (a, f) -> Cg.FEntry.EDepFeat (a, f)
    | P.FWeakFeat (a, f) -> Cg.FEntry.EWeakFeat (a, f)

  (* one slot per manifest site -- SiteFunctional -- where the site is
     (cfg, kind, alias): the tables a manifest offers are maps, so two
     records can only collide here if an index entry repeats a site, which
     no manifest can spell.  Conjoining the requirements and unioning the
     requested features is what that unreachable case gets; every real
     repeat of an alias across kinds or cfgs stays its own slot, because
     that is what cargo resolves. *)
  let unify_site (ds : P.dep list) : P.dep =
    let d0 = List.hd ds in
    {
      d0 with
      P.d_req = List.concat_map (fun (d : P.dep) -> d.P.d_req) ds;
      d_feats =
        List.sort_uniq String.compare
          (List.concat_map (fun (d : P.dep) -> d.P.d_feats) ds);
      d_optional = List.for_all (fun (d : P.dep) -> d.P.d_optional) ds;
      d_default = List.exists (fun (d : P.dep) -> d.P.d_default) ds;
    }

  let site_of (d : P.dep) : string * P.kind * string =
    (d.P.d_alias, d.P.d_kind, d.P.d_cfg)

  let slots_of (v : P.ver) : P.dep list =
    let tbl = Hashtbl.create 16 in
    let order = ref [] in
    List.iter
      (fun (d : P.dep) ->
        let k = site_of d in
        if not (Hashtbl.mem tbl k) then order := k :: !order;
        Hashtbl.replace tbl k
          (d :: (match Hashtbl.find_opt tbl k with Some l -> l | None -> [])))
      v.P.v_deps;
    List.map
      (fun k -> unify_site (List.rev (Hashtbl.find tbl k)))
      (List.rev !order)

  (* -- per-crate fibres: Lookup's SlotFibred/LinkFibred/SupportFibred
     .tailFibre and fdefFibre at (n, v), and Lookup.reads -- *)

  type fibres = {
    r_slots : Cg.SlotRel.t;
    r_fdefs : Cg.FDefRel.t;
    r_links : Cg.LinkRel.t;
    r_supp : Cg.SupportSet.t;
    r_reads : string list; (* own name plus the slot targets *)
  }

  let empty_fibres n =
    {
      r_slots = Cg.SlotRel.empty;
      r_fdefs = Cg.FDefRel.empty;
      r_links = Cg.LinkRel.empty;
      r_supp = Cg.SupportSet.empty;
      r_reads = [ n ];
    }

  let slot_data (d : P.dep) : Cg.SlotData.t =
    ( d.P.d_alias,
      ( d.P.d_target,
        ( xreq d.P.d_req,
          ( xkind d.P.d_kind,
            ( d.P.d_optional,
              (d.P.d_default, (fset_of d.P.d_feats, (d.P.d_cfg, "registry"))) )
          ) ) ) )

  let fibres_cache : (string * string, fibres) Hashtbl.t = Hashtbl.create 4096

  let fibres_of ar (p : string * string) : fibres =
    match Hashtbl.find_opt fibres_cache p with
    | Some r -> r
    | None ->
        let n, v = p in
        let r =
          match meta ar n v with
          | None -> empty_fibres n
          | Some m ->
              let ds = slots_of m in
              let slots =
                Cg.SlotRel.ofList (List.map (fun d -> (p, slot_data d)) ds)
              in
              let fdefs =
                Cg.FDefRel.ofList
                  (List.concat_map
                     (fun (f, es) -> List.map (fun e -> ((p, f), xentry e)) es)
                     m.P.v_feats)
              in
              let supp =
                Cg.SupportSet.ofList
                  (List.map (fun (f, _) -> (p, f)) m.P.v_feats)
              in
              let links =
                match m.P.v_links with
                | None -> Cg.LinkRel.empty
                | Some l -> Cg.LinkRel.add (p, l) Cg.LinkRel.empty
              in
              {
                r_slots = slots;
                r_fdefs = fdefs;
                r_links = links;
                r_supp = supp;
                r_reads =
                  List.sort_uniq String.compare
                    (n :: List.map (fun (d : P.dep) -> d.P.d_target) ds);
              }
        in
        Hashtbl.replace fibres_cache p r;
        r

  (* ---- repository preimages ---- *)

  let name_set_cache : (string, Cg.PkgSet.t) Hashtbl.t = Hashtbl.create 4096

  let name_set ar (n : string) : Cg.PkgSet.t =
    match Hashtbl.find_opt name_set_cache n with
    | Some s -> s
    | None ->
        let s =
          Cg.PkgSet.ofList (List.map (fun v -> (n, v)) (versions_of ar n))
        in
        Hashtbl.replace name_set_cache n s;
        s

  (* every version of every name the crate's fibres read, and nothing else *)
  (* keyed by the read names rather than by the crate version, because
     consecutive versions of a crate almost always read the same names *)
  let repo_preimage_cache : (string list, Cg.PkgSet.t) Hashtbl.t =
    Hashtbl.create 4096

  let repo_preimage ar (p : string * string) : Cg.PkgSet.t =
    let reads = (fibres_of ar p).r_reads in
    match Hashtbl.find_opt repo_preimage_cache reads with
    | Some s -> s
    | None ->
        let s = Cg.PkgSet.unions (List.map (name_set ar) reads) in
        Hashtbl.replace repo_preimage_cache reads s;
        s

  (* ---- the lazy core graph ---- *)

  type state = {
    ar : archive;
    rc : string * string;
    rfeats : Cg.FSet.t;
    rustv : string option;
  }

  let mk_state ar rc rfeats rustv =
    { ar; rc; rfeats = fset_of rfeats; rustv }

  (* ---- the per-name version lookups ---- *)

  let link_preimage st (l : string) =
    match Hashtbl.find_opt st.ar.links_idx l with Some x -> x | None -> []

  let msrv_cache : (string * string * string, bool) Hashtbl.t =
    Hashtbl.create 65536

  let crate_msrv_ok st (rustc : string) ((n, v) : string * string) : bool =
    match Hashtbl.find_opt msrv_cache (rustc, n, v) with
    | Some b -> b
    | None ->
        let b =
          match meta st.ar n v with
          | None -> true
          | Some m -> msrv_ok rustc m.P.v_msrv
        in
        Hashtbl.replace msrv_cache (rustc, n, v) b;
        b

  (* the support relation at a name -- Lookup.supportPreimage at {n},
     which versions_lookupFeatPSub reads -- as the union of its versions'
     fibres.  Cached for the same reason name_set is: load_name takes a
     name whole, so this cannot grow once it has been asked. *)
  let support_cache : (string, Cg.SupportSet.t) Hashtbl.t = Hashtbl.create 4096

  let support_of_name st (n : string) : Cg.SupportSet.t =
    match Hashtbl.find_opt support_cache n with
    | Some s -> s
    | None ->
        let s =
          Cg.SupportSet.unions
            (List.map
               (fun (v : P.ver) -> (fibres_of st.ar (n, v.P.v_vers)).r_supp)
               (load_name st.ar n))
        in
        Hashtbl.replace support_cache n s;
        s

  (* one branch per versions_lookup{Root,Crate,FeatP,Slot,Decision,Link}Sub,
     each passing the components its theorem names and nothing else *)
  let versions st (tn : Cg.NPlus.t) : Cg.VPlus.t list =
    let call r supp fdefs slots links =
      T.VSet.elements
        (Cg.versions compat_class r supp fdefs slots links st.rc tn)
    in
    let none = Cg.PkgSet.empty in
    let nosupp = Cg.SupportSet.empty in
    let nofd = Cg.FDefRel.empty in
    let nosl = Cg.SlotRel.empty in
    let nolk = Cg.LinkRel.empty in
    match tn with
    | Cg.NPlus.CRoot -> call none nosupp nofd nosl nolk
    | Cg.NPlus.CCrate (n, _) -> call (name_set st.ar n) nosupp nofd nosl nolk
    | Cg.NPlus.CFeatP (n, _, _) ->
        call (name_set st.ar n) (support_of_name st n) nofd nosl nolk
    | Cg.NPlus.CSlot (n, v, _) ->
        let rw = fibres_of st.ar (n, v) in
        call (repo_preimage st.ar (n, v)) nosupp nofd rw.r_slots nolk
    | Cg.NPlus.CDec (n, v, _, _, _) ->
        let rw = fibres_of st.ar (n, v) in
        call (repo_preimage st.ar (n, v)) nosupp rw.r_fdefs rw.r_slots nolk
    | Cg.NPlus.CLink l ->
        (* Lookup.claimants and LinkFibred.headFibre at l, over the
           declarers loaded so far; see the note above Make *)
        let rs = link_preimage st l in
        let r =
          Cg.PkgSet.ofList
            (List.filter (fun (n, v) -> meta st.ar n v <> None) rs)
        in
        call r nosupp nofd nosl (Cg.LinkRel.ofList (List.map (fun q -> (q, l)) rs))

  (* one branch per dependees_lookup{Root,Crate,FeatP,Slot,Decision}Sub,
     with the request (rc, rootFeats, default) carried whole as the
     theorems carry it; the fall-through is dependees_lookupInert, empty *)
  let deps st (p : T.Pkg.t) : T.Dependees.t list =
    let call r supp fdefs slots links =
      T.DependeesSet.elements
        (Cg.dependees compat_class r supp fdefs slots links
           default_feature st.rc st.rfeats p)
    in
    let none = Cg.PkgSet.empty in
    let nosupp = Cg.SupportSet.empty in
    let nofd = Cg.FDefRel.empty in
    let nosl = Cg.SlotRel.empty in
    let nolk = Cg.LinkRel.empty in
    let owner n v k =
      let rw = fibres_of st.ar (n, v) in
      k (repo_preimage st.ar (n, v)) rw
    in
    match (fst p, snd p) with
    | Cg.NPlus.CRoot, _ -> call none nosupp nofd nosl nolk
    | Cg.NPlus.CCrate (n, _), Cg.VPlus.WOrig v ->
        owner n v (fun r rw -> call r nosupp nofd rw.r_slots rw.r_links)
    | Cg.NPlus.CFeatP (n, _, _), Cg.VPlus.WOrig v ->
        owner n v (fun r rw -> call r rw.r_supp rw.r_fdefs rw.r_slots nolk)
    | Cg.NPlus.CSlot (n, v, _), Cg.VPlus.WClass _ ->
        owner n v (fun r rw -> call r nosupp nofd rw.r_slots nolk)
    | Cg.NPlus.CDec (n, v, _, _, _), Cg.VPlus.WClass _ ->
        owner n v (fun r rw -> call r nosupp rw.r_fdefs rw.r_slots nolk)
    | _, _ -> []

  (* the crate versions a slot node's class stands for: its own edges
     already carry them -- CSlot points at CCrate/CFeatP with the members
     of the class the requirement admits, and CDec at CFeatP with the same
     set -- so reading them back off dependees asks the encoder rather
     than re-evaluating a requirement here, and cannot drift from what
     choosing the class actually offers *)
  let class_members st (tn : Cg.NPlus.t) (w : Cg.VPlus.t) :
      (string * string) list =
    List.concat_map
      (fun ((m, vs) : T.Dependees.t) ->
        match m with
        | Cg.NPlus.CCrate (t, _) | Cg.NPlus.CFeatP (t, _, _) ->
            List.filter_map
              (function Cg.VPlus.WOrig v -> Some (t, v) | _ -> None)
              (T.VSet.elements vs)
        | _ -> [])
      (deps st (tn, w))

  (* a slot node is one manifest site, so its name has to spell the site
     out: bare alias for the plain [dependencies] row, and the kind or cfg
     that told the row apart otherwise *)
  let pp_site fmt ((a, (k, cfg)) : Cg.SlotKey.t) =
    Format.fprintf fmt "%s%s%s" a
      (match k with
      | Cg.Kind.KNormal -> ""
      | Cg.Kind.KBuild -> "[build]"
      | Cg.Kind.KDev -> "[dev]")
      (if cfg = "" then "" else "[" ^ cfg ^ "]")

  module PName = struct
    type t = Cg.NPlus.t

    let compare a b = r2c (Cg.NPlus.compare a b)

    let pp fmt (tn : t) =
      match tn with
      | Cg.NPlus.CRoot -> Format.fprintf fmt "root"
      | Cg.NPlus.CCrate (n, gr) -> Format.fprintf fmt "%s@%s" n gr
      | Cg.NPlus.CFeatP (n, f, gr) -> Format.fprintf fmt "%s/%s@%s" n f gr
      | Cg.NPlus.CSlot (n, v, k) ->
          Format.fprintf fmt "%s@%s->%a" n v pp_site k
      | Cg.NPlus.CDec (n, v, f, k, feat) ->
          Format.fprintf fmt "<%s@%s/%s=>%a/%s>" n v f pp_site k feat
      | Cg.NPlus.CLink l -> Format.fprintf fmt "links:%s" l
  end

  module PVersion = struct
    type t = { msrv : bool; v : Cg.VPlus.t }

    let compare a b =
      match (a.msrv, b.msrv) with
      | false, true -> -1
      | true, false -> 1
      | _ -> r2c (Cg.VPlus.compare a.v b.v)

    let pp fmt ({ v; _ } : t) =
      match v with
      | Cg.VPlus.WUnit -> Format.fprintf fmt "()"
      | Cg.VPlus.WOrig x -> Format.fprintf fmt "%s" x
      | Cg.VPlus.WClass gr -> Format.fprintf fmt "class:%s" gr
      | Cg.VPlus.WName n -> PName.pp fmt n
  end

  module PG = Pubgrub.Make (PName) (PVersion)

  type result = {
    crates : (string * string) list;
    feats : (string * string * string list) list;
    (* the parent relation, keyed in the theory by manifest site: one
       crate may depend on a single crate name twice -- under two aliases
       through a rename, or under one alias from two sites -- and the
       copies may land on different compatibility classes, so the edge has
       to record which declaration received which version.  ParentElt
       carries only the target's version, since the site already
       determines the slot it came through; the target name is read back
       off that slot here, and the alias is what is reported, because a
       consumer comparing against cargo's (depender, dependee) edges has
       no other way to name the crate the version belongs to and no notion
       of a site at all.
       (owner, owner version, alias, target name, target version) *)
    parents : (string * string * string * string * string) list;
    nodes : int;
    processed : int;
  }

  let solve ?(debug = false) ?rfeats ?(rustv = rust_version) ar
      (rc : string * string) =
    Pubgrub.set_debug debug;
    let rfeats =
      match rfeats with
      | Some fs -> fs
      | None -> (
          match meta ar (fst rc) (snd rc) with
          | None -> []
          | Some m -> root_feats m)
    in
    let st = mk_state ar rc rfeats rustv in
    (* A class is compatible when it still offers a crate version the
       toolchain can build, not when all of its versions do: cargo ranks
       the candidate versions themselves, so a class holding one buildable
       version is a choice it makes without hesitation, and demanding every
       member be buildable would demote exactly those classes.  Holding
       this per (name, class) also keeps the tag a function of the version
       it labels, which is what makes it a preference: two PVersion.t with
       the same v always carry the same flag, so no candidate is added or
       dropped anywhere and only the order over them moves. *)
    let class_cache = Hashtbl.create 4096 in
    let class_msrv_ok rustc (tn : Cg.NPlus.t) (w : Cg.VPlus.t) : bool =
      match Hashtbl.find_opt class_cache (tn, w) with
      | Some b -> b
      | None ->
          let ms = class_members st tn w in
          let b = ms = [] || List.exists (crate_msrv_ok st rustc) ms in
          Hashtbl.replace class_cache (tn, w) b;
          b
    in
    (* the preference must land on every name whose candidates stand for
       concrete crate versions, not just the crate name.  CFeatP also
       carries WOrig, and whichever of the two families is decided first
       entails the other, so a family left untagged decides by bare semver
       and the demotion never acts.  CSlot and CDec carry WClass, and a
       class is where the choice between semver-incompatible versions of
       one crate is actually made -- 0.60 against 0.61 is a different name,
       so ranking versions within a name can never reach it.  Only CRoot
       and CLink, whose candidates are not crate versions at all, have no
       standing. *)
    let tag (tn : Cg.NPlus.t) (w : Cg.VPlus.t) : PVersion.t =
      match (st.rustv, tn, w) with
      | ( Some rustc,
          (Cg.NPlus.CCrate (n, _) | Cg.NPlus.CFeatP (n, _, _)),
          Cg.VPlus.WOrig v ) ->
          { PVersion.msrv = crate_msrv_ok st rustc (n, v); v = w }
      | ( Some rustc,
          (Cg.NPlus.CSlot (_, _, _) | Cg.NPlus.CDec (_, _, _, _, _)),
          Cg.VPlus.WClass _ ) ->
          { PVersion.msrv = class_msrv_ok rustc tn w; v = w }
      | _ -> { PVersion.msrv = true; v = w }
    in
    (* the tagged list, not just the untagged one, has to be memoized:
       PubGrub asks a name for its versions at every propagation step.
       CLink l is the one name that cannot be held: its versions are the
       whole preimage of the link relation at l (versions_lookupLinkSub),
       and no declaration of any one declarer names the others, so
       links_idx holds only the declarers among the names loaded so far
       and may grow after CLink l has answered.  Recomputing the filter --
       a handful of entries -- lets a declarer loaded later simply be
       there, where a cache would freeze the answer mid-run and refuse it
       against a set fixed without it. *)
    let vcache = Hashtbl.create 65536 in
    let versions tn =
      match Hashtbl.find_opt vcache tn with
      | Some vs -> vs
      | None ->
          let vs = List.map (tag tn) (versions st tn) in
          (match tn with
          | Cg.NPlus.CLink _ -> ()
          | _ -> Hashtbl.replace vcache tn vs);
          vs
    in
    (* the decisive memoization: PubGrub asks for the same node's
       dependencies over and over during propagation *)
    let dcache = Hashtbl.create 65536 in
    let dependencies tn ({ PVersion.v = w; _ } : PVersion.t) =
      match Hashtbl.find_opt dcache (tn, w) with
      | Some r -> r
      | None ->
          let r =
            List.map
              (fun ((m, vs) : T.Dependees.t) ->
                ( m,
                  PG.Ranges.of_list
                    (List.map (tag m) (T.VSet.elements vs)) ))
              (deps st (tn, w))
          in
          Hashtbl.replace dcache (tn, w) r;
          r
    in
    match
      PG.solve ~vers:versions ~deps:dependencies
        [ ( Cg.NPlus.CRoot,
            PG.Ranges.of_list [ tag Cg.NPlus.CRoot Cg.VPlus.WUnit ] )
        ]
    with
    | Error inc ->
        Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
        None
    | Ok sol ->
        let sol =
          List.map
            (fun ((tn, { PVersion.v; _ }) : Cg.NPlus.t * PVersion.t) -> (tn, v))
            sol
        in
        let s = T.PkgSet.ofList sol in
        (* back through the proved decoders *)
        let crates = Cg.PkgSet.elements (Cg.decodeS s) in
        (* the placeholder default the parser gives a crate declaring none
           keeps a depender's default-features request satisfiable; cargo
           records no such feature (dep_cache.rs, handle_default requires
           the key), so Resolve::features has it only where the manifest
           does, and the reported set follows *)
        let feats =
          List.map
            (fun (((n, v), fs) : Cg.Featured.t) ->
              let fs = Cg.FSet.elements fs in
              let fs =
                match meta ar n v with
                | Some m when not m.P.v_default_declared ->
                    List.filter (fun f -> f <> default_feature) fs
                | _ -> fs
              in
              (n, v, fs))
            (Cg.FeaturedSet.elements (Cg.decodeFS s))
        in
        (* decodeParents is the one decoder that reads the instance, and a
           lazy run has no global relation to hand it; the fibres of the
           crates it decodes are all it looks at, since it reads Slots and
           FDefs only at the owner a slot node names and keeps the node
           only when that owner is decoded *)
        let fibres = List.map (fibres_of st.ar) (st.rc :: crates) in
        let slots = Cg.SlotRel.unions (List.map (fun r -> r.r_slots) fibres) in
        let fdefs = Cg.FDefRel.unions (List.map (fun r -> r.r_fdefs) fibres) in
        (* site -> target name, over the same slots decodeParents reads.
           The site and not the alias, because a rename may point two
           sites sharing an alias at different crates *)
        let target_of = Hashtbl.create 256 in
        List.iter
          (fun ((n, v) as p) ->
            match meta st.ar n v with
            | None -> ()
            | Some m ->
                List.iter
                  (fun (d : P.dep) ->
                    Hashtbl.replace target_of (p, site_of d) d.P.d_target)
                  (slots_of m))
          (st.rc :: crates);
        let parents =
          List.map
            (fun ((((n, v), (a, (k, cfg))), u) : Cg.ParentElt.t) ->
              let k =
                match k with
                | Cg.Kind.KNormal -> P.Normal
                | Cg.Kind.KBuild -> P.Build
                | Cg.Kind.KDev -> P.Dev
              in
              let t =
                match Hashtbl.find_opt target_of ((n, v), (a, k, cfg)) with
                | Some t -> t
                | None -> a
              in
              (n, v, a, t, u))
            (Cg.ParentRel.elements
               (Cg.decodeParents fdefs slots st.rc s))
        in
        Some
          {
            crates = List.sort compare crates;
            feats;
            parents;
            nodes = List.length sol;
            (* the crate versions whose manifests became encoded fibres *)
            processed = Hashtbl.length fibres_cache;
          }
end
