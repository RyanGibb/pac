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
   relation, at the name alone; dependees_lookup{Crate,FeatP}Sub read the
   owner's fibres and the repository at Lookup.reads, the owner's name and
   its slots' targets; and a slot or decision name carries the dependency
   it stands for, so {versions,dependees}_lookup{Slot,Decision}Sub read the
   repository at that dependency's target and the fibres of one version of
   the owner's class declaring it, found by scanning the owner's index
   entry.  Each of those is complete by construction: name_set,
   support_of_name and repo_preimage load every name they read whole, and
   meta and the witness scan load the owner.
   versions_lookupLinkSub is the exception.  Its
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
  let class_of = Hashtbl.create 65536

  let compat_class (v : string) : string =
    match Hashtbl.find_opt class_of v with
    | Some c -> c
    | None ->
        let p = Cargo_version.parse v in
        let c =
          if p.Cargo_version.major > 0 then
            Printf.sprintf "%d.0.0" p.Cargo_version.major
          else if p.Cargo_version.minor > 0 then
            Printf.sprintf "0.%d.0" p.Cargo_version.minor
          else Printf.sprintf "0.0.%d" p.Cargo_version.patch
        in
        Hashtbl.add class_of v c;
        c

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

  (* the manifest record a slot name's dependency came from, for choose's
     walk over its candidates: the name carries the dependency but not the
     parsed requirement the comparator reads *)
  let dep_of_data : (Cg.SlotData.t, P.dep) Hashtbl.t = Hashtbl.create 4096

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
                Cg.SlotRel.ofList
                  (List.map
                     (fun d ->
                       let sd = slot_data d in
                       Hashtbl.replace dep_of_data sd d;
                       (p, sd))
                     ds)
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

  (* the witness versions_lookup{Slot,Decision}Sub name: a version of n in
     class gr whose own declarations make the name, found by scanning n's
     index entry, which holds every version of n and is loaded whole.  With
     none, the empty fibres stand for slot_declines and decision_declines:
     nothing in the instance makes the name, and the lookup declines. *)
  let witness_cache :
      ( [ `Slot of string * string * Cg.SlotData.t
        | `Dec of string * string * string * Cg.SlotData.t * string ],
        Cg.SlotRel.t * Cg.FDefRel.t )
      Hashtbl.t =
    Hashtbl.create 4096

  let witness st key (ok : string * string -> fibres -> bool) n gr =
    match Hashtbl.find_opt witness_cache key with
    | Some r -> r
    | None ->
        let r =
          match
            List.find_map
              (fun v ->
                if compat_class v = gr then
                  let rw = fibres_of st.ar (n, v) in
                  if ok (n, v) rw then Some rw else None
                else None)
              (versions_of st.ar n)
          with
          | Some rw -> (rw.r_slots, rw.r_fdefs)
          | None -> (Cg.SlotRel.empty, Cg.FDefRel.empty)
        in
        Hashtbl.replace witness_cache key r;
        r

  let slot_witness st n gr d =
    fst
      (witness st (`Slot (n, gr, d))
         (fun p rw ->
           Cg.SlotRel.mem (p, d) rw.r_slots && Cg.slotActive st.rc p d)
         n gr)

  let dec_witness st n gr f d feat =
    witness st (`Dec (n, gr, f, d, feat))
      (fun p rw ->
        Cg.SlotRel.mem (p, d) rw.r_slots
        && Cg.slotActive st.rc p d
        && List.exists
             (fun (((_, f'), e) : Cg.FDefElt.t) ->
               f' = f && Cg.entryFeatD e = Some (Cg.sAlias d, feat))
             (Cg.FDefRel.elements rw.r_fdefs))
      n gr

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
    | Cg.NPlus.CSlot (n, gr, d) ->
        call (name_set st.ar (Cg.sTarget d)) nosupp nofd
          (slot_witness st n gr d) nolk
    | Cg.NPlus.CDec (n, gr, f, d, feat) ->
        let sl, fd = dec_witness st n gr f d feat in
        call (name_set st.ar (Cg.sTarget d)) nosupp fd sl nolk
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
    | Cg.NPlus.CSlot (n, gr, d), Cg.VPlus.WClass _ ->
        call (name_set st.ar (Cg.sTarget d)) nosupp nofd
          (slot_witness st n gr d) nolk
    | Cg.NPlus.CDec (n, gr, f, d, feat), Cg.VPlus.WClass _ ->
        let sl, fd = dec_witness st n gr f d feat in
        call (name_set st.ar (Cg.sTarget d)) nosupp fd sl nolk
    | _, _ -> []

  let site_key (d : P.dep) : Cg.SlotKey.t =
    (d.P.d_alias, (xkind d.P.d_kind, d.P.d_cfg))

  (* the dependency the owner's fibre holds at a site, which is what a slot
     name carries: the order replay reads raw manifest rows, which
     unify_site has not merged, so the name is taken from the fibre *)
  let site_data_cache = Hashtbl.create 4096

  let site_data ar (p : string * string) (k : Cg.SlotKey.t) =
    match Hashtbl.find_opt site_data_cache (p, k) with
    | Some sd -> sd
    | None ->
        let sd =
          List.find_map
            (fun ((_, sd) : Cg.SlotElt.t) ->
              if Cg.sKey sd = k then Some sd else None)
            (Cg.SlotRel.elements (fibres_of ar p).r_slots)
        in
        Hashtbl.replace site_data_cache (p, k) sd;
        sd

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

  (* the requirement a slot name carries, since versions of one class may
     declare one site differently and so have distinct slots *)
  let pp_req fmt (d : Cg.SlotData.t) =
    let op = function
      | E.OpGe -> ">="
      | E.OpGt -> ">"
      | E.OpLe -> "<="
      | E.OpLt -> "<"
      | E.OpEq -> "="
      | E.OpNe -> "!="
    in
    Format.fprintf fmt "(%s)"
      (String.concat "||"
         (List.map
            (fun cs ->
              String.concat ","
                (List.map
                   (function Cg.CAny -> "*" | Cg.COp (o, v) -> op o ^ v)
                   cs))
            (Cg.sReq d)))

  module PName = struct
    type t = Cg.NPlus.t

    let compare a b = r2c (Cg.NPlus.compare a b)

    let pp fmt (tn : t) =
      match tn with
      | Cg.NPlus.CRoot -> Format.fprintf fmt "root"
      | Cg.NPlus.CCrate (n, gr) -> Format.fprintf fmt "%s@%s" n gr
      | Cg.NPlus.CFeatP (n, f, gr) -> Format.fprintf fmt "%s/%s@%s" n f gr
      | Cg.NPlus.CSlot (n, gr, d) ->
          Format.fprintf fmt "%s@%s->%a%a" n gr pp_site (Cg.sKey d) pp_req d
      | Cg.NPlus.CDec (n, gr, f, d, feat) ->
          Format.fprintf fmt "<%s@%s/%s=>%a%a/%s>" n gr f pp_site (Cg.sKey d)
            pp_req d feat
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
    let named = rfeats in
    let rfeats =
      match rfeats with
      | Some fs -> fs
      | None -> (
          match meta ar (fst rc) (snd rc) with
          | None -> []
          | Some m -> root_feats m)
    in
    let st = mk_state ar rc rfeats rustv in
    (* the preference must land on both names whose candidates are crate
       versions: CFeatP carries WOrig as CCrate does, and whichever of the
       two is decided first entails the other, so a family left untagged
       decides by bare semver and the demotion never acts.  A class, which
       CSlot and CDec carry, has no standing: cargo ranks the versions a
       dependency admits and not their classes, and which class the ranked
       walk lands on depends on what is already activated, which only
       choose below can see. *)
    let tag (tn : Cg.NPlus.t) (w : Cg.VPlus.t) : PVersion.t =
      match (st.rustv, tn, w) with
      | ( Some rustc,
          (Cg.NPlus.CCrate (n, _) | Cg.NPlus.CFeatP (n, _, _)),
          Cg.VPlus.WOrig v ) ->
          { PVersion.msrv = crate_msrv_ok st rustc (n, v); v = w }
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
    let decided assigned x =
      match assigned x with PG.Decided v -> Some v | _ -> None
    in
    let decided_v assigned x =
      Option.map (fun (pv : PVersion.t) -> pv.PVersion.v) (decided assigned x)
    in
    let is_open assigned x =
      match assigned x with PG.Entailed _ -> true | _ -> false
    in
    (* what the registry query returns for one dependency record, in the
       order sort_summaries leaves it (version_prefs.rs): MSRV-compatible
       first when a toolchain is set, newest first within each.  The
       requirement is read by the comparator the encoding is handed through
       xreq, so these are the members of the classes the slot offers. *)
    let cand_cache = Hashtbl.create 4096 in
    let candidates (d : P.dep) =
      let key = (d.P.d_target, d.P.d_req) in
      match Hashtbl.find_opt cand_cache key with
      | Some us -> us
      | None ->
          let fits u =
            match st.rustv with
            | None -> true
            | Some r -> crate_msrv_ok st r (d.P.d_target, u)
          in
          let us =
            List.stable_sort
              (fun a b ->
                match (fits a, fits b) with
                | true, false -> -1
                | false, true -> 1
                | _ -> Cargo_version.compare b a)
              (List.filter
                 (fun u -> Cargo_version.holds u d.P.d_req)
                 (versions_of ar d.P.d_target))
          in
          Hashtbl.replace cand_cache key us;
          us
    in
    let enabled_cache = Hashtbl.create 4096 in
    let enabled_deps t u feats default =
      let key = (t, u, Cargo_order.SS.elements feats, default) in
      match Hashtbl.find_opt enabled_cache key with
      | Some ds -> ds
      | None ->
          let ds =
            match meta ar t u with
            | None -> []
            | Some m ->
                let _, deps =
                  Cargo_order.requirements m ~all:false feats default
                in
                Cargo_order.enabled ~root:false m deps
          in
          Hashtbl.replace enabled_cache key ds;
          ds
    in
    (* RemainingCandidates::next (core/resolver/mod.rs): a candidate is
       valid unless its class is activated at another version or another
       crate holds its links key.  That is a rule over the partial
       solution, and it is where resolver v3's ranking of versions meets
       the classes a slot decides between.  The partial solution stands
       still for the length of one lookahead. *)
    let lookahead ~assigned =
      let links_free t u gr =
        match meta ar t u with
        | Some { P.v_links = Some l; _ } -> (
            match decided_v assigned (Cg.NPlus.CLink l) with
            | Some (Cg.VPlus.WName (Cg.NPlus.CCrate (t', gr'))) ->
                t' = t && gr' = gr
            | _ -> true)
        | _ -> true
      in
      let valid_memo = Hashtbl.create 64 in
      let valid t u =
        match Hashtbl.find_opt valid_memo (t, u) with
        | Some b -> b
        | None ->
            let gr = compat_class u in
            let g = Cg.NPlus.CCrate (t, gr) in
            let b =
              (match assigned g with
                | PG.Decided { PVersion.v = Cg.VPlus.WOrig w; _ } ->
                    Cargo_version.compare w u = 0
                | PG.Entailed r ->
                    PG.Ranges.contains (tag g (Cg.VPlus.WOrig u)) r
                | _ -> true)
              && links_free t u gr
            in
            Hashtbl.replace valid_memo (t, u) b;
            b
      in
      (* a candidate one of whose mandatory dependencies has no valid
         candidate left, or only one that is itself dead: cargo activates
         it, fails on that dependency and backtracks to this candidate's
         frame, every frame between being younger than the clash
         (find_candidate), and the next time the same dependency comes up
         its conflict cache skips the candidate outright
         (past_conflicting_activations, keyed by the dependency and not by
         who declares it).  PubGrub learns the same thing one version at a
         time, since a slot is named by its owner's version, and each
         lesson can cost a backjump past every decision since the clashing
         activation.  What it has learned against the forced candidate is
         out of sight here, assigned reporting only what a name is
         entailed to, so the chain of forced candidates is followed a few
         steps instead. *)
      let rec first_two t acc = function
        | [] -> acc
        | _ when List.length acc = 2 -> acc
        | w :: ws -> first_two t (if valid t w then w :: acc else acc) ws
      in
      (* a dependency with one valid candidate is followed down at no cost
         in depth, as a forced chain; one with several dies only if all of
         them do, which is looked into a level at most *)
      let dead_memo = Hashtbl.create 64 in
      let rec dead depth chain t u feats default =
        let key = (depth, chain, t, u, Cargo_order.SS.elements feats, default) in
        match Hashtbl.find_opt dead_memo key with
        | Some b -> b
        | None ->
            let b =
              List.exists
                (fun ((d : P.dep), fs) ->
                  let t' = d.P.d_target and dflt = d.P.d_default in
                  match first_two t' [] (candidates d) with
                  | [] -> true
                  | [ w ] -> chain > 0 && dead depth (chain - 1) t' w fs dflt
                  | _ ->
                      depth > 0
                      && List.for_all
                           (fun w ->
                             (not (valid t' w))
                             || dead (depth - 1) chain t' w fs dflt)
                           (candidates d))
                (enabled_deps t u feats default)
            in
            Hashtbl.replace dead_memo key b;
            b
      in
      let live t u feats default = valid t u && not (dead 1 3 t u feats default) in
      (links_free, live)
    in
    let live_by (d : P.dep) live u =
      live d.P.d_target u (Cargo_order.SS.of_list d.P.d_feats) d.P.d_default
    in
    let choose ~assigned tn (cands : PVersion.t list) =
      let links_free, live = lookahead ~assigned in
      let offered w =
        List.find_opt
          (fun (c : PVersion.t) -> Cg.VPlus.compare c.PVersion.v w = E.Eq)
          cands
      in
      let walk (d : P.dep) =
        List.find_map
          (fun u ->
            if live_by d live u then offered (Cg.VPlus.WClass (compat_class u))
            else None)
          (candidates d)
      in
      (* the features the encoding already asks of a crate version: an
         optional dependency they enable can be the one that dies *)
      let asked m gr u =
        match meta ar m u with
        | None -> Cargo_order.SS.empty
        | Some mm ->
            List.fold_left
              (fun acc (f, _) ->
                let x = Cg.NPlus.CFeatP (m, f, gr) in
                match assigned x with
                | PG.Entailed r when PG.Ranges.contains (tag x (Cg.VPlus.WOrig u)) r
                  ->
                    Cargo_order.SS.add f acc
                | PG.Decided { PVersion.v = Cg.VPlus.WOrig w; _ }
                  when Cargo_version.compare w u = 0 ->
                    Cargo_order.SS.add f acc
                | _ -> acc)
              Cargo_order.SS.empty mm.P.v_feats
      in
      let pick =
        match tn with
        | Cg.NPlus.CSlot (_, _, d) ->
            Option.bind (Hashtbl.find_opt dep_of_data d) walk
        | Cg.NPlus.CDec (n, gr, _, d, _) -> (
            match decided_v assigned (Cg.NPlus.CSlot (n, gr, d)) with
            | Some w -> offered w
            | None -> Option.bind (Hashtbl.find_opt dep_of_data d) walk)
        | Cg.NPlus.CCrate (m, gr) ->
            List.find_opt
              (fun (c : PVersion.t) ->
                match c.PVersion.v with
                | Cg.VPlus.WOrig u ->
                    links_free m u gr && live m u (asked m gr u) false
                | _ -> true)
              (List.sort (fun a b -> PVersion.compare b a) cands)
        | Cg.NPlus.CFeatP (m, _, gr) ->
            Option.bind (decided_v assigned (Cg.NPlus.CCrate (m, gr))) offered
        | _ -> None
      in
      match pick with
      | Some c -> c
      | None ->
          List.fold_left
            (fun a b -> if PVersion.compare b a > 0 then b else a)
            (List.hd cands) cands
    in
    (* processing one of cargo's dependencies is, in the encoding, the slot,
       then what the parent delivers to it at that site, then the class's
       crate, then the target's own features, forced by then.  The
       deliveries go before the crate so that its version is chosen seeing
       every feature asked of it, as cargo's candidate is activated with
       them. *)
    let module O = Cargo_order.Make (struct
      type name = Cg.NPlus.t
      type version = PVersion.t
      type assigned = Cg.NPlus.t -> PG.selection

      let equal a b = Cg.NPlus.compare a b = E.Eq
      let decided = decided
      let version_equal a b = PVersion.compare a b = 0
      let root = st.rc
      let root_features = named
      let meta (n, v) = meta ar n v

      let candidates d = List.length (candidates d)

      let owned (t, u) gr =
        match meta (t, u) with
        | None -> []
        | Some m ->
            List.map (fun (f, _) -> Cg.NPlus.CFeatP (t, f, gr)) m.P.v_feats
            @ (match m.P.v_links with
              | Some l -> [ Cg.NPlus.CLink l ]
              | None -> [])

      let root_step assigned =
        let n, v = st.rc in
        let gr = compat_class v in
        List.find_opt (is_open assigned)
          (Cg.NPlus.CRoot :: Cg.NPlus.CCrate (n, gr) :: owned (n, v) gr)

      let dep_step assigned (n, v) (d : P.dep) =
        match site_data ar (n, v) (site_key d) with
        | None -> Cargo_order.Skip
        | Some sd -> (
            let gr0 = compat_class v in
            let sigma = Cg.NPlus.CSlot (n, gr0, sd) in
            match assigned sigma with
            | PG.Entailed _ -> Cargo_order.Decide sigma
            | PG.Decided { PVersion.v = Cg.VPlus.WClass gr; _ } -> (
                let delivered =
                  match meta (n, v) with
                  | None -> []
                  | Some m ->
                      List.concat_map
                        (fun (f, es) ->
                          List.filter_map
                            (function
                              | P.FDepFeat (a, f') | P.FWeakFeat (a, f')
                                when a = d.P.d_alias ->
                                  Some (Cg.NPlus.CDec (n, gr0, f, sd, f'))
                              | _ -> None)
                            es)
                        m.P.v_feats
                in
                let t = d.P.d_target in
                let g = Cg.NPlus.CCrate (t, gr) in
                match List.find_opt (is_open assigned) delivered with
                | Some x -> Cargo_order.Decide x
                | None -> (
                    match assigned g with
                    | PG.Entailed _ -> Cargo_order.Decide g
                    | PG.Decided { PVersion.v = Cg.VPlus.WOrig u; _ } -> (
                        match List.find_opt (is_open assigned) (owned (t, u) gr) with
                        | Some x -> Cargo_order.Decide x
                        | None -> Cargo_order.Activated (t, u))
                    | _ -> Cargo_order.Skip))
            | _ -> Cargo_order.Skip)
    end) in
    let o = O.create () in
    let r =
      PG.solve ~next:(O.next o) ~choose ~vers:versions ~deps:dependencies
        [ ( Cg.NPlus.CRoot,
            PG.Ranges.of_list [ tag Cg.NPlus.CRoot Cg.VPlus.WUnit ] )
        ]
    in
    O.report o;
    match r with
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
