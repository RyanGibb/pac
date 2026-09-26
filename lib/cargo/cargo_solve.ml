module E = Pac
module P = Cargo_parse
module Q = Cargo_query
module Ot = Pac_common.Ot

module CVerOT = Ot.Make (struct
  type t = string

  let compare = Cargo_version.compare
end)

(* SemverMatch: the two tests V.compare cannot express.  sameCore takes
   the candidate first and the comparator's constant second. *)
module PM = struct
  let isPre = Cargo_version.is_prerelease
  let sameCore = Cargo_version.same_core
end

(* rootFeats.  Under All, every key of the root crate's own feature table,
   which is the instantiation Cargo.lock is.  Cargo resolves twice.  The
   lock comes from resolve_with_registry, which passes
   CliFeatures::new_all(true) and HasDevUnits::Yes, and build_requirements
   turns all_features into require_feature for each key of the root
   summary's feature map; with_implicit_features has already put an
   optional dependency's implicit feature into that table, so every
   optional dependency the root declares is reachable.  The build is a
   second resolve handed the lock, so it keeps the lock's versions.  Named
   is not that: it resolves afresh with the features named, and default
   where the root declares one, so its versions can differ from the
   lock's.

   The flag reaches workspace members only: ws.members_with_features
   hands CliFeatures to the root alone, and every other summary arrives as
   RequestedFeatures::DepFeatures carrying whatever its declaring record
   asked for, past resolve_features' [if dep.is_optional() && !reqs.deps
   .contains_key(..) { continue }].  So a *transitive* crate's unactivated
   optionals stay out of the lock, which is sOptional's guard, and nothing
   here forces them in. *)
let root_feats (m : P.ver) : Q.features -> string list = function
  | Q.All -> List.map fst m.P.v_feats
  | Q.Named { feats; default } ->
      if default && m.P.v_default_declared then feats @ [ P.default_feature ]
      else feats

(* dev dependencies participate only from the root crate: that is
   slotActive's rule in the theory, not a choice made here. *)

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
   preference. *)

(* Pre-release versions stay in the index.  The calculus admits one only
   inside a comparator set that names a pre-release at the same release
   core, so no filtering is needed here; yanked versions are dropped by
   the parser instead, which is a repository fact rather than a policy. *)

type archive = {
  index : string;
  crates : (string, P.ver list) Hashtbl.t;
  entry : (string * string, P.ver) Hashtbl.t;
  links_table : (string, (string * string) list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  (* wall time inside the parser, which the solve interleaves with *)
  mutable t_parse : float;
}

let empty_archive index =
  {
    index;
    crates = Hashtbl.create 4096;
    entry = Hashtbl.create 65536;
    links_table = Hashtbl.create 256;
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
              Hashtbl.replace ar.links_table l
                ((n, v.P.v_vers)
                ::
                (match Hashtbl.find_opt ar.links_table l with
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

(* the query's root package, a crate version like any other once its name
   has been read: it takes the place of a registry version at its own
   (name, version), which is the one node the model has there *)
let install_root ar (v : P.ver) =
  let n = v.P.v_name and u = v.P.v_vers in
  let vs = List.filter (fun (w : P.ver) -> w.P.v_vers <> u) (load_name ar n) in
  Hashtbl.replace ar.crates n (vs @ [ v ]);
  Hashtbl.replace ar.entry (n, u) v;
  Hashtbl.filter_map_inplace
    (fun _ ps ->
      match List.filter (( <> ) (n, u)) ps with [] -> None | ps -> Some ps)
    ar.links_table;
  Option.iter
    (fun l ->
      Hashtbl.replace ar.links_table l
        ((n, u) :: Option.value (Hashtbl.find_opt ar.links_table l) ~default:[]))
    v.P.v_links

(* There is no cone pass: a crate is parsed the first time a sub-instance
   reads its name, as cargo's sparse protocol fetches it, so a run touches
   the crates the solver asks about and no others.  Because the instance is
   still being uncovered, the sub-instance a lookup theorem names must be
   complete at the moment the lookup answers.  Each is complete by
   construction -- name_set, support_of_name and repo_preimage load every
   name they read whole, and meta and the witness scan load the owner --
   except the one versions_lookupLink names.  Its
   sub-instance is the preimage of the link relation at l -- every crate
   version declaring l -- and no declaration of any one crate names the
   other declarers, so nothing a loaded crate carries can bring them in:
   links_table holds the declarers among the names loaded so far, and may
   grow after CLink l has answered.  pg_versions answers it afresh each
   time rather than memoizing it. *)

module Cg = E.Cargo (Ot.Str) (CVerOT) (Ot.Str) (CVerOT) (Ot.Str) (Ot.Str) (PM)
module T = Cg.T

(* At most one version per semver granularity class.  The label is the
   class's least release version rather than a tag like "^1", and it is
   ordered as versions are, because the encoding hands PubGrub a
   granularity class where the version would otherwise go: what the solver
   maximises is the label, so an order on labels that disagrees with the
   order on versions silently reverses the preference.  Lexical order on
   "0.9" against "0.10" is exactly that disagreement. *)
let granularity_of (v : string) : string =
  let p = Cargo_version.parse v in
  if p.Cargo_version.major > 0 then
    Printf.sprintf "%d.0.0" p.Cargo_version.major
  else if p.Cargo_version.minor > 0 then
    Printf.sprintf "0.%d.0" p.Cargo_version.minor
  else Printf.sprintf "0.0.%d" p.Cargo_version.patch

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
            (d.P.d_default, (fset_of d.P.d_feats, (d.P.d_cfg, "registry"))) ) )
      ) ) )

let site_key (d : P.dep) : Cg.SlotKey.t =
  (d.P.d_alias, (xkind d.P.d_kind, d.P.d_cfg))

(* a slot node is one manifest site, so its name has to spell the site
   out: bare alias for the plain [dependencies] record, and the kind or cfg
   that told the record apart otherwise *)
let pp_site fmt ((a, (k, cfg)) : Cg.SlotKey.t) =
  Format.fprintf fmt "%s%s%s" a
    (match k with
    | Cg.Kind.KNormal -> ""
    | Cg.Kind.KBuild -> "[build]"
    | Cg.Kind.KDev -> "[dev]")
    (if cfg = "" then "" else "[" ^ cfg ^ "]")

(* the requirement a slot name carries, since versions of one granularity
   class may declare one site differently and so have distinct slots *)
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

  let compare a b = Ot.r2c (Cg.NPlus.compare a b)

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
    | _ -> Ot.r2c (Cg.VPlus.compare a.v b.v)

  let pp fmt ({ v; _ } : t) =
    match v with
    | Cg.VPlus.WUnit -> Format.fprintf fmt "()"
    | Cg.VPlus.WOrig x -> Format.fprintf fmt "%s" x
    | Cg.VPlus.WClass gr -> Format.fprintf fmt "granularity:%s" gr
    | Cg.VPlus.WName n -> PName.pp fmt n
end

module PG = Pubgrub.Make (PName) (PVersion)

type result = {
  crates : (string * string) list;
  feats : (string * string * string list) list;
  (* the parent relation, keyed in the theory by manifest site: one
     crate may depend on a single crate name twice -- under two aliases
     through a rename, or under one alias from two sites -- and the
     copies may land on different granularity classes, so the edge has
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

(* what one solve read of the index, reported whether or not it found an
   answer *)
type run = {
  answer : (result, Pac_common.Report.explanation) Stdlib.result;
  n_names : int;
  n_vers : int;
  t_parse : float;
}

type witness_key =
  [ `Slot of string * string * Cg.SlotData.t
  | `Dec of string * string * string * Cg.SlotData.t * string ]

(* One solve's archive, request and memo tables.  Every table is keyed as
   narrowly as it is because this record is: a second solve builds its
   own, so no answer outlives the archive and root it was computed for. *)
type state = {
  ar : archive;
  rc : string * string;
  features : Q.features;
  rfeats : Cg.FSet.t;
  rustv : string option;
  granularities : (string, string) Hashtbl.t;
  fibres : (string * string, fibres) Hashtbl.t;
  (* the manifest record a slot name's dependency came from, for choose's
     walk over its candidates: the name carries the dependency but not the
     parsed requirement the comparator reads *)
  dep_of_data : (Cg.SlotData.t, P.dep) Hashtbl.t;
  name_sets : (string, Cg.PkgSet.t) Hashtbl.t;
  (* keyed by the read names rather than by the crate version, so that
     versions reading the same names share one entry *)
  repo_preimages : (string list, Cg.PkgSet.t) Hashtbl.t;
  msrv : (string * string * string, bool) Hashtbl.t;
  supports : (string, Cg.SupportSet.t) Hashtbl.t;
  witnesses : (witness_key, Cg.SlotRel.t * Cg.FDefRel.t) Hashtbl.t;
  site_datas :
    ((string * string) * Cg.SlotKey.t, Cg.SlotData.t option) Hashtbl.t;
  (* the tagged list, not just the untagged one, has to be memoized:
     PubGrub asks a name for its versions at every propagation step *)
  pg_vers : (Cg.NPlus.t, PVersion.t list) Hashtbl.t;
  (* at each decision PubGrub's dependency_incomps asks for the
     dependencies of the decided version's neighbours, once per
     dependency, to widen each incompatibility's range *)
  pg_deps :
    (Cg.NPlus.t * Cg.VPlus.t, (Cg.NPlus.t * PG.Ranges.t) list) Hashtbl.t;
  cands : (string * Cargo_version.req, string list) Hashtbl.t;
  enabled :
    (string * string * string list * bool, (P.dep * Order.SS.t) list) Hashtbl.t;
}

let memo tbl k f =
  match Hashtbl.find_opt tbl k with
  | Some v -> v
  | None ->
      let v = f () in
      Hashtbl.replace tbl k v;
      v

let create ar (root : Q.root) ~features ~rustv =
  let rc = Q.crate root in
  {
    ar;
    rc;
    features;
    rfeats = fset_of (root_feats root.Q.ver features);
    rustv;
    granularities = Hashtbl.create 65536;
    fibres = Hashtbl.create 4096;
    dep_of_data = Hashtbl.create 4096;
    name_sets = Hashtbl.create 4096;
    repo_preimages = Hashtbl.create 4096;
    msrv = Hashtbl.create 65536;
    supports = Hashtbl.create 4096;
    witnesses = Hashtbl.create 4096;
    site_datas = Hashtbl.create 4096;
    pg_vers = Hashtbl.create 65536;
    pg_deps = Hashtbl.create 65536;
    cands = Hashtbl.create 4096;
    enabled = Hashtbl.create 4096;
  }

let granularity st v = memo st.granularities v (fun () -> granularity_of v)

let fibres_of st (p : string * string) : fibres =
  memo st.fibres p (fun () ->
      let n, v = p in
      match meta st.ar n v with
      | None -> empty_fibres n
      | Some m ->
          let ds = slots_of m in
          let slots =
            Cg.SlotRel.ofList
              (List.map
                 (fun d ->
                   let sd = slot_data d in
                   Hashtbl.replace st.dep_of_data sd d;
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
            Cg.SupportSet.ofList (List.map (fun (f, _) -> (p, f)) m.P.v_feats)
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
          })

let name_set st (n : string) : Cg.PkgSet.t =
  memo st.name_sets n (fun () ->
      Cg.PkgSet.ofList (List.map (fun v -> (n, v)) (versions_of st.ar n)))

let repo_preimage st (p : string * string) : Cg.PkgSet.t =
  let reads = (fibres_of st p).r_reads in
  memo st.repo_preimages reads (fun () ->
      Cg.PkgSet.unions (List.map (name_set st) reads))

let link_preimage st (l : string) =
  match Hashtbl.find_opt st.ar.links_table l with Some x -> x | None -> []

let crate_msrv_ok st (rustc : string) ((n, v) : string * string) : bool =
  memo st.msrv (rustc, n, v) (fun () ->
      match meta st.ar n v with
      | None -> true
      | Some m -> msrv_ok rustc m.P.v_msrv)

(* the support relation at a name -- Lookup.supportPreimage at {n},
   which versions_lookupFeatP reads -- as the union of its versions'
   fibres.  Memoized for the same reason name_set is: load_name takes a
   name whole, so this cannot grow once it has been asked. *)
let support_of_name st (n : string) : Cg.SupportSet.t =
  memo st.supports n (fun () ->
      Cg.SupportSet.unions
        (List.map
           (fun (v : P.ver) -> (fibres_of st (n, v.P.v_vers)).r_supp)
           (load_name st.ar n)))

(* the witness versions_lookup{Slot,Decision} name: a version of n in
   granularity class gr whose own declarations make the name, found by
   scanning n's index entry, which holds every version of n and is loaded
   whole.  With none, the empty fibres stand for slot_declines and
   decision_declines: nothing in the instance makes the name, and the
   lookup declines.  The verdict reads st.rc through slotActive. *)
let witness st key (ok : string * string -> fibres -> bool) n gr =
  memo st.witnesses key (fun () ->
      match
        List.find_map
          (fun v ->
            if granularity st v = gr then
              let rw = fibres_of st (n, v) in
              if ok (n, v) rw then Some rw else None
            else None)
          (versions_of st.ar n)
      with
      | Some rw -> (rw.r_slots, rw.r_fdefs)
      | None -> (Cg.SlotRel.empty, Cg.FDefRel.empty))

let slot_witness st n gr d =
  fst
    (witness st
       (`Slot (n, gr, d))
       (fun p rw -> Cg.SlotRel.mem (p, d) rw.r_slots && Cg.slotActive st.rc p d)
       n gr)

let dec_witness st n gr f d feat =
  witness st
    (`Dec (n, gr, f, d, feat))
    (fun p rw ->
      Cg.SlotRel.mem (p, d) rw.r_slots
      && Cg.slotActive st.rc p d
      && List.exists
           (fun (((_, f'), e) : Cg.FDefElt.t) ->
             f' = f && Cg.entryFeatD e = Some (Cg.sAlias d, feat))
           (Cg.FDefRel.elements rw.r_fdefs))
    n gr

(* the five components a lookup theorem names, labelled so that the
   extracted functions' like-typed positional arguments cannot be swapped *)
type sub = {
  repo : Cg.PkgSet.t;
  supp : Cg.SupportSet.t;
  fdefs : Cg.FDefRel.t;
  slots : Cg.SlotRel.t;
  links : Cg.LinkRel.t;
}

let empty_sub =
  {
    repo = Cg.PkgSet.empty;
    supp = Cg.SupportSet.empty;
    fdefs = Cg.FDefRel.empty;
    slots = Cg.SlotRel.empty;
    links = Cg.LinkRel.empty;
  }

(* one branch per versions_lookup{Root,Crate,FeatP,Slot,Decision,Link},
   each passing the components its theorem names and nothing else *)
let versions st (tn : Cg.NPlus.t) : Cg.VPlus.t list =
  let call s =
    T.VSet.elements
      (Cg.versions (granularity st) s.repo s.supp s.fdefs s.slots s.links st.rc
         tn)
  in
  match tn with
  | Cg.NPlus.CRoot -> call empty_sub
  | Cg.NPlus.CCrate (n, _) -> call { empty_sub with repo = name_set st n }
  | Cg.NPlus.CFeatP (n, _, _) ->
      let supp = support_of_name st n in
      call { empty_sub with repo = name_set st n; supp }
  | Cg.NPlus.CSlot (n, gr, d) ->
      let slots = slot_witness st n gr d in
      call { empty_sub with repo = name_set st (Cg.sTarget d); slots }
  | Cg.NPlus.CDec (n, gr, f, d, feat) ->
      let slots, fdefs = dec_witness st n gr f d feat in
      call { empty_sub with repo = name_set st (Cg.sTarget d); fdefs; slots }
  | Cg.NPlus.CLink l ->
      (* Lookup.claimants and LinkFibred.headFibre at l, over the
         declarers loaded so far; see the note above Cg *)
      let rs = link_preimage st l in
      let links = Cg.LinkRel.ofList (List.map (fun q -> (q, l)) rs) in
      let repo =
        Cg.PkgSet.ofList (List.filter (fun (n, v) -> meta st.ar n v <> None) rs)
      in
      call { empty_sub with repo; links }

(* one branch per dependees_lookup{Root,Crate,FeatP,Slot,Decision},
   with the request (rc, rootFeats, default) carried whole as the
   theorems carry it; the fall-through is dependees_reduceDepsInert, empty *)
let dependees st (p : T.Pkg.t) : T.Dependees.t list =
  let call s =
    T.DependeesSet.elements
      (Cg.dependees (granularity st) s.repo s.supp s.fdefs s.slots s.links
         P.default_feature st.rc st.rfeats p)
  in
  match p with
  | Cg.NPlus.CRoot, _ -> call empty_sub
  | Cg.NPlus.CCrate (n, _), Cg.VPlus.WOrig v ->
      let rw = fibres_of st (n, v) in
      let repo = repo_preimage st (n, v) in
      call { empty_sub with repo; slots = rw.r_slots; links = rw.r_links }
  | Cg.NPlus.CFeatP (n, _, _), Cg.VPlus.WOrig v ->
      let rw = fibres_of st (n, v) in
      let repo = repo_preimage st (n, v) in
      call
        {
          repo;
          supp = rw.r_supp;
          fdefs = rw.r_fdefs;
          slots = rw.r_slots;
          links = Cg.LinkRel.empty;
        }
  | Cg.NPlus.CSlot (n, gr, d), Cg.VPlus.WClass _ ->
      let slots = slot_witness st n gr d in
      call { empty_sub with repo = name_set st (Cg.sTarget d); slots }
  | Cg.NPlus.CDec (n, gr, f, d, feat), Cg.VPlus.WClass _ ->
      let slots, fdefs = dec_witness st n gr f d feat in
      call { empty_sub with repo = name_set st (Cg.sTarget d); fdefs; slots }
  | _, _ -> []

(* the dependency the owner's fibre holds at a site, which is what a slot
   name carries: the order replay reads raw manifest records, which
   unify_site has not merged, so the name is taken from the fibre *)
let site_data st (p : string * string) (k : Cg.SlotKey.t) =
  memo st.site_datas (p, k) (fun () ->
      List.find_map
        (fun ((_, sd) : Cg.SlotElt.t) ->
          if Cg.sKey sd = k then Some sd else None)
        (Cg.SlotRel.elements (fibres_of st p).r_slots))

(* the preference must land on both names whose candidates are crate
   versions: CFeatP carries WOrig as CCrate does, and whichever of the
   two is decided first fixes the version (a decided CFeatP entails its
   CCrate; choose gives a later CFeatP its CCrate's version), so a family
   left untagged decides by bare semver and the demotion never acts.  A
   granularity class, which CSlot and CDec carry, has no standing: cargo
   ranks the versions a dependency admits and not their granularity
   classes, and which one the ranked walk lands on depends on what is
   already activated, which only choose can see. *)
let tag st (tn : Cg.NPlus.t) (w : Cg.VPlus.t) : PVersion.t =
  match (st.rustv, tn, w) with
  | ( Some rustc,
      (Cg.NPlus.CCrate (n, _) | Cg.NPlus.CFeatP (n, _, _)),
      Cg.VPlus.WOrig v ) ->
      { PVersion.msrv = crate_msrv_ok st rustc (n, v); v = w }
  | _ -> { PVersion.msrv = true; v = w }

(* CLink l is the one name that cannot be held (see the note above Cg); a
   memo would freeze its answer mid-run and refuse a declarer loaded later
   against a set fixed without it *)
let pg_versions st tn =
  match tn with
  | Cg.NPlus.CLink _ -> List.map (tag st tn) (versions st tn)
  | _ -> memo st.pg_vers tn (fun () -> List.map (tag st tn) (versions st tn))

let pg_dependencies st tn ({ PVersion.v = w; _ } : PVersion.t) =
  memo st.pg_deps (tn, w) (fun () ->
      List.map
        (fun ((m, vs) : T.Dependees.t) ->
          (m, PG.Ranges.of_list (List.map (tag st m) (T.VSet.elements vs))))
        (dependees st (tn, w)))

let decided assigned x =
  match assigned x with PG.Decided v -> Some v | _ -> None

let decided_v assigned x =
  Option.map (fun (pv : PVersion.t) -> pv.PVersion.v) (decided assigned x)

let is_open assigned x =
  match assigned x with PG.Entailed _ -> true | _ -> false

(* what the registry query returns for one dependency record, in the
   order sort_summaries leaves it (version_prefs.rs): MSRV-compatible
   first when a toolchain is set, newest first within each.  The
   requirement is read by the comparator the encoding is handed through
   xreq, so these are the members of the granularity classes the slot
   offers. *)
let candidates st (d : P.dep) =
  memo st.cands (d.P.d_target, d.P.d_req) (fun () ->
      let fits u =
        match st.rustv with
        | None -> true
        | Some r -> crate_msrv_ok st r (d.P.d_target, u)
      in
      List.stable_sort
        (fun a b ->
          match (fits a, fits b) with
          | true, false -> -1
          | false, true -> 1
          | _ -> Cargo_version.compare b a)
        (List.filter
           (fun u -> Cargo_version.holds u d.P.d_req)
           (versions_of st.ar d.P.d_target)))

let enabled_deps st t u feats default =
  memo st.enabled
    (t, u, Order.SS.elements feats, default)
    (fun () ->
      match meta st.ar t u with
      | None -> []
      | Some m ->
          let _, deps = Order.requirements m ~all:false feats default in
          Order.enabled ~root:false m deps)

(* RemainingCandidates::next (core/resolver/mod.rs): a candidate is valid
   unless its granularity class is activated at another version or
   another crate holds its links key.  That is a rule over the partial
   solution, and it is where resolver v3's ranking of versions meets the
   granularity classes a slot decides between.  The partial solution
   stands still for the length of one lookahead, so its memos are the
   lookahead's own. *)
type lookahead = {
  links_free : string -> string -> string -> bool;
  live : string -> string -> Order.SS.t -> bool -> bool;
}

let lookahead st ~assigned =
  let links_free t u gr =
    match meta st.ar t u with
    | Some { P.v_links = Some l; _ } -> (
        match decided_v assigned (Cg.NPlus.CLink l) with
        | Some (Cg.VPlus.WName (Cg.NPlus.CCrate (t', gr'))) ->
            t' = t && gr' = gr
        | _ -> true)
    | _ -> true
  in
  let valid_memo = Hashtbl.create 64 in
  let valid t u =
    memo valid_memo (t, u) (fun () ->
        let gr = granularity st u in
        let g = Cg.NPlus.CCrate (t, gr) in
        (match assigned g with
          | PG.Decided { PVersion.v = Cg.VPlus.WOrig w; _ } ->
              Cargo_version.compare w u = 0
          | PG.Entailed r -> PG.Ranges.contains (tag st g (Cg.VPlus.WOrig u)) r
          | _ -> true)
        && links_free t u gr)
  in
  (* a candidate one of whose mandatory dependencies has no valid
     candidate left, or only one that is itself dead: cargo activates
     it, fails on that dependency and backtracks to this candidate's
     frame, every frame between being younger than the clash
     (find_candidate), and the next time the same dependency comes up
     its conflict cache skips the candidate outright
     (past_conflicting_activations, keyed by the dependency and not by
     who declares it).  PubGrub learns the same thing one slot at a
     time, a slot being named by its owner's granularity class and the
     dependency as that owner declares it, and each lesson can cost a
     backjump past every decision since the clashing activation.  What it
     has learned against the forced candidate is out of sight here,
     assigned reporting only what a name is entailed to, so the chain
     of forced candidates is followed a few steps instead. *)
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
    memo dead_memo
      (depth, chain, t, u, Order.SS.elements feats, default)
      (fun () ->
        List.exists
          (fun ((d : P.dep), fs) ->
            let t' = d.P.d_target and dflt = d.P.d_default in
            match first_two t' [] (candidates st d) with
            | [] -> true
            | [ w ] -> chain > 0 && dead depth (chain - 1) t' w fs dflt
            | _ ->
                depth > 0
                && List.for_all
                     (fun w ->
                       (not (valid t' w)) || dead (depth - 1) chain t' w fs dflt)
                     (candidates st d))
          (enabled_deps st t u feats default))
  in
  let live t u feats default = valid t u && not (dead 1 3 t u feats default) in
  { links_free; live }

(* the features the encoding already asks of a crate version: an
   optional dependency they enable can be the one that dies *)
let asked st ~assigned m gr u =
  match meta st.ar m u with
  | None -> Order.SS.empty
  | Some mm ->
      List.fold_left
        (fun acc (f, _) ->
          let x = Cg.NPlus.CFeatP (m, f, gr) in
          match assigned x with
          | PG.Entailed r
            when PG.Ranges.contains (tag st x (Cg.VPlus.WOrig u)) r ->
              Order.SS.add f acc
          | PG.Decided { PVersion.v = Cg.VPlus.WOrig w; _ }
            when Cargo_version.compare w u = 0 ->
              Order.SS.add f acc
          | _ -> acc)
        Order.SS.empty mm.P.v_feats

let choose st ~assigned tn (cands : PVersion.t list) =
  let la = lookahead st ~assigned in
  let offered w =
    List.find_opt
      (fun (c : PVersion.t) -> Cg.VPlus.compare c.PVersion.v w = E.Eq)
      cands
  in
  let walk (d : P.dep) =
    List.find_map
      (fun u ->
        if la.live d.P.d_target u (Order.SS.of_list d.P.d_feats) d.P.d_default
        then offered (Cg.VPlus.WClass (granularity st u))
        else None)
      (candidates st d)
  in
  let pick =
    match tn with
    | Cg.NPlus.CSlot (_, _, d) ->
        Option.bind (Hashtbl.find_opt st.dep_of_data d) walk
    | Cg.NPlus.CDec (n, gr, _, d, _) -> (
        match decided_v assigned (Cg.NPlus.CSlot (n, gr, d)) with
        | Some w -> offered w
        | None -> Option.bind (Hashtbl.find_opt st.dep_of_data d) walk)
    | Cg.NPlus.CCrate (m, gr) ->
        List.find_opt
          (fun (c : PVersion.t) ->
            match c.PVersion.v with
            | Cg.VPlus.WOrig u ->
                la.links_free m u gr
                && la.live m u (asked st ~assigned m gr u) false
            | _ -> true)
          (List.sort (fun a b -> PVersion.compare b a) cands)
    | Cg.NPlus.CFeatP (m, _, gr) ->
        Option.bind (decided_v assigned (Cg.NPlus.CCrate (m, gr))) offered
    | _ -> None
  in
  match pick with
  | Some c -> c
  | None -> Pac_common.Order.greatest PVersion.compare cands

(* processing one of cargo's dependencies is, in the encoding, the slot,
   then what the parent delivers to it at that site, then the granularity
   class's crate, then the target's own features, forced by then.  The
   deliveries go before the crate so that its version is chosen seeing
   every feature asked of it, as cargo's candidate is activated with
   them. *)
module Driver (S : sig
  val st : state
end) =
struct
  let st = S.st

  type name = Cg.NPlus.t
  type version = PVersion.t
  type selection = PG.selection
  type assigned = name -> selection

  let equal a b = Cg.NPlus.compare a b = E.Eq
  let decided = decided
  let version_equal a b = PVersion.compare a b = 0
  let root = st.rc
  let root_features = st.features
  let meta (n, v) = meta st.ar n v
  let candidates d = List.length (candidates st d)
  let choose ~assigned tn cands = choose st ~assigned tn cands

  let owned (t, u) gr =
    match meta (t, u) with
    | None -> []
    | Some m -> (
        List.map (fun (f, _) -> Cg.NPlus.CFeatP (t, f, gr)) m.P.v_feats
        @ match m.P.v_links with Some l -> [ Cg.NPlus.CLink l ] | None -> [])

  let root_step assigned =
    let n, v = st.rc in
    let gr = granularity st v in
    List.find_opt (is_open assigned)
      (Cg.NPlus.CRoot :: Cg.NPlus.CCrate (n, gr) :: owned (n, v) gr)

  (* the decisions for what (n, v) delivers to d's site: every dependency
     feature one of its features names under d's alias *)
  let delivered (n, v) gr0 sd (d : P.dep) =
    match meta (n, v) with
    | None -> []
    | Some m ->
        List.concat_map
          (fun (f, es) ->
            List.filter_map
              (function
                | (P.FDepFeat (a, f') | P.FWeakFeat (a, f'))
                  when a = d.P.d_alias ->
                    Some (Cg.NPlus.CDec (n, gr0, f, sd, f'))
                | _ -> None)
              es)
          m.P.v_feats

  let dep_step assigned (n, v) (d : P.dep) =
    match site_data st (n, v) (site_key d) with
    | None -> Order.Skip
    | Some sd -> (
        let gr0 = granularity st v in
        let sigma = Cg.NPlus.CSlot (n, gr0, sd) in
        match assigned sigma with
        | PG.Entailed _ -> Order.Decide sigma
        | PG.Decided { PVersion.v = Cg.VPlus.WClass gr; _ } -> (
            let t = d.P.d_target in
            let g = Cg.NPlus.CCrate (t, gr) in
            match
              List.find_opt (is_open assigned) (delivered (n, v) gr0 sd d)
            with
            | Some x -> Order.Decide x
            | None -> (
                match assigned g with
                | PG.Entailed _ -> Order.Decide g
                | PG.Decided { PVersion.v = Cg.VPlus.WOrig u; _ } -> (
                    match
                      List.find_opt (is_open assigned) (owned (t, u) gr)
                    with
                    | Some x -> Order.Decide x
                    | None -> Order.Activated (t, u))
                | _ -> Order.Skip))
        | _ -> Order.Skip)
end

let decode st (sol : (Cg.NPlus.t * PVersion.t) list) : result =
  let sol =
    List.map
      (fun ((tn, { PVersion.v; _ }) : Cg.NPlus.t * PVersion.t) -> (tn, v))
      sol
  in
  let s = T.PkgSet.ofList sol in
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
          match meta st.ar n v with
          | Some m when not m.P.v_default_declared ->
              List.filter (fun f -> f <> P.default_feature) fs
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
  let fibres = List.map (fibres_of st) (st.rc :: crates) in
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
      (Cg.ParentRel.elements (Cg.decodeParents fdefs slots st.rc s))
  in
  {
    crates = List.sort compare crates;
    feats;
    parents;
    nodes = List.length sol;
    (* the crate versions whose manifests became encoded fibres *)
    processed = Hashtbl.length st.fibres;
  }

let solve ?(debug = false) ?(order = `Tool) ~index ~features ~rustv
    (root : Q.root) : run =
  Pubgrub.set_debug debug;
  let ar = empty_archive index in
  install_root ar root.Q.ver;
  let st = create ar root ~features ~rustv in
  let query =
    [
      ( Cg.NPlus.CRoot,
        PG.Ranges.of_list [ tag st Cg.NPlus.CRoot Cg.VPlus.WUnit ] );
    ]
  in
  let module O = Order.Make (Driver (struct
    let st = st
  end))
  in
  let h = O.hooks order () in
  let outcome =
    PG.solve ?next:h.Pac_common.Order.next ?choose:h.Pac_common.Order.choose
      ~vers:(pg_versions st) ~deps:(pg_dependencies st) query
  in
  h.Pac_common.Order.finish ();
  let answer =
    match outcome with
    | Error inc -> Error (fun ppf -> PG.explain_incompatibility ppf inc)
    | Ok sol -> Ok (decode st sol)
  in
  { answer; n_names = ar.n_names; n_vers = ar.n_vers; t_parse = ar.t_parse }

(* cargo tells packages apart by source as well, so without the
   self-patch the registry's crate at the root's name and version is a
   second package, which one node per (name, version) cannot be *)
let reaches_registry_root (root : Q.root) (r : result) =
  let rc = Q.crate root in
  (not root.Q.self_patch)
  && List.exists (fun (n, u, _, t, w) -> (t, w) = rc && (n, u) <> rc) r.parents
