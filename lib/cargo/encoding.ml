module E = Pac
module P = Cargo_parse
module Q = Cargo_query
module Ot = Pac_common.Ot

module CVerOT = Ot.Make (struct
  type t = string

  let compare = Cargo_version.compare
end)

(* SemverMatch: the two tests a version order cannot express.  sameCore
   takes the candidate first and the comparator's constant second. *)
module PM = struct
  let isPre = Cargo_version.is_prerelease
  let sameCore = Cargo_version.same_core
end

module Cg = E.Cargo (Ot.Str) (CVerOT) (Ot.Str) (CVerOT) (Ot.Str) (Ot.Str) (PM)
module T = Cg.T

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

(* Build and normal edges share one feature-unified graph here.  Resolver
   v2 decouples them, and v3 inherits that, but cargo decouples in
   FeatureResolver, which runs over an already-fixed resolution: it
   decides which features each unit is compiled with and cannot move a
   version.  So the decoupling is not part of what a resolution is, and
   the only half of v3 that reaches version selection is the MSRV
   preference.  A dev edge counts from the root alone, which is
   slotActive's rule in the theory and not a choice made here. *)
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
   requested features is what that unreachable case gets. *)
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

(* [ds] grouped by [key], in order of first appearance, each group merged *)
let group key merge (ds : P.dep list) : P.dep list =
  let tbl = Hashtbl.create 16 in
  let order = ref [] in
  List.iter
    (fun (d : P.dep) ->
      let k = key d in
      if not (Hashtbl.mem tbl k) then order := k :: !order;
      Pac_common.Tbl.push tbl k d)
    ds;
  List.map (fun k -> merge (List.rev (Hashtbl.find tbl k))) (List.rev !order)

(* cargo writes a crate's dependencies to the lock as the versions they
   resolved to, and reading the lock back locks each declaration to the
   first of those, in version order, that its requirement admits
   (core/registry.rs, lock).  Two active declarations of one alias with one
   requirement therefore get one version, whatever cfg or kind each sits
   under, and are one slot here: the first's site, both sets of features.
   A dev-dependency is active from the root alone.  Declarations whose
   requirements differ but overlap are held to the same rule by cargo and
   not here. *)
let lock_merge (ds : P.dep list) : P.dep =
  let d0 = List.hd ds in
  {
    d0 with
    P.d_feats =
      List.sort_uniq String.compare
        (List.concat_map (fun (d : P.dep) -> d.P.d_feats) ds);
    d_default = List.exists (fun (d : P.dep) -> d.P.d_default) ds;
  }

let slots_of ~root (v : P.ver) : P.dep list =
  group
    (fun (d : P.dep) ->
      if d.P.d_kind = P.Dev && not root then `Site (site_of d)
      else `Lock (d.P.d_alias, d.P.d_target, d.P.d_req, d.P.d_optional))
    lock_merge
    (group site_of unify_site v.P.v_deps)

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
