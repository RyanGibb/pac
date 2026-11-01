module type S = sig
  module E = Pac

  module CVerOT : sig
    type t = string

    val compare : t -> t -> Pac.comparison
    val eq_dec : t -> t -> bool
  end

  module PM : sig
    val isPre : string -> bool
    val sameCore : string -> string -> bool
  end

  module Cg :
      module type of
        Pac.Cargo (Pac_common.Ot.Str) (CVerOT) (Pac_common.Ot.Str) (CVerOT)
          (Pac_common.Ot.Str)
          (Pac_common.Ot.Str)
          (PM)

  module T = Cg.Reduction.Reduced

  val root_feats : Cargo_parse.ver -> Cargo_query.features -> string list
  val msrv_ok : string -> string option -> bool
  val granularity_of : string -> string
  val fset_of : string list -> Cg.FSet.t
  val xentry : Cargo_parse.fentry -> Cg.FeatureEntry.t
  val slots_of : root:bool -> Cargo_parse.ver -> Cargo_parse.dep list
  val slot_data : Cargo_parse.dep -> Cg.DependencyRecord.t
  val site_key : Cargo_parse.dep -> Cg.Site.t

  module PName : sig
    type t = Cg.Reduction.Name.t

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module PVersion : sig
    type t = { msrv : bool; v : Cg.Reduction.Version.t }

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module PG : module type of Pubgrub.Make (PName) (PVersion)
end

module Make () = struct
  module E = Pac
  module P = Cargo_parse
  module Q = Cargo_query
  module Ot = Pac_common.Ot

  module CVerOT = Ot.Make (struct
    type t = string

    let compare = Cargo_version.compare
  end)

  module PM = struct
    let isPre = Cargo_version.is_prerelease
    let sameCore = Cargo_version.same_core
  end

  module Cg = E.Cargo (Ot.Str) (CVerOT) (Ot.Str) (CVerOT) (Ot.Str) (Ot.Str) (PM)
  module T = Cg.Reduction.Reduced

  (* rootFeats.  Under All, every key of the root's feature table, as
     Cargo.lock is resolved with every feature (resolve_with_registry,
     CliFeatures::new_all), with_implicit_features having given each optional
     dependency its implicit feature.  Only the root gets every feature
     (members_with_features), so a transitive crate's unactivated optional
     dependencies stay out, as cargo's resolve_features skips them.  Named
     resolves afresh, so its versions can differ from the lock's. *)
  let root_feats (m : P.ver) : Q.features -> string list = function
    | Q.All -> List.map fst m.P.v_feats
    | Q.Named { feats; default } ->
        if default && m.P.v_default_declared then feats @ [ P.default_feature ]
        else feats

  (* cargo's RustVersion::is_compatible_with: the MSRV as a caret
     requirement against the toolchain with any pre-release dropped.  The
     index writes a partial MSRV ("1.71"), which caret expansion is defined
     on, so nothing pads it.  No MSRV is compatible with every toolchain
     (msrv_compat_count). *)
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

  let xentry : P.fentry -> Cg.FeatureEntry.t = function
    | P.FFeat f -> Cg.FeatureEntry.EFeat f
    | P.FDep a -> Cg.FeatureEntry.EDep a
    | P.FDepFeat (a, f) -> Cg.FeatureEntry.EDepFeat (a, f)
    | P.FWeakFeat (a, f) -> Cg.FeatureEntry.EWeakFeat (a, f)

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

  (* cargo resolves each declaration apart (resolve_features,
     core/resolver/dep_cache.rs), so two sites of one alias may take two
     versions, and cargo's own fresh lock splits them where one version
     lacks a feature one site asks for.  Two active sites that ask the same
     of the same crate -- requirement, features, default features -- see
     the same candidates, newest first, and the second finds the first's
     version active with nothing new to enable (activate, core/resolver/
     mod.rs), so they get one version, and are one slot here, at the first
     site.  A dev-dependency is active from the root alone. *)
  let same_ask ~root (d : P.dep) =
    if d.P.d_kind = P.Dev && not root then `Site (site_of d)
    else
      `Ask
        ( d.P.d_alias,
          d.P.d_name,
          d.P.d_req,
          List.sort_uniq String.compare d.P.d_feats,
          d.P.d_default,
          d.P.d_optional )

  let slots_of ~root (v : P.ver) : P.dep list =
    group (same_ask ~root) List.hd (group site_of unify_site v.P.v_deps)

  let slot_data (d : P.dep) : Cg.DependencyRecord.t =
    ( d.P.d_alias,
      ( d.P.d_name,
        ( xreq d.P.d_req,
          ( xkind d.P.d_kind,
            ( d.P.d_optional,
              (d.P.d_default, (fset_of d.P.d_feats, (d.P.d_cfg, "registry"))) )
          ) ) ) )

  let site_key (d : P.dep) : Cg.Site.t =
    (d.P.d_alias, (xkind d.P.d_kind, d.P.d_cfg))

  (* a slot node is one manifest site, so its name has to spell the site
     out: bare alias for the plain [dependencies] record, and the kind or cfg
     that told the record apart otherwise *)
  let pp_site fmt ((a, (k, cfg)) : Cg.Site.t) =
    Format.fprintf fmt "%s%s%s" a
      (match k with
      | Cg.Kind.KNormal -> ""
      | Cg.Kind.KBuild -> "[build]"
      | Cg.Kind.KDev -> "[dev]")
      (if cfg = "" then "" else "[" ^ cfg ^ "]")

  (* the requirement a slot name carries, since versions of one granularity
     class may declare one site differently and so have distinct slots *)
  let pp_req fmt (d : Cg.DependencyRecord.t) =
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
            (Cg.sRange d)))

  module PName = struct
    type t = Cg.Reduction.Name.t

    let compare a b = Ot.r2c (Cg.Reduction.Name.compare a b)

    let pp fmt (tn : t) =
      match tn with
      | Cg.Reduction.Name.CRoot -> Format.fprintf fmt "root"
      | Cg.Reduction.Name.CGran (n, gr) -> Format.fprintf fmt "%s@%s" n gr
      | Cg.Reduction.Name.CFeatP (n, f, gr) ->
          Format.fprintf fmt "%s/%s@%s" n f gr
      | Cg.Reduction.Name.CSlot (n, gr, d) ->
          Format.fprintf fmt "%s@%s->%a%a" n gr pp_site (Cg.sSite d) pp_req d
      | Cg.Reduction.Name.CDec (n, gr, f, d, feat) ->
          Format.fprintf fmt "<%s@%s/%s=>%a%a/%s>" n gr f pp_site (Cg.sSite d)
            pp_req d feat
      | Cg.Reduction.Name.CCls l -> Format.fprintf fmt "links:%s" l
  end

  module PVersion = struct
    type t = { msrv : bool; v : Cg.Reduction.Version.t }

    let compare a b =
      match (a.msrv, b.msrv) with
      | false, true -> -1
      | true, false -> 1
      | _ -> Ot.r2c (Cg.Reduction.Version.compare a.v b.v)

    let pp fmt ({ v; _ } : t) =
      match v with
      | Cg.Reduction.Version.WUnit -> Format.fprintf fmt "()"
      | Cg.Reduction.Version.WOrig x -> Format.fprintf fmt "%s" x
      | Cg.Reduction.Version.WClass gr -> Format.fprintf fmt "granularity:%s" gr
      | Cg.Reduction.Version.WName n -> PName.pp fmt n
  end

  module PG = Pubgrub.Make (PName) (PVersion)
end
