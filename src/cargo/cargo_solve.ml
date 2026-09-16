(* Cargo solving over the verified pipeline, deb_solve/opam_solve-style:
   the index is parsed into hashtables a crate at a time, as the solver
   first asks for each; every query is answered from a small
   slice instance in the shape one of Cargo.v's lookup theorems justifies
   (own rows, and the repository restricted to realPreimage of crateReads,
   or to a link's declarers), pushed through the Cargo encoder straight to
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

(* cfg_active: target-specific dependencies are dropped rather than
   evaluated, so this resolves the cfg-independent subgraph.  A real
   frontend would evaluate the cfg expression against a target triple. *)
let cfg_active (cfg : string) : bool = cfg = ""

(* the feature every dependency requests unless it opts out with
   default-features = false *)
let default_feature = "default"

(* rootFeats: the root crate's own features start empty, so only what its
   dependencies request is enabled.  Cargo would enable the root's
   "default" feature; that is a one-line change here, kept off because the
   brief pins it. *)
let root_feats : string list = []

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
   rows are never taken from a name parsed in part *)
let meta ar n v : P.ver option =
  ignore (load_name ar n);
  Hashtbl.find_opt ar.entry (n, v)

(* There is no cone pass: a crate is parsed the first time a slice reads
   its name, as cargo's sparse protocol fetches it, so a run touches the
   crates the solver asks about and no others.  Because the instance is
   still being uncovered, each lookup theorem's slice must be complete at
   the moment it answers.  That holds by construction for all but one
   query: CCrate n and CFeatP n read the repository at n alone; CSlot and
   CDec at (n, v) read (n, v)'s own rows and the repository at crateReads,
   the names its slots target; and name_set and slice load every name they
   read, while meta loads the owner.  CLink l is the exception.  Its slice
   is the link relation's preimage at l -- every crate version declaring l
   -- and no row of any one crate names the other declarers, so nothing a
   loaded crate carries can bring them in: links_idx holds the declarers
   among the names loaded so far, and may grow after CLink l has answered.
   Make.solve answers it afresh each time rather than memoizing it. *)

module Make () = struct
  module Cg =
    E.Cargo (StringOT) (CVerOT) (StringOT) (StringOT) (CVerOT) (StringOT)
      (StringOT)
      (PM)

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

  (* the manifest may name one alias under several kinds or cfgs; the
     calculus wants at most one slot per (crate, alias) -- AliasFunctional
     -- so unify them the way cargo does: conjoin the requirements, union
     the requested features, and prefer the unconditional rows when there
     are any *)
  let unify_alias (ds : P.dep list) : P.dep =
    let active = List.filter (fun (d : P.dep) -> cfg_active d.P.d_cfg) ds in
    let ds = if active <> [] then active else ds in
    (* a dev row participates only from the root, so an alias that is also
       declared non-dev is a non-dev slot: conjoining the two would make the
       dev row's requirement -- and its non-optionality -- bind on every
       depender.  When every row is dev the slot stays dev and slotActive
       gates it.  The residual is that the root loses a dev-only requirement
       on an alias it also depends on normally, which AliasFunctional cannot
       express *)
    let nondev = List.filter (fun (d : P.dep) -> d.P.d_kind <> P.Dev) ds in
    let ds = if nondev <> [] then nondev else ds in
    let d0 = List.hd ds in
    let rank (d : P.dep) =
      match d.P.d_kind with P.Normal -> 0 | P.Build -> 1 | P.Dev -> 2
    in
    let best =
      List.fold_left (fun a b -> if rank b < rank a then b else a) d0 ds
    in
    {
      d0 with
      P.d_target = best.P.d_target;
      d_kind = best.P.d_kind;
      d_cfg = (if active <> [] then "" else d0.P.d_cfg);
      d_req = List.concat_map (fun (d : P.dep) -> d.P.d_req) ds;
      d_feats =
        List.sort_uniq String.compare
          (List.concat_map (fun (d : P.dep) -> d.P.d_feats) ds);
      d_optional = List.for_all (fun (d : P.dep) -> d.P.d_optional) ds;
      d_default = List.exists (fun (d : P.dep) -> d.P.d_default) ds;
    }

  let slots_of (v : P.ver) : P.dep list =
    let tbl = Hashtbl.create 16 in
    let order = ref [] in
    List.iter
      (fun (d : P.dep) ->
        if not (Hashtbl.mem tbl d.P.d_alias) then order := d.P.d_alias :: !order;
        Hashtbl.replace tbl d.P.d_alias
          (d
          ::
          (match Hashtbl.find_opt tbl d.P.d_alias with
          | Some l -> l
          | None -> [])))
      v.P.v_deps;
    List.rev_map (fun a -> unify_alias (List.rev (Hashtbl.find tbl a))) !order

  (* ---- per-crate rows: exactly ownSlots/ownFDefs/ownLinks/ownSupport ---- *)

  type rows = {
    r_slots : Cg.SlotRel.t;
    r_fdefs : Cg.FDefRel.t;
    r_links : Cg.LinkRel.t;
    r_supp : Cg.SupportSet.t;
    r_reads : string list; (* crateReads: own name plus the slot targets *)
  }

  let empty_rows n =
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

  let rows_cache : (string * string, rows) Hashtbl.t = Hashtbl.create 4096

  let rows_of ar (p : string * string) : rows =
    match Hashtbl.find_opt rows_cache p with
    | Some r -> r
    | None ->
        let n, v = p in
        let r =
          match meta ar n v with
          | None -> empty_rows n
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
        Hashtbl.replace rows_cache p r;
        r

  (* ---- repository slices ---- *)

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

  (* realPreimage R (crateReads Slots p): every version of every name the
     crate's rows read, and nothing else *)
  (* keyed by the read names rather than by the crate version, because
     consecutive versions of a crate almost always read the same names *)
  let slice_cache : (string list, Cg.PkgSet.t) Hashtbl.t = Hashtbl.create 4096

  let slice ar (p : string * string) : Cg.PkgSet.t =
    let reads = (rows_of ar p).r_reads in
    match Hashtbl.find_opt slice_cache reads with
    | Some s -> s
    | None ->
        let s = Cg.PkgSet.unions (List.map (name_set ar) reads) in
        Hashtbl.replace slice_cache reads s;
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

  let link_rows st (l : string) =
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

  (* ownSupport summed over a name's versions, which is the slice a feature
     name's lookup reads.  Cached for the same reason name_set is: load_name
     takes a name whole, so this cannot grow once it has been asked. *)
  let support_cache : (string, Cg.SupportSet.t) Hashtbl.t = Hashtbl.create 4096

  let support_of_name st (n : string) : Cg.SupportSet.t =
    match Hashtbl.find_opt support_cache n with
    | Some s -> s
    | None ->
        let s =
          Cg.SupportSet.unions
            (List.map
               (fun (v : P.ver) -> (rows_of st.ar (n, v.P.v_vers)).r_supp)
               (load_name st.ar n))
        in
        Hashtbl.replace support_cache n s;
        s

  let versions st (nm : Cg.NPlus.t) : Cg.VPlus.t list =
    let call r supp fdefs slots links =
      T.VSet.elements
        (Cg.versions compat_class r supp fdefs slots links cfg_active st.rc nm)
    in
    let none = Cg.PkgSet.empty in
    let nosupp = Cg.SupportSet.empty in
    let nofd = Cg.FDefRel.empty in
    let nosl = Cg.SlotRel.empty in
    let nolk = Cg.LinkRel.empty in
    match nm with
    | Cg.NPlus.CRoot -> call none nosupp nofd nosl nolk
    | Cg.NPlus.CCrate (n, _) -> call (name_set st.ar n) nosupp nofd nosl nolk
    | Cg.NPlus.CFeatP (n, _, _) ->
        call (name_set st.ar n) (support_of_name st n) nofd nosl nolk
    | Cg.NPlus.CSlot (n, v, _) ->
        let rw = rows_of st.ar (n, v) in
        call (slice st.ar (n, v)) nosupp nofd rw.r_slots nolk
    | Cg.NPlus.CDec (n, v, _, _, _) ->
        let rw = rows_of st.ar (n, v) in
        call (slice st.ar (n, v)) nosupp rw.r_fdefs rw.r_slots nolk
    | Cg.NPlus.CLink l ->
        let rs = link_rows st l in
        let r =
          Cg.PkgSet.ofList
            (List.filter (fun (n, v) -> meta st.ar n v <> None) rs)
        in
        call r nosupp nofd nosl (Cg.LinkRel.ofList (List.map (fun q -> (q, l)) rs))

  let deps st (p : T.Pkg.t) : T.Dependees.t list =
    let call r supp fdefs slots links rootf =
      T.DependeesSet.elements
        (Cg.dependees compat_class r supp fdefs slots links cfg_active
           default_feature st.rc rootf p)
    in
    let none = Cg.PkgSet.empty in
    let nosupp = Cg.SupportSet.empty in
    let nofd = Cg.FDefRel.empty in
    let nosl = Cg.SlotRel.empty in
    let nolk = Cg.LinkRel.empty in
    let nofs = Cg.FSet.empty in
    let owner n v k =
      let rw = rows_of st.ar (n, v) in
      k (slice st.ar (n, v)) rw
    in
    match (fst p, snd p) with
    | Cg.NPlus.CRoot, _ -> call none nosupp nofd nosl nolk st.rfeats
    | Cg.NPlus.CCrate (n, _), Cg.VPlus.WOrig v ->
        owner n v (fun r rw -> call r nosupp nofd rw.r_slots rw.r_links nofs)
    | Cg.NPlus.CFeatP (n, _, _), Cg.VPlus.WOrig v ->
        owner n v (fun r rw ->
            call r rw.r_supp rw.r_fdefs rw.r_slots nolk nofs)
    | Cg.NPlus.CSlot (n, v, _), Cg.VPlus.WClass _ ->
        owner n v (fun r rw -> call r nosupp nofd rw.r_slots nolk nofs)
    | Cg.NPlus.CDec (n, v, _, _, _), Cg.VPlus.WClass _ ->
        owner n v (fun r rw -> call r nosupp rw.r_fdefs rw.r_slots nolk nofs)
    | _, _ -> []

  module PName = struct
    type t = Cg.NPlus.t

    let compare a b = r2c (Cg.NPlus.compare a b)

    let pp fmt (nm : t) =
      match nm with
      | Cg.NPlus.CRoot -> Format.fprintf fmt "root"
      | Cg.NPlus.CCrate (n, gr) -> Format.fprintf fmt "%s@%s" n gr
      | Cg.NPlus.CFeatP (n, f, gr) -> Format.fprintf fmt "%s/%s@%s" n f gr
      | Cg.NPlus.CSlot (n, v, a) -> Format.fprintf fmt "%s@%s->%s" n v a
      | Cg.NPlus.CDec (n, v, f, a, feat) ->
          Format.fprintf fmt "<%s@%s/%s=>%s/%s>" n v f a feat
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
      | Cg.VPlus.WMember (n, x) -> Format.fprintf fmt "member:%s-%s" n x
  end

  module PG = Pubgrub.Make (PName) (PVersion)

  type result = {
    crates : (string * string) list;
    feats : (string * string * string list) list;
    (* the parent relation, keyed by alias: a cargo rename lets one crate
       depend on a single crate name twice, and the two aliases may land
       on different compatibility classes, so the edge has to record which
       alias received which version *)
    parents : (string * string * string * string) list;
    nodes : int;
    processed : int;
  }

  let solve ?(debug = false) ?(rfeats = root_feats) ?(rustv = rust_version) ar
      (rc : string * string) =
    Pubgrub.set_debug debug;
    let st = mk_state ar rc rfeats rustv in
    (* the preference must land on every name whose candidates are concrete
       crate versions, not just the crate name: CFeatP also carries WOrig,
       and whichever of the two families is decided first entails the other,
       so a family left untagged decides by bare semver and the demotion
       never acts.  Class gadgets carry WClass/WMember and no standing. *)
    let tag (nm : Cg.NPlus.t) (w : Cg.VPlus.t) : PVersion.t =
      match (st.rustv, nm, w) with
      | ( Some rustc,
          (Cg.NPlus.CCrate (n, _) | Cg.NPlus.CFeatP (n, _, _)),
          Cg.VPlus.WOrig v ) ->
          { PVersion.msrv = crate_msrv_ok st rustc (n, v); v = w }
      | _ -> { PVersion.msrv = true; v = w }
    in
    (* the tagged list, not just the untagged one, has to be memoized:
       PubGrub asks a name for its versions at every propagation step.
       CLink l is the one name that cannot be held: its versions are the
       whole preimage of the link relation at l, and no row of any one
       declarer names the others, so links_idx holds only the declarers
       among the names loaded so far and may grow after CLink l has
       answered.  Recomputing the filter -- a handful of rows -- lets a
       declarer loaded later simply be there, where a cache would freeze
       the answer mid-run and refuse it against a set fixed without it. *)
    let vcache = Hashtbl.create 65536 in
    let versions nm =
      match Hashtbl.find_opt vcache nm with
      | Some vs -> vs
      | None ->
          let vs = List.map (tag nm) (versions st nm) in
          (match nm with
          | Cg.NPlus.CLink _ -> ()
          | _ -> Hashtbl.replace vcache nm vs);
          vs
    in
    (* the decisive memoization: PubGrub asks for the same node's
       dependencies over and over during propagation *)
    let dcache = Hashtbl.create 65536 in
    let dependencies nm ({ PVersion.v = w; _ } : PVersion.t) =
      match Hashtbl.find_opt dcache (nm, w) with
      | Some r -> r
      | None ->
          let r =
            List.map
              (fun ((m, vs) : T.Dependees.t) ->
                ( m,
                  PG.Ranges.of_list
                    (List.map (tag m) (T.VSet.elements vs)) ))
              (deps st (nm, w))
          in
          Hashtbl.replace dcache (nm, w) r;
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
            (fun ((nm, { PVersion.v; _ }) : Cg.NPlus.t * PVersion.t) -> (nm, v))
            sol
        in
        let s = T.PkgSet.ofList sol in
        (* back through the proved decoders *)
        let crates = Cg.PkgSet.elements (Cg.decodeS s) in
        let feats =
          List.map
            (fun (((n, v), fs) : Cg.Featured.t) -> (n, v, Cg.FSet.elements fs))
            (Cg.FeaturedSet.elements (Cg.decodeFS s))
        in
        (* decodeParents is the one decoder that reads Slots, and a lazy
           run has no global relation to hand it; the slots of the crates
           it decodes are all it looks at, since slotsAt filters to the
           owner named by the node *)
        let slots =
          Cg.SlotRel.unions
            (List.map (fun p -> (rows_of st.ar p).r_slots) (st.rc :: crates))
        in
        let parents =
          List.map
            (fun ((((n, v), a), u) : Cg.ParentElt.t) -> (n, v, a, u))
            (Cg.ParentRel.elements
               (Cg.decodeParents slots cfg_active st.rc s))
        in
        Some
          {
            crates = List.sort compare crates;
            feats;
            parents;
            nodes = List.length sol;
            (* the crate versions whose manifests became encoded rows *)
            processed = Hashtbl.length rows_cache;
          }
end
