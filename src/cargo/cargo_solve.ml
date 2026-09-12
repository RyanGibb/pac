(* Cargo solving over the verified pipeline, deb_solve/opam_solve-style:
   the index is parsed into hashtables a crate at a time, as the solver
   first asks for each; every query is answered from a small
   slice instance in the shape one of Cargo.v's lookup theorems justifies
   (own rows, and the repository restricted to realPreimage of crateReads,
   or to a link's declarers), pushed through the Cargo encoder and then
   through FeatureConcurrent's proved reduction to Core; PubGrub solves the
   accumulated core graph lazily and the solution comes back through the
   proved decoders.  Trusted here (TCB): the parser, the version
   comparator, the policy defaults below, and the plumbing. *)

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

(* Resolver v1 feature reading: build and normal dependencies share one
   feature-unified graph.  Cargo's resolver v2 splits them (and splits
   target-specific features); the theory carries the kind but does not
   separate them, so this matches the theory. *)

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
   the moment it answers.  That holds by construction for three of the four
   queries: Crate n reads the repository at n alone; SlotN and DecisionN at
   (n, v) read (n, v)'s own rows and the repository at crateReads, the
   names its slots target; and name_set and slice load every name they
   read, while meta loads the owner.  LinkN l is the exception.  Its slice
   is the link relation's preimage at l -- every crate version declaring l
   -- and no row of any one crate names the other declarers, so nothing a
   loaded crate carries can bring them in: links_idx holds the declarers
   among the names loaded so far, and may grow after LinkN l has answered.
   Make.solve detects that and repeats the run; see there. *)

module Make () = struct
  module Cg =
    E.Cargo (StringOT) (CVerOT) (StringOT) (StringOT) (StringOT) (StringOT)
      (StringOT)
      (PM)

  module FC = Cg.FC
  module Red = FC.Reduction
  module T = Red.T

  (* ---- granularity: at most one version per semver compatibility class,
     the leftmost-nonzero component ---- *)
  let compat_class (v : string) : string =
    let p = Cargo_version.parse v in
    if p.Cargo_version.major > 0 then Printf.sprintf "^%d" p.Cargo_version.major
    else if p.Cargo_version.minor > 0 then
      Printf.sprintf "0.%d" p.Cargo_version.minor
    else Printf.sprintf "0.0.%d" p.Cargo_version.patch

  let gp = Cg.gPlus compat_class

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

  (* the support of a crate version is its feature table's domain: this is
     ownSupport support p read straight off the manifest, without paying
     for the encoded rows *)
  let has_feature ar ((n, v) : string * string) (f : string) : bool =
    match meta ar n v with
    | None -> false
    | Some m -> List.mem_assoc f m.P.v_feats

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
    edges : (T.Pkg.t, T.DependeesSet.t) Hashtbl.t;
    gadget_vers : (Red.Name.name, Cg.VPlus.t list) Hashtbl.t;
    processed : (string * string, unit) Hashtbl.t;
    mutable root_done : bool;
    npv_cache : (Cg.NPlus.t, Cg.VPlus.t list) Hashtbl.t;
    mutable n_proc : int;
  }

  let mk_state ar rc rfeats =
    {
      ar;
      rc;
      rfeats = fset_of rfeats;
      edges = Hashtbl.create 65536;
      gadget_vers = Hashtbl.create 65536;
      processed = Hashtbl.create 4096;
      root_done = false;
      npv_cache = Hashtbl.create 65536;
      n_proc = 0;
    }

  let verbose = Sys.getenv_opt "PACPROG" <> None

  let record_deprel st (d : T.DepRel.t) =
    List.iter
      (fun ((s, h) : T.DepElt.t) ->
        let prev =
          match Hashtbl.find_opt st.edges s with
          | Some x -> x
          | None -> T.DependeesSet.empty
        in
        Hashtbl.replace st.edges s (T.DependeesSet.add h prev))
      (T.DepRel.elements d)

  (* only the intermediate gadgets are harvested; the granular names are
     answered by the per-name lookups below *)
  let record_real st (r : T.PkgSet.t) =
    List.iter
      (fun ((nm, u) : T.Pkg.t) ->
        match nm with
        | Red.Name.GranularOrig _ | Red.Name.GranularFeatPkg _ -> ()
        | _ ->
            let prev =
              match Hashtbl.find_opt st.gadget_vers nm with
              | Some x -> x
              | None -> []
            in
            if not (List.mem u prev) then
              Hashtbl.replace st.gadget_vers nm (u :: prev))
      (T.PkgSet.elements r)

  (* the FC-side repository a crate's own rows need: the packages its
     support rows sit on.  reduceDeps reads R only to filter those rows,
     and every one of them is a package of the global translation. *)
  let support_owners (sup : FC.Feat.SupportSet.t) : FC.PkgSet.t =
    FC.PkgSet.ofList
      (List.map
         (fun ((q, _) : FC.Feat.PkgF.t) -> q)
         (FC.Feat.SupportSet.elements sup))

  let process_root st =
    if not st.root_done then begin
      st.root_done <- true;
      let df = Cg.rootEdge st.rc st.rfeats in
      record_deprel st
        (Red.reduceDeps FC.PkgSet.empty FC.Feat.SupportSet.empty df
           FC.Feat.AddlDepRel.empty gp);
      record_real st
        (Red.reduceReal FC.PkgSet.empty FC.Feat.SupportSet.empty df
           FC.Feat.AddlDepRel.empty gp)
    end

  let process st (p : string * string) =
    if not (Hashtbl.mem st.processed p) then begin
      Hashtbl.replace st.processed p ();
      st.n_proc <- st.n_proc + 1;
      if verbose then
        Printf.eprintf "[%d] %s %s %.1fs\n%!" st.n_proc (fst p) (snd p)
          (Sys.time ());
      let rw = rows_of st.ar p in
      let r = slice st.ar p in
      let df =
        Cg.dependees r rw.r_fdefs rw.r_slots rw.r_links cfg_active
          default_feature st.rc p
      in
      let da = Cg.addlDependees r rw.r_fdefs rw.r_slots cfg_active st.rc p in
      let sup =
        Cg.supportAt r rw.r_supp rw.r_fdefs rw.r_slots cfg_active st.rc p
      in
      let rfc = support_owners sup in
      record_deprel st (Red.reduceDeps rfc sup df da gp);
      record_real st (Red.reduceReal rfc sup df da gp)
    end

  (* the Cargo crate owning an encoded package, recoverable from the name
     alone: every row of the translation is minted by one crate version *)
  let owner_of_np (np : Cg.NPlus.t) (u : Cg.VPlus.t) =
    match (np, u) with
    | Cg.NPlus.Root, _ -> `Root
    | Cg.NPlus.Crate n, Cg.VPlus.VOrig v -> `Crate (n, v)
    | Cg.NPlus.SlotN (n, v, _), _ -> `Crate (n, v)
    | Cg.NPlus.DecisionN (n, v, _, _, _), _ -> `Crate (n, v)
    | _ -> `None

  let owner_of ((nm, u) : T.Pkg.t) =
    match nm with
    | Red.Name.GranularOrig (np, _) -> owner_of_np np u
    | Red.Name.GranularFeatPkg (np, _, _) -> owner_of_np np u
    | Red.Name.Intermediate (np, w, _) -> owner_of_np np w
    | Red.Name.IntermediateF (np, w, _, _) -> owner_of_np np w
    | Red.Name.IntermediateA (np, w, _, _, _) -> owner_of_np np w

  let touch st q =
    match owner_of q with
    | `Root -> process_root st
    | `Crate p -> process st p
    | `None -> ()

  (* ---- the per-name version lookups ---- *)

  let link_rows st (l : string) =
    match Hashtbl.find_opt st.ar.links_idx l with Some x -> x | None -> []

  (* Cargo.versions on the slice each name's lookup theorem allows: the
     name's own repository rows for a crate, and the owning crate's rows
     for a slot, decision or link gadget *)
  let np_versions st (np : Cg.NPlus.t) : Cg.VPlus.t list =
    (* every shape but LinkN is a function of rows already loaded when the
       query is asked, so memoizing is safe; LinkN is not (see solve) *)
    let memo = match np with Cg.NPlus.LinkN _ -> false | _ -> true in
    match if memo then Hashtbl.find_opt st.npv_cache np else None with
    | Some vs -> vs
    | None ->
        let vs =
          let call r fdefs slots links =
            Cg.FC.VSet.elements
              (Cg.versions r fdefs slots links cfg_active st.rc np)
          in
          match np with
          | Cg.NPlus.Root ->
              call Cg.PkgSet.empty Cg.FDefRel.empty Cg.SlotRel.empty
                Cg.LinkRel.empty
          | Cg.NPlus.Crate n ->
              call (name_set st.ar n) Cg.FDefRel.empty Cg.SlotRel.empty
                Cg.LinkRel.empty
          | Cg.NPlus.SlotN (n, v, _) ->
              let rw = rows_of st.ar (n, v) in
              call
                (slice st.ar (n, v))
                Cg.FDefRel.empty rw.r_slots Cg.LinkRel.empty
          | Cg.NPlus.DecisionN (n, v, _, _, _) ->
              let rw = rows_of st.ar (n, v) in
              call (slice st.ar (n, v)) rw.r_fdefs rw.r_slots Cg.LinkRel.empty
          | Cg.NPlus.LinkN l ->
              let rs = link_rows st l in
              (* PkgSet.inter R (linkPkgs Links l): versions_lookupLink is
                 hypothesis-free only because the declarers are cut down to
                 repository rows here, rather than because links_idx happens
                 to be built from them *)
              let r =
                Cg.PkgSet.ofList
                  (List.filter (fun (n, v) -> meta st.ar n v <> None) rs)
              in
              let links = Cg.LinkRel.ofList (List.map (fun q -> (q, l)) rs) in
              call r Cg.FDefRel.empty Cg.SlotRel.empty links
        in
        if memo then Hashtbl.replace st.npv_cache np vs;
        vs

  (* the FC support at an encoded package: a crate version carries its own
     features, and a decision gadget carries the witness feature *)
  let fc_support st (np : Cg.NPlus.t) (u : Cg.VPlus.t) (f : Cg.FPlusComp.t) =
    match (np, u, f) with
    | Cg.NPlus.Crate n, Cg.VPlus.VOrig v, Cg.FPlusComp.FOrigF f0 ->
        has_feature st.ar (n, v) f0
    | Cg.NPlus.DecisionN _, _, Cg.FPlusComp.FWit -> true
    | _ -> false

  let versions st (nm : Red.Name.name) : Cg.VPlus.t list =
    match nm with
    | Red.Name.GranularOrig (np, w) ->
        List.filter (fun u -> gp u = w) (np_versions st np)
    | Red.Name.GranularFeatPkg (np, f, w) ->
        List.filter
          (fun u -> gp u = w && fc_support st np u f)
          (np_versions st np)
    | _ -> (
        (* an intermediate is minted by its owner's rows alone *)
        (match owner_of (nm, Cg.VPlus.VUnit) with
        | `Root -> process_root st
        | `Crate p -> process st p
        | `None -> ());
        match Hashtbl.find_opt st.gadget_vers nm with
        | Some vs -> vs
        | None -> [])

  (* ---- PubGrub ---- *)

  module PName = struct
    type t = Red.Name.name

    let compare a b = r2c (Red.Name.compare a b)

    let pp_np fmt (np : Cg.NPlus.t) =
      match np with
      | Cg.NPlus.Root -> Format.fprintf fmt "root"
      | Cg.NPlus.Crate n -> Format.fprintf fmt "%s" n
      | Cg.NPlus.LinkN l -> Format.fprintf fmt "links:%s" l
      | Cg.NPlus.SlotN (n, v, a) -> Format.fprintf fmt "%s@%s->%s" n v a
      | Cg.NPlus.DecisionN (n, v, f, a, g) ->
          Format.fprintf fmt "%s@%s[%s]->%s/%s" n v f a g

    let pp_f fmt (f : Cg.FPlusComp.t) =
      match f with
      | Cg.FPlusComp.FOrigF x -> Format.fprintf fmt "%s" x
      | Cg.FPlusComp.FWit -> Format.fprintf fmt "wit"

    let pp fmt (n : t) =
      match n with
      | Red.Name.GranularOrig (np, _) -> pp_np fmt np
      | Red.Name.GranularFeatPkg (np, f, _) ->
          Format.fprintf fmt "%a/%a" pp_np np pp_f f
      | Red.Name.Intermediate (np, _, m) ->
          Format.fprintf fmt "<%a=>%a>" pp_np np pp_np m
      | Red.Name.IntermediateF (np, _, m, f) ->
          Format.fprintf fmt "<%a=>%a/%a>" pp_np np pp_np m pp_f f
      | Red.Name.IntermediateA (np, _, f, m, g) ->
          Format.fprintf fmt "<%a/%a=>%a/%a>" pp_np np pp_f f pp_np m pp_f g
  end

  module PVersion = struct
    type t = Cg.VPlus.t

    let compare a b = r2c (Cg.VPlus.compare a b)

    let pp fmt (v : t) =
      match v with
      | Cg.VPlus.VOrig v -> Format.fprintf fmt "%s" v
      | Cg.VPlus.VChoice v -> Format.fprintf fmt "choose:%s" v
      | Cg.VPlus.VFire v -> Format.fprintf fmt "fire:%s" v
      | Cg.VPlus.VOff -> Format.fprintf fmt "off"
      | Cg.VPlus.VMember (n, v) -> Format.fprintf fmt "member:%s@%s" n v
      | Cg.VPlus.VUnit -> Format.fprintf fmt "()"
  end

  module PG = Pubgrub.Make (PName) (PVersion)

  let root_name = Red.Name.GranularOrig (Cg.NPlus.Root, Cg.GPlus.GUnit)

  type result = {
    crates : (string * string) list;
    feats : (string * string * string list) list;
    sel : (string * string * string * string) list;
    nodes : int;
    processed : int;
  }

  let solve ?(debug = false) ?(rfeats = root_feats) ar (rc : string * string) =
    Pubgrub.set_debug debug;
    let st = mk_state ar rc rfeats in
    let versions nm = versions st nm in
    (* the decisive memoization: PubGrub asks for the same node's
       dependencies over and over during propagation *)
    let cache = Hashtbl.create 65536 in
    let dependencies nm (u : Cg.VPlus.t) =
      match Hashtbl.find_opt cache (nm, u) with
      | Some r -> r
      | None ->
          touch st (nm, u);
          let hs =
            match Hashtbl.find_opt st.edges (nm, u) with
            | Some x -> x
            | None -> T.DependeesSet.empty
          in
          let r =
            List.map
              (fun ((m, vs) : T.Dependees.t) ->
                (m, PG.Ranges.of_list (T.VSet.elements vs)))
              (T.DependeesSet.elements hs)
          in
          Hashtbl.replace cache (nm, u) r;
          r
    in
    (* LinkN l's versions are the whole preimage of the link relation at l,
       and no row of any one declarer names the others, so this is the one
       query lazy loading cannot complete from what a loaded crate carries.
       It needs no remedy beyond not memoizing it: PubGrub asks versions
       afresh at every decision, so recomputing the filter over links_idx --
       a handful of rows -- lets a declarer loaded later simply be there.
       Caching it instead would freeze the answer mid-run and a late
       declarer would be refused against a version set fixed without it. *)
    match
      PG.solve ~versions ~dependencies
        [ (root_name, PG.Ranges.of_list [ Cg.VPlus.VUnit ]) ]
    with
    | Error inc ->
        Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc;
        None
    | Ok sol ->
        let s = T.PkgSet.ofList sol in
        (* back through the proved decoders *)
        let s_fc = Red.featureConcurrentResolution gp s in
        let crates = Cg.PkgSet.elements (Cg.decodeS s_fc) in
        let feats =
          List.map
            (fun (((n, v), fs) : Cg.Featured.t) -> (n, v, Cg.FSet.elements fs))
            (Cg.FeaturedSet.elements (Cg.decodeFS s_fc))
        in
        let sel =
          List.map
            (fun ((((n, v), a), u) : Cg.SelElt.t) -> (n, v, a, u))
            (Cg.SelRel.elements (Cg.decodeSel s_fc))
        in
        Some
          {
            crates = List.sort compare crates;
            feats;
            sel;
            nodes = List.length sol;
            processed = st.n_proc;
          }
end
