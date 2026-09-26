open Encoding
module P = Cargo_parse
module Q = Cargo_query
module Tbl = Pac_common.Tbl

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

type owner_key =
  [ `Slot of string * string * Cg.SlotData.t
  | `Dec of string * string * string * Cg.SlotData.t * string ]

(* One solve's archive, request and memo tables.  Every table is keyed as
   narrowly as it is because this record is: a second solve builds its
   own, so no answer outlives the archive and root it was computed for. *)
type state = {
  ar : Archive.t;
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
  msrv : (string * string, bool) Hashtbl.t;
  supports : (string, Cg.SupportSet.t) Hashtbl.t;
  owners : (owner_key, Cg.SlotRel.t * Cg.FDefRel.t) Hashtbl.t;
  site_datas :
    ((string * string) * Cg.SlotKey.t, Cg.SlotData.t option) Hashtbl.t;
  (* the tagged list, not just the untagged one, has to be memoized:
     PubGrub asks a name for its versions at every propagation step *)
  pg_vers : (Cg.NPlus.t, PVersion.t list) Hashtbl.t;
  (* at each decision PubGrub's dependency_incomps asks for the
     dependencies of the decided version's neighbours, once per
     dependency, to widen each incompatibility's range *)
  pg_deps : (Cg.NPlus.t * Cg.VPlus.t, (Cg.NPlus.t * PG.Ranges.t) list) Hashtbl.t;
}

let create ar (root : Q.root) ~features ~rustv =
  {
    ar;
    rc = Q.crate root;
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
    owners = Hashtbl.create 4096;
    site_datas = Hashtbl.create 4096;
    pg_vers = Hashtbl.create 65536;
    pg_deps = Hashtbl.create 65536;
  }

let granularity st v = Tbl.memo st.granularities v (fun () -> granularity_of v)
let meta st n v = Archive.meta st.ar n v
let versions_of st n = Archive.versions_of st.ar n

let fibres_of st (p : string * string) : fibres =
  Tbl.memo st.fibres p (fun () ->
      let n, v = p in
      match meta st n v with
      | None -> empty_fibres n
      | Some m ->
          let ds = slots_of ~root:(p = st.rc) m in
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
  Tbl.memo st.name_sets n (fun () ->
      Cg.PkgSet.ofList (List.map (fun v -> (n, v)) (versions_of st n)))

let repo_preimage st (p : string * string) : Cg.PkgSet.t =
  let reads = (fibres_of st p).r_reads in
  Tbl.memo st.repo_preimages reads (fun () ->
      Cg.PkgSet.unions (List.map (name_set st) reads))

(* whether (n, v) fits the toolchain resolver v3 ranks against; every
   version does when there is none *)
let msrv_fits st ((n, v) : string * string) : bool =
  match st.rustv with
  | None -> true
  | Some rustc ->
      Tbl.memo st.msrv (n, v) (fun () ->
          match meta st n v with
          | None -> true
          | Some m -> msrv_ok rustc m.P.v_msrv)

(* the support relation at a name -- Lookup.supportPreimage at {n},
   which versions_lookupFeatP reads -- as the union of its versions'
   fibres.  Memoized for the same reason name_set is: load_name takes a
   name whole, so this cannot grow once it has been asked. *)
let support_of_name st (n : string) : Cg.SupportSet.t =
  Tbl.memo st.supports n (fun () ->
      Cg.SupportSet.unions
        (List.map
           (fun (v : P.ver) -> (fibres_of st (n, v.P.v_vers)).r_supp)
           (Archive.load_name st.ar n)))

(* the owner versions_lookup{Slot,Decision} name: a version of n in
   granularity class gr whose own declarations make the name, found by
   scanning n's index entry, which holds every version of n and is loaded
   whole.  With none, the empty fibres stand for slot_declines and
   decision_declines: nothing in the instance makes the name, and the
   lookup declines.  The verdict reads st.rc through slotActive. *)
let owner st key (ok : string * string -> fibres -> bool) n gr =
  Tbl.memo st.owners key (fun () ->
      match
        List.find_map
          (fun v ->
            if granularity st v = gr then
              let rw = fibres_of st (n, v) in
              if ok (n, v) rw then Some rw else None
            else None)
          (versions_of st n)
      with
      | Some rw -> (rw.r_slots, rw.r_fdefs)
      | None -> (Cg.SlotRel.empty, Cg.FDefRel.empty))

let slot_owner st n gr d =
  fst
    (owner st
       (`Slot (n, gr, d))
       (fun p rw -> Cg.SlotRel.mem (p, d) rw.r_slots && Cg.slotActive st.rc p d)
       n gr)

let dec_owner st n gr f d feat =
  owner st
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
      let slots = slot_owner st n gr d in
      call { empty_sub with repo = name_set st (Cg.sTarget d); slots }
  | Cg.NPlus.CDec (n, gr, f, d, feat) ->
      let slots, fdefs = dec_owner st n gr f d feat in
      call { empty_sub with repo = name_set st (Cg.sTarget d); fdefs; slots }
  | Cg.NPlus.CLink l ->
      (* Lookup.claimants and LinkFibred.headFibre at l, over the
         declarers loaded so far; see Archive.t *)
      let rs = Archive.link_preimage st.ar l in
      let links = Cg.LinkRel.ofList (List.map (fun q -> (q, l)) rs) in
      let repo =
        Cg.PkgSet.ofList (List.filter (fun (n, v) -> meta st n v <> None) rs)
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
      let slots = slot_owner st n gr d in
      call { empty_sub with repo = name_set st (Cg.sTarget d); slots }
  | Cg.NPlus.CDec (n, gr, f, d, feat), Cg.VPlus.WClass _ ->
      let slots, fdefs = dec_owner st n gr f d feat in
      call { empty_sub with repo = name_set st (Cg.sTarget d); fdefs; slots }
  | _, _ -> []

(* the dependency the owner's fibre holds at a site, which is what a slot
   name carries: the order replay reads raw manifest records, which
   slots_of has not merged, so the name is taken from the fibre *)
let site_data st (p : string * string) (k : Cg.SlotKey.t) =
  Tbl.memo st.site_datas (p, k) (fun () ->
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
  match (tn, w) with
  | (Cg.NPlus.CCrate (n, _) | Cg.NPlus.CFeatP (n, _, _)), Cg.VPlus.WOrig v ->
      { PVersion.msrv = msrv_fits st (n, v); v = w }
  | _ -> { PVersion.msrv = true; v = w }

(* CLink l is the one name that cannot be held (see Archive.t); a memo
   would freeze its answer mid-run and refuse a declarer loaded later
   against a set fixed without it *)
let pg_versions st tn =
  match tn with
  | Cg.NPlus.CLink _ -> List.map (tag st tn) (versions st tn)
  | _ -> Tbl.memo st.pg_vers tn (fun () -> List.map (tag st tn) (versions st tn))

let pg_dependencies st tn ({ PVersion.v = w; _ } : PVersion.t) =
  Tbl.memo st.pg_deps (tn, w) (fun () ->
      List.map
        (fun ((m, vs) : T.Dependees.t) ->
          (m, PG.Ranges.of_list (List.map (tag st m) (T.VSet.elements vs))))
        (dependees st (tn, w)))
