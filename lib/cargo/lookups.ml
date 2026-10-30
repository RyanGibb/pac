module P = Cargo_parse
module Q = Cargo_query
module Tbl = Pac_common.Tbl

module Make (Encoding : Encoding.S) = struct
  open Encoding

  type fibres = {
    r_slots : Cg.SlotRel.t;
    r_fdefs : Cg.FDefRel.t;
    r_links : Cg.LinkRel.t;
    r_supp : Cg.SupportSet.t;
    r_reads : string list; (* own name plus its slots' dependee names *)
  }

  let empty_fibres n =
    {
      r_slots = Cg.SlotRel.empty;
      r_fdefs = Cg.FDefRel.empty;
      r_links = Cg.LinkRel.empty;
      r_supp = Cg.SupportSet.empty;
      r_reads = [ n ];
    }

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
    dep_of_data : (Cg.SlotData.t, P.dep) Hashtbl.t;
    name_sets : (string, Cg.PkgSet.t) Hashtbl.t;
    name_versions : (string, Cg.VSet.t) Hashtbl.t;
    msrv : (string * string, bool) Hashtbl.t;
    (* a name's support pairs by feature, which support_at builds sets of *)
    support_pairs_at :
      (string, (string, ((string * string) * string) list) Hashtbl.t) Hashtbl.t;
    supports : (string * string, Cg.SupportSet.t) Hashtbl.t;
    site_datas :
      ((string * string) * Cg.Site.t, Cg.SlotData.t option) Hashtbl.t;
    (* the tagged list, not just the untagged one, has to be memoized:
       PubGrub asks a name for its versions at every propagation step *)
    pg_vers : (Cg.Reduction.NPlus.t, PVersion.t list) Hashtbl.t;
    (* at each decision PubGrub's dependency_incomps asks for the
       dependencies of the decided version's neighbours, once per
       dependency, to widen each incompatibility's range *)
    pg_deps :
      ( Cg.Reduction.NPlus.t * Cg.Reduction.VPlus.t,
        (Cg.Reduction.NPlus.t * PG.Ranges.t) list )
      Hashtbl.t;
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
      name_versions = Hashtbl.create 4096;
      msrv = Hashtbl.create 65536;
      support_pairs_at = Hashtbl.create 4096;
      supports = Hashtbl.create 4096;
      site_datas = Hashtbl.create 4096;
      pg_vers = Hashtbl.create 65536;
      pg_deps = Hashtbl.create 65536;
    }

  let root st = st.rc
  let root_features st = st.features
  let slot_dep st sd = Hashtbl.find_opt st.dep_of_data sd
  let dependency_lookups st = Hashtbl.length st.pg_deps

  let granularity st v =
    Tbl.memo st.granularities v (fun () -> granularity_of v)

  let meta st n v = Archive.meta st.ar n v
  let versions_of st n = Archive.versions_of st.ar n

  (* a version's support pairs, one per key of its feature table, which
     with_implicit_features has completed *)
  let support_pairs p (m : P.ver) = List.map (fun (f, _) -> (p, f)) m.P.v_feats

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
            let supp = Cg.SupportSet.ofList (support_pairs p m) in
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
                  (n :: List.map (fun (d : P.dep) -> d.P.d_name) ds);
            })

  let slots_and_fdefs st p =
    let r = fibres_of st p in
    (r.r_slots, r.r_fdefs)

  let name_set st (n : string) : Cg.PkgSet.t =
    Tbl.memo st.name_sets n (fun () ->
        Cg.PkgSet.ofList (List.map (fun v -> (n, v)) (versions_of st n)))

  (* the Vq the dependees lookups take, C.versions at a name: loaded
     whole, as name_set is *)
  let name_versions st (m : string) : Cg.VSet.t =
    Tbl.memo st.name_versions m (fun () -> Cg.VSet.ofList (versions_of st m))

  let msrv_fits st ((n, v) : string * string) : bool =
    match st.rustv with
    | None -> true
    | Some rustc ->
        Tbl.memo st.msrv (n, v) (fun () ->
            match meta st n v with
            | None -> true
            | Some m -> msrv_ok rustc m.P.v_msrv)

  (* the support relation at a name and feature -- Lookup.supportAt n f,
     which versions_lookupFeatP reads -- from its versions' support pairs.
     Memoized for the same reason name_set is: load_name takes a name whole,
     so this cannot grow once it has been asked. *)
  let support_at st (n : string) (f : string) : Cg.SupportSet.t =
    Tbl.memo st.supports (n, f) (fun () ->
        let by_feature =
          Tbl.memo st.support_pairs_at n (fun () ->
              let h = Hashtbl.create 64 in
              List.iter
                (fun (v : P.ver) ->
                  match meta st n v.P.v_vers with
                  | None -> ()
                  | Some m ->
                      List.iter
                        (fun ((_, f) as x) -> Tbl.push h f x)
                        (support_pairs (n, v.P.v_vers) m))
                (Archive.load_name st.ar n);
              h)
        in
        Cg.SupportSet.ofList (Tbl.find_list by_feature f))

  (* every lookup theorem carries the request (granularity, default, rc,
     rootFeats) whole, so its instance differs from this one only in the
     relations it names *)
  let empty_inst st : Cg.coq_Inst =
    {
      Cg.inst_repo = Cg.PkgSet.empty;
      inst_support = Cg.SupportSet.empty;
      inst_fdefs = Cg.FDefRel.empty;
      inst_slots = Cg.SlotRel.empty;
      inst_links = Cg.LinkRel.empty;
      inst_gran = granularity st;
      inst_default = P.default_feature;
      inst_root = st.rc;
      inst_rootFeats = st.rfeats;
    }

  (* one branch per versions_lookup{Root,Granular,FeatP,Slot,Decision,Link},
     each filling in the components its theorem names and nothing else *)
  let versions st (tn : Cg.Reduction.NPlus.t) : Cg.Reduction.VPlus.t list =
    let call i = T.VSet.elements (Cg.Reduction.versions i tn) in
    let e = empty_inst st in
    match tn with
    | Cg.Reduction.NPlus.CRoot -> call e
    | Cg.Reduction.NPlus.CGran (n, _) ->
        call { e with inst_repo = name_set st n }
    | Cg.Reduction.NPlus.CFeatP (n, f, _) ->
        let supp = support_at st n f in
        call { e with inst_repo = name_set st n; inst_support = supp }
    | Cg.Reduction.NPlus.CSlot (_, _, d)
    | Cg.Reduction.NPlus.CDec (_, _, _, d, _) ->
        call { e with inst_repo = name_set st (Cg.sName d) }
    | Cg.Reduction.NPlus.CLink l ->
        (* Lookup.claimants and LinkFibred.headFibre at l, over the
           declarers loaded so far: the answer may only grow
           (versions_link_mono) *)
        let rs = Archive.link_preimage st.ar l in
        let links = Cg.LinkRel.ofList (List.map (fun q -> (q, l)) rs) in
        let repo =
          Cg.PkgSet.ofList (List.filter (fun (n, v) -> meta st n v <> None) rs)
        in
        call { e with inst_repo = repo; inst_links = links }

  (* one branch per dependees_lookup{Root,Granular,FeatP,Slot,Decision}, the
     repository read through name_versions alone; the fall-through is
     dependees_reduceDepsInert, empty.  A crate version's reads are all
     loaded before it answers, an optional slot's dependee too, so that which
     names are loaded, and so a links value's declarers so far, does not
     turn on which ranges the lookup evaluates. *)
  let dependees st (p : T.Pkg.t) : T.Dependees.t list =
    let call i =
      T.DependeesSet.elements (Cg.Reduction.dependeesBy (name_versions st) i p)
    in
    let e = empty_inst st in
    match p with
    | Cg.Reduction.NPlus.CRoot, _ -> call e
    | Cg.Reduction.NPlus.CGran (n, _), Cg.Reduction.VPlus.WOrig v ->
        let rw = fibres_of st (n, v) in
        List.iter (fun m -> ignore (name_versions st m)) rw.r_reads;
        call { e with inst_slots = rw.r_slots; inst_links = rw.r_links }
    | Cg.Reduction.NPlus.CFeatP (n, _, _), Cg.Reduction.VPlus.WOrig v ->
        let rw = fibres_of st (n, v) in
        List.iter (fun m -> ignore (name_versions st m)) rw.r_reads;
        call
          {
            e with
            inst_support = rw.r_supp;
            inst_fdefs = rw.r_fdefs;
            inst_slots = rw.r_slots;
          }
    | ( (Cg.Reduction.NPlus.CSlot _ | Cg.Reduction.NPlus.CDec _),
        Cg.Reduction.VPlus.WClass _ ) ->
        call e
    | _, _ -> []

  let site_data st (p : string * string) (k : Cg.Site.t) =
    Tbl.memo st.site_datas (p, k) (fun () ->
        List.find_map
          (fun ((_, sd) : Cg.SlotElt.t) ->
            if Cg.sSite sd = k then Some sd else None)
          (Cg.SlotRel.elements (fibres_of st p).r_slots))

  (* the preference must land on both names whose candidates are crate
     versions: CFeatP carries WOrig as CGran does, and whichever of the
     two is decided first fixes the version (a decided CFeatP entails its
     CGran; choose gives a later CFeatP its CGran's version), so a family
     left untagged decides by bare semver and the demotion never acts.  A
     granularity class, which CSlot and CDec carry, has no standing: cargo
     ranks the versions a dependency admits and not their granularity
     classes, and which one the ranked walk lands on depends on what is
     already activated, which only choose can see. *)
  let tag st (tn : Cg.Reduction.NPlus.t) (w : Cg.Reduction.VPlus.t) : PVersion.t
      =
    match (tn, w) with
    | ( (Cg.Reduction.NPlus.CGran (n, _) | Cg.Reduction.NPlus.CFeatP (n, _, _)),
        Cg.Reduction.VPlus.WOrig v ) ->
        { PVersion.msrv = msrv_fits st (n, v); v = w }
    | _ -> { PVersion.msrv = true; v = w }

  (* CLink l's versions may only grow (versions_link_mono), so they are not
     held: a memo would refuse a declarer loaded later.  The rest of the
     contract that makes growth safe holds too: its dependees are fixed,
     being none, and every range onto it is an exact set of listed versions,
     built by pg_dependencies with of_list from a loaded declarer's own *)
  let pg_versions st tn =
    match tn with
    | Cg.Reduction.NPlus.CLink _ -> List.map (tag st tn) (versions st tn)
    | _ ->
        Tbl.memo st.pg_vers tn (fun () -> List.map (tag st tn) (versions st tn))

  let pg_dependencies st tn ({ PVersion.v = w; _ } : PVersion.t) =
    Tbl.memo st.pg_deps (tn, w) (fun () ->
        List.map
          (fun ((m, vs) : T.Dependees.t) ->
            (m, PG.Ranges.of_list (List.map (tag st m) (T.VSet.elements vs))))
          (dependees st (tn, w)))
end
