open Encoding
module P = Cargo_parse
module L = Lookups

(* cargo's candidate policy over one solve's lookups, and its memos *)
type t = {
  lk : L.state;
  cands : (string * Cargo_version.req, string list) Hashtbl.t;
  enabled :
    (string * string * string list * bool, (P.dep * Order.SS.t) list) Hashtbl.t;
}

let create lk =
  { lk; cands = Hashtbl.create 4096; enabled = Hashtbl.create 4096 }

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
let candidates pk (d : P.dep) =
  L.memo pk.cands (d.P.d_target, d.P.d_req) (fun () ->
      let fits u = L.msrv_fits pk.lk (d.P.d_target, u) in
      List.stable_sort
        (fun a b ->
          match (fits a, fits b) with
          | true, false -> -1
          | false, true -> 1
          | _ -> Cargo_version.compare b a)
        (List.filter
           (fun u -> Cargo_version.holds u d.P.d_req)
           (L.versions_of pk.lk d.P.d_target)))

let enabled_deps pk t u feats default =
  L.memo pk.enabled
    (t, u, Order.SS.elements feats, default)
    (fun () ->
      match L.meta pk.lk t u with
      | None -> []
      | Some m ->
          let _, deps = Order.requirements m ~all:false feats default in
          Order.enabled ~root:false m deps)

(* how far a lookahead follows a dependency with several valid candidates,
   and how long a chain of single-candidate ones *)
let lookahead_depth = 1
let forced_chain = 3

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

let lookahead pk ~assigned =
  let st = pk.lk in
  let links_free t u gr =
    match L.meta st t u with
    | Some { P.v_links = Some l; _ } -> (
        match decided_v assigned (Cg.NPlus.CLink l) with
        | Some (Cg.VPlus.WName (Cg.NPlus.CCrate (t', gr'))) ->
            t' = t && gr' = gr
        | _ -> true)
    | _ -> true
  in
  let valid_memo = Hashtbl.create 64 in
  let valid t u =
    L.memo valid_memo (t, u) (fun () ->
        let gr = L.granularity st u in
        let g = Cg.NPlus.CCrate (t, gr) in
        (match assigned g with
          | PG.Decided { PVersion.v = Cg.VPlus.WOrig w; _ } ->
              Cargo_version.compare w u = 0
          | PG.Entailed r ->
              PG.Ranges.contains (L.tag st g (Cg.VPlus.WOrig u)) r
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
    L.memo dead_memo
      (depth, chain, t, u, Order.SS.elements feats, default)
      (fun () ->
        List.exists
          (fun ((d : P.dep), fs) ->
            let t' = d.P.d_target and dflt = d.P.d_default in
            match first_two t' [] (candidates pk d) with
            | [] -> true
            | [ w ] -> chain > 0 && dead depth (chain - 1) t' w fs dflt
            | _ ->
                depth > 0
                && List.for_all
                     (fun w ->
                       (not (valid t' w)) || dead (depth - 1) chain t' w fs dflt)
                     (candidates pk d))
          (enabled_deps pk t u feats default))
  in
  let live t u feats default =
    valid t u && not (dead lookahead_depth forced_chain t u feats default)
  in
  { links_free; live }

(* the features the encoding already asks of a crate version: an
   optional dependency they enable can be the one that dies *)
let asked st ~assigned m gr u =
  match L.meta st m u with
  | None -> Order.SS.empty
  | Some mm ->
      List.fold_left
        (fun acc (f, _) ->
          let x = Cg.NPlus.CFeatP (m, f, gr) in
          match assigned x with
          | PG.Entailed r
            when PG.Ranges.contains (L.tag st x (Cg.VPlus.WOrig u)) r ->
              Order.SS.add f acc
          | PG.Decided { PVersion.v = Cg.VPlus.WOrig w; _ }
            when Cargo_version.compare w u = 0 ->
              Order.SS.add f acc
          | _ -> acc)
        Order.SS.empty mm.P.v_feats

let choose pk ~assigned tn (cands : PVersion.t list) =
  let st = pk.lk in
  let la = lookahead pk ~assigned in
  let offered w =
    List.find_opt
      (fun (c : PVersion.t) -> Cg.VPlus.compare c.PVersion.v w = E.Eq)
      cands
  in
  let walk (d : P.dep) =
    List.find_map
      (fun u ->
        if la.live d.P.d_target u (Order.SS.of_list d.P.d_feats) d.P.d_default
        then offered (Cg.VPlus.WClass (L.granularity st u))
        else None)
      (candidates pk d)
  in
  let pick =
    match tn with
    | Cg.NPlus.CSlot (_, _, d) ->
        Option.bind (Hashtbl.find_opt st.L.dep_of_data d) walk
    | Cg.NPlus.CDec (n, gr, _, d, _) -> (
        match decided_v assigned (Cg.NPlus.CSlot (n, gr, d)) with
        | Some w -> offered w
        | None -> Option.bind (Hashtbl.find_opt st.L.dep_of_data d) walk)
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
  val pk : t
end) =
struct
  let pk = S.pk
  let st = pk.lk

  type name = Cg.NPlus.t
  type version = PVersion.t
  type selection = PG.selection
  type assigned = name -> selection

  let equal a b = Cg.NPlus.compare a b = E.Eq
  let decided = decided
  let version_equal a b = PVersion.compare a b = 0
  let root = st.L.rc
  let root_features = st.L.features
  let meta (n, v) = L.meta st n v
  let candidates d = List.length (candidates pk d)
  let choose ~assigned tn cands = choose pk ~assigned tn cands

  let owned (t, u) gr =
    match meta (t, u) with
    | None -> []
    | Some m -> (
        List.map (fun (f, _) -> Cg.NPlus.CFeatP (t, f, gr)) m.P.v_feats
        @ match m.P.v_links with Some l -> [ Cg.NPlus.CLink l ] | None -> [])

  let root_step assigned =
    let n, v = root in
    let gr = L.granularity st v in
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

  (* once the target crate is decided, its owned names, then the
     activation that ends the dependency's processing *)
  let crate_step assigned t gr =
    let g = Cg.NPlus.CCrate (t, gr) in
    match assigned g with
    | PG.Entailed _ -> Order.Decide g
    | PG.Decided { PVersion.v = Cg.VPlus.WOrig u; _ } -> (
        match List.find_opt (is_open assigned) (owned (t, u) gr) with
        | Some x -> Order.Decide x
        | None -> Order.Activated (t, u))
    | _ -> Order.Skip

  let dep_step assigned (n, v) (d : P.dep) =
    match L.site_data st (n, v) (site_key d) with
    | None -> Order.Skip
    | Some sd -> (
        let gr0 = L.granularity st v in
        let sigma = Cg.NPlus.CSlot (n, gr0, sd) in
        match assigned sigma with
        | PG.Entailed _ -> Order.Decide sigma
        | PG.Decided { PVersion.v = Cg.VPlus.WClass gr; _ } -> (
            match
              List.find_opt (is_open assigned) (delivered (n, v) gr0 sd d)
            with
            | Some x -> Order.Decide x
            | None -> crate_step assigned d.P.d_target gr)
        | _ -> Order.Skip)
end
