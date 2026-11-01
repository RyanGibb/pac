module Make
    (Encoding : Encoding.S)
    (L : module type of Lookups.Make (Encoding)) =
struct
  open Encoding

  type t = {
    lk : L.state;
    cands : (string * Cargo_version.req, string list) Hashtbl.t;
    enabled :
      ( string * string * string list * bool,
        (Cargo_parse.dep * Order.StringSet.t) list )
      Hashtbl.t;
  }

  let create lk =
    { lk; cands = Hashtbl.create 4096; enabled = Hashtbl.create 4096 }

  let decided assigned x =
    match assigned x with Resolver.Decided v -> Some v | _ -> None

  let decided_v assigned x =
    Option.map (fun (pv : PVersion.t) -> pv.PVersion.v) (decided assigned x)

  let is_open assigned x =
    match assigned x with Resolver.Entailed _ -> true | _ -> false

  (* what the registry query returns for one dependency record, in the
     order sort_summaries leaves it (version_prefs.rs): MSRV-compatible
     first when a toolchain is set, newest first within each.  The
     requirement is read by the comparator the encoding is handed through
     xreq, so these are the members of the granularity classes the slot
     offers. *)
  let candidates pk (d : Cargo_parse.dep) =
    Pac_common.Tbl.memo pk.cands (d.Cargo_parse.d_name, d.Cargo_parse.d_req)
      (fun () ->
        let fits u = L.msrv_fits pk.lk (d.Cargo_parse.d_name, u) in
        List.stable_sort
          (fun a b ->
            match (fits a, fits b) with
            | true, false -> -1
            | false, true -> 1
            | _ -> Cargo_version.compare b a)
          (List.filter
             (fun u -> Cargo_version.holds u d.Cargo_parse.d_req)
             (L.versions_of pk.lk d.Cargo_parse.d_name)))

  let enabled_deps pk t u feats default =
    Pac_common.Tbl.memo pk.enabled
      (t, u, Order.StringSet.elements feats, default)
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
    live : string -> string -> Order.StringSet.t -> bool -> bool;
  }

  let lookahead pk ~assigned =
    let st = pk.lk in
    let links_free t u gr =
      match L.meta st t u with
      | Some { Cargo_parse.v_links = Some l; _ } -> (
          match decided_v assigned (Cargo.Reduction.Name.CCls l) with
          | Some
              (Cargo.Reduction.Version.WName
                 (Cargo.Reduction.Name.CGran (t', gr'))) ->
              t' = t && gr' = gr
          | _ -> true)
      | _ -> true
    in
    let valid_memo = Hashtbl.create 64 in
    let valid t u =
      Pac_common.Tbl.memo valid_memo (t, u) (fun () ->
          let gr = L.granularity st u in
          let g = Cargo.Reduction.Name.CGran (t, gr) in
          (match assigned g with
            | Resolver.Decided
                { PVersion.v = Cargo.Reduction.Version.WOrig w; _ } ->
                Cargo_version.compare w u = 0
            | Resolver.Entailed r ->
                Resolver.Ranges.contains
                  (L.tag st g (Cargo.Reduction.Version.WOrig u))
                  r
            | _ -> true)
          && links_free t u gr)
    in
    (* a candidate one of whose mandatory dependencies has no valid candidate
       left, or only a dead one: cargo backtracks from it and its conflict
       cache then skips it (past_conflicting_activations), while PubGrub learns
       the same one slot at a time, each lesson a backjump; what it has learned
       is out of sight here, so the chain of forced candidates is followed a
       few steps instead. *)
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
      Pac_common.Tbl.memo dead_memo
        (depth, chain, t, u, Order.StringSet.elements feats, default)
        (fun () ->
          List.exists
            (fun ((d : Cargo_parse.dep), fs) ->
              let t' = d.Cargo_parse.d_name
              and dflt = d.Cargo_parse.d_default in
              match first_two t' [] (candidates pk d) with
              | [] -> true
              | [ w ] -> chain > 0 && dead depth (chain - 1) t' w fs dflt
              | _ ->
                  depth > 0
                  && List.for_all
                       (fun w ->
                         (not (valid t' w))
                         || dead (depth - 1) chain t' w fs dflt)
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
    | None -> Order.StringSet.empty
    | Some mm ->
        List.fold_left
          (fun acc (f, _) ->
            let x = Cargo.Reduction.Name.CFeatP (m, f, gr) in
            match assigned x with
            | Resolver.Entailed r
              when Resolver.Ranges.contains
                     (L.tag st x (Cargo.Reduction.Version.WOrig u))
                     r ->
                Order.StringSet.add f acc
            | Resolver.Decided
                { PVersion.v = Cargo.Reduction.Version.WOrig w; _ }
              when Cargo_version.compare w u = 0 ->
                Order.StringSet.add f acc
            | _ -> acc)
          Order.StringSet.empty mm.Cargo_parse.v_feats

  let choose pk ~assigned tn (cands : PVersion.t list) =
    let st = pk.lk in
    let la = lookahead pk ~assigned in
    let offered w =
      List.find_opt
        (fun (c : PVersion.t) ->
          Cargo.Reduction.Version.compare c.PVersion.v w = Pac.Eq)
        cands
    in
    let walk (d : Cargo_parse.dep) =
      List.find_map
        (fun u ->
          if
            la.live d.Cargo_parse.d_name u
              (Order.StringSet.of_list d.Cargo_parse.d_feats)
              d.Cargo_parse.d_default
          then offered (Cargo.Reduction.Version.WClass (L.granularity st u))
          else None)
        (candidates pk d)
    in
    let pick =
      match tn with
      | Cargo.Reduction.Name.CSlot (_, _, d) ->
          Option.bind (L.slot_dep st d) walk
      | Cargo.Reduction.Name.CDec (n, gr, _, d, _) -> (
          match decided_v assigned (Cargo.Reduction.Name.CSlot (n, gr, d)) with
          | Some w -> offered w
          | None -> Option.bind (L.slot_dep st d) walk)
      | Cargo.Reduction.Name.CGran (m, gr) ->
          List.find_opt
            (fun (c : PVersion.t) ->
              match c.PVersion.v with
              | Cargo.Reduction.Version.WOrig u ->
                  la.links_free m u gr
                  && la.live m u (asked st ~assigned m gr u) false
              | _ -> true)
            (List.sort (fun a b -> PVersion.compare b a) cands)
      | Cargo.Reduction.Name.CFeatP (m, _, gr) ->
          Option.bind
            (decided_v assigned (Cargo.Reduction.Name.CGran (m, gr)))
            offered
      | _ -> None
    in
    match pick with
    | Some c -> c
    | None -> Pac_common.Order.greatest PVersion.compare cands

  (* processing one of cargo's dependencies is, in the encoding, the slot,
     then what the parent delivers to it at that site, then the granularity
     class's crate, then the dependee's own features, forced by then.  The
     deliveries go before the crate so that its version is chosen seeing
     every feature asked of it, as cargo's candidate is activated with
     them. *)
  module Driver (S : sig
    val pk : t
  end) =
  struct
    let pk = S.pk
    let st = pk.lk

    type name = Cargo.Reduction.Name.t
    type version = PVersion.t
    type selection = Resolver.selection
    type assigned = name -> selection

    let equal a b = Cargo.Reduction.Name.compare a b = Pac.Eq
    let decided = decided
    let version_equal a b = PVersion.compare a b = 0
    let root = L.root st
    let root_features = L.root_features st
    let meta (n, v) = L.meta st n v
    let candidates d = List.length (candidates pk d)
    let choose ~assigned tn cands = choose pk ~assigned tn cands

    let owned (t, u) gr =
      match meta (t, u) with
      | None -> []
      | Some m -> (
          List.map
            (fun (f, _) -> Cargo.Reduction.Name.CFeatP (t, f, gr))
            m.Cargo_parse.v_feats
          @
          match m.Cargo_parse.v_links with
          | Some l -> [ Cargo.Reduction.Name.CCls l ]
          | None -> [])

    let root_step assigned =
      let n, v = root in
      let gr = L.granularity st v in
      List.find_opt (is_open assigned)
        (Cargo.Reduction.Name.CRoot
        :: Cargo.Reduction.Name.CGran (n, gr)
        :: owned (n, v) gr)

    (* the decisions for what (n, v) delivers to d's site: every dependency
       feature one of its features names under d's alias *)
    let delivered (n, v) gr0 sd (d : Cargo_parse.dep) =
      match meta (n, v) with
      | None -> []
      | Some m ->
          List.concat_map
            (fun (f, es) ->
              List.filter_map
                (function
                  | Cargo_parse.FDepFeat (a, f')
                  | Cargo_parse.FWeakFeat (a, f')
                    when a = d.Cargo_parse.d_alias ->
                      Some (Cargo.Reduction.Name.CDec (n, gr0, f, sd, f'))
                  | _ -> None)
                es)
            m.Cargo_parse.v_feats

    (* once the dependee crate is decided, its owned names, then the
       activation that ends the dependency's processing *)
    let crate_step assigned t gr =
      let g = Cargo.Reduction.Name.CGran (t, gr) in
      match assigned g with
      | Resolver.Entailed _ -> Order.Decide g
      | Resolver.Decided { PVersion.v = Cargo.Reduction.Version.WOrig u; _ }
        -> (
          match List.find_opt (is_open assigned) (owned (t, u) gr) with
          | Some x -> Order.Decide x
          | None -> Order.Activated (t, u))
      | _ -> Order.Skip

    let dep_step assigned (n, v) (d : Cargo_parse.dep) =
      match L.site_data st (n, v) (site_key d) with
      | None -> Order.Skip
      | Some sd -> (
          let gr0 = L.granularity st v in
          let sigma = Cargo.Reduction.Name.CSlot (n, gr0, sd) in
          match assigned sigma with
          | Resolver.Entailed _ -> Order.Decide sigma
          | Resolver.Decided
              { PVersion.v = Cargo.Reduction.Version.WClass gr; _ } -> (
              match
                List.find_opt (is_open assigned) (delivered (n, v) gr0 sd d)
              with
              | Some x -> Order.Decide x
              | None -> crate_step assigned d.Cargo_parse.d_name gr)
          | _ -> Order.Skip)
  end
end
