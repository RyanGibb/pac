(* Cargo's activation order, replayed through PubGrub's next hook.

   activate_deps_loop (core/resolver/mod.rs) keeps the dependencies still
   to activate as frames, one per activation, each holding its crate's
   enabled dependencies sorted by how many candidates the registry offers
   (dep_cache.rs, build_deps: a stable sort, so declaration order breaks
   ties).  pop_most_constrained (types.rs) takes the frame whose next
   dependency has the fewest candidates, the oldest frame among equals, so
   the order over every pending dependency is (candidates, frame age,
   place in the frame).  Processing one picks its candidate and activates
   it, and a crate activated with features it did not yet have gets a
   fresh frame of every dependency those features enable, the mandatory
   ones again among them (flag_activated, then build_deps).

   PubGrub decides one encoded name at a time, so a dependency is
   processed as the run of decisions the driver's step names, and a frame
   is made when the step reports the crate it activated.  A backjump
   undoes a suffix of PubGrub's decisions, and the shadow returns to the
   state it had before the first of them: the order is a function of the
   decisions that stand, as cargo's is of the activations in the context
   it restores. *)

module P = Cargo_parse
module SS = Set.Make (String)

type crate = string * string

(* build_requirements (dep_cache.rs): the features a request turns on, and
   what it asks of each dependency, by alias.  A strong a/f over an
   optional a turning on the feature a is already an entry of the table
   (Cargo_parse.with_implicit_features). *)
let requirements (m : P.ver) ~all feats default =
  let on = ref SS.empty and deps = Hashtbl.create 8 in
  let want a f =
    let s = Option.value (Hashtbl.find_opt deps a) ~default:SS.empty in
    Hashtbl.replace deps a (match f with Some f -> SS.add f s | None -> s)
  in
  let rec feature f =
    if not (SS.mem f !on) then (
      on := SS.add f !on;
      List.iter entry (Option.value (List.assoc_opt f m.P.v_feats) ~default:[]))
  and entry = function
    | P.FFeat f -> feature f
    | P.FDep a -> want a None
    | P.FDepFeat (a, f) | P.FWeakFeat (a, f) -> want a (Some f)
  in
  (* the default the parser adds to a table lacking one is not a key of
     cargo's, and handle_default requires the key *)
  let declared f = f <> P.default_feature || m.P.v_default_declared in
  if all then List.iter (fun (f, _) -> if declared f then feature f) m.P.v_feats;
  SS.iter feature feats;
  if default && declared P.default_feature then feature P.default_feature;
  (!on, deps)

(* a path package's dependencies in the order to_real_manifest gathers them
   (util/toml/mod.rs): dependencies, dev- and build-dependencies, then each
   target's normal, build and dev tables, the targets and the keys of every
   table being BTreeMaps *)
let manifest_order (ds : P.dep list) =
  let rank (d : P.dep) =
    match (d.P.d_cfg, d.P.d_kind) with
    | "", P.Normal -> ("", 0)
    | "", P.Dev -> ("", 1)
    | "", P.Build -> ("", 2)
    | c, P.Normal -> (c, 0)
    | c, P.Build -> (c, 1)
    | c, P.Dev -> (c, 2)
  in
  List.stable_sort
    (fun (a : P.dep) (b : P.dep) ->
      compare (rank a, a.P.d_alias) (rank b, b.P.d_alias))
    ds

(* resolve_features: the dependencies a request enables, each with the
   features it asks of its target *)
let enabled ~root (m : P.ver) deps =
  List.filter_map
    (fun (d : P.dep) ->
      if d.P.d_kind = P.Dev && not root then None
      else
        match Hashtbl.find_opt deps d.P.d_alias with
        | None when d.P.d_optional -> None
        | fs ->
            let fs = Option.value fs ~default:SS.empty in
            Some (d, SS.union fs (SS.of_list d.P.d_feats)))
    (if root then manifest_order m.P.v_deps else m.P.v_deps)

type 'name step = Decide of 'name | Activated of crate | Skip

module type DRIVER = sig
  type name
  type version
  type assigned

  val equal : name -> name -> bool
  val decided : assigned -> name -> version option
  val version_equal : version -> version -> bool
  val root : crate

  (* None when the lock is resolved: every feature and the defaults, as
     CliFeatures::new_all(true) asks *)
  val root_features : string list option
  val meta : crate -> P.ver option
  val candidates : P.dep -> int
  val root_step : assigned -> name option
  val dep_step : assigned -> crate -> P.dep -> name step

  (* the names whose decisions left the choice just made without a live
     candidate, reported once *)
  val doomed : unit -> name list option

  (* whether no candidate of the dependency is live *)
  val hopeless : assigned -> crate -> P.dep -> bool
end

module Make (D : DRIVER) = struct
  type item = {
    count : int;
    time : int;
    idx : int;
    parent : crate;
    dep : P.dep;
    feats : SS.t;
  }

  module Q = Set.Make (struct
    type t = item

    let compare a b =
      compare (a.count, a.time, a.idx) (b.count, b.time, b.idx)
  end)

  module CM = Map.Make (struct
    type t = crate

    let compare = compare
  end)

  (* persistent, so that every trail entry can keep the state it was
     decided from *)
  type state = { rooted : bool; queue : Q.t; act : SS.t CM.t; clock : int }
  type entry = { name : D.name; mutable value : D.version option; pre : state }

  (* A dependency processed with no live candidate left can only be
     refuted, one version at a time, and PubGrub's backjump past the
     decisions that doomed it means a replay to reach it again, in cargo's
     order, behind every dependency queued ahead of it.  Once those
     decisions stand again, and it is still hopeless, it goes first: every
     decision it leads to is refuted and undone, so the answer the replay
     reaches is the same, and only the replays are shorter.  checked is the
     trail depth of a check that found it live, not repeated before a
     backjump goes below it. *)
  type hint = { h_item : item; culprits : D.name list; mutable checked : int }

  type t = {
    mutable state : state;
    mutable trail : entry list;
    mutable depth : int;
    mutable current : item option;
    mutable hints : hint list;
    mutable n_next : int;
    mutable n_fallback : int;
    mutable n_undo : int;
    mutable n_promote : int;
  }

  let create () =
    {
      state = { rooted = false; queue = Q.empty; act = CM.empty; clock = 0 };
      trail = [];
      depth = 0;
      current = None;
      hints = [];
      n_next = 0;
      n_fallback = 0;
      n_undo = 0;
      n_promote = 0;
    }

  let frame st p (m : P.ver) ~root ~all feats default =
    let on, deps = requirements m ~all feats default in
    let ds =
      List.stable_sort
        (fun (a, _) (b, _) -> compare a b)
        (List.map (fun ((d, _) as e) -> (D.candidates d, e)) (enabled ~root m deps))
    in
    let time = st.clock + 1 in
    let queue, _ =
      List.fold_left
        (fun (q, idx) (count, (dep, feats)) ->
          (Q.add { count; time; idx; parent = p; dep; feats } q, idx + 1))
        (st.queue, 0) ds
    in
    let prev = Option.value (CM.find_opt p st.act) ~default:SS.empty in
    { st with queue; clock = time; act = CM.add p (SS.union on prev) st.act }

  (* flag_activated (context.rs): a crate already activated with every
     feature asked of it, default included where it has one, adds no
     frame *)
  let activate st (it : item) c =
    match D.meta c with
    | None -> st
    | Some m -> (
        let default = it.dep.P.d_default in
        match CM.find_opt c st.act with
        | Some prev
          when SS.subset it.feats prev
               && ((not default)
                  || SS.mem P.default_feature prev
                  || not m.P.v_default_declared) ->
            st
        | _ -> frame st c m ~root:false ~all:false it.feats default)

  (* the queue's key can recur on another item once a replay diverges *)
  let same a b = a.dep == b.dep && a.parent = b.parent

  let queued st it =
    match Q.find_opt it st.queue with Some x -> same x it | None -> false

  let promoted t ~assigned st =
    List.find_map
      (fun h ->
        if
          t.depth < h.checked
          && queued st h.h_item
          && List.for_all (fun c -> D.decided assigned c <> None) h.culprits
        then
          if D.hopeless assigned h.h_item.parent h.h_item.dep then (
            t.n_promote <- t.n_promote + 1;
            Some h.h_item)
          else (
            h.checked <- t.depth;
            None)
        else None)
      t.hints

  let rec advance t ~assigned st =
    if not st.rooted then
      match D.root_step assigned with
      | Some n -> (st, Some n)
      | None -> (
          let st = { st with rooted = true } in
          match D.meta D.root with
          | None -> (st, None)
          | Some m ->
              (* named features are the root's featured names exactly, as
                 the encoding's request has them *)
              let st =
                match D.root_features with
                | None -> frame st D.root m ~root:true ~all:true SS.empty true
                | Some fs ->
                    frame st D.root m ~root:true ~all:false (SS.of_list fs)
                      false
              in
              advance t ~assigned st)
    else
      let head =
        match promoted t ~assigned st with
        | Some it -> Some it
        | None -> Q.min_elt_opt st.queue
      in
      match head with
      | None -> (st, None)
      | Some it -> (
          let rest = { st with queue = Q.remove it st.queue } in
          match D.dep_step assigned it.parent it.dep with
          | Decide n ->
              t.current <- Some it;
              (st, Some n)
          | Skip -> advance t ~assigned rest
          | Activated c -> advance t ~assigned (activate rest it c))

  (* PubGrub drops a suffix of its decisions, and a decision it refused on
     the spot as conflicting never lands: either way the entry's name is no
     longer decided as it was *)
  let rec sync t ~assigned =
    match t.trail with
    | [] -> ()
    | e :: rest ->
        let stands =
          match (D.decided assigned e.name, e.value) with
          | Some v, None ->
              e.value <- Some v;
              true
          | Some v, Some w -> D.version_equal v w
          | None, _ -> false
        in
        if not stands then (
          t.state <- e.pre;
          t.trail <- rest;
          t.depth <- t.depth - 1;
          t.n_undo <- t.n_undo + 1;
          sync t ~assigned)

  let next t ~assigned open_names =
    (match (D.doomed (), t.current) with
    | Some culprits, Some it
      when not (List.exists (fun h -> same h.h_item it) t.hints) ->
        t.hints <- { h_item = it; culprits; checked = max_int } :: t.hints
    | _ -> ());
    sync t ~assigned;
    t.current <- None;
    let st, n = advance t ~assigned t.state in
    t.state <- st;
    t.n_next <- t.n_next + 1;
    let n =
      match n with
      | Some n when List.exists (fun (m, _) -> D.equal m n) open_names -> n
      | _ ->
          (* a name nothing cargo activates reached: PubGrub's own order *)
          t.n_fallback <- t.n_fallback + 1;
          fst (List.hd open_names)
    in
    t.trail <- { name = n; value = None; pre = st } :: t.trail;
    t.depth <- t.depth + 1;
    n

  let report t =
    if Sys.getenv_opt "PACORDER" <> None then
      Printf.eprintf "PACORDER next=%d fallback=%d undone=%d promoted=%d\n%!"
        t.n_next t.n_fallback t.n_undo t.n_promote
end
