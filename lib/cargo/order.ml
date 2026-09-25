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

  val root_features : Cargo_query.features
  val meta : crate -> P.ver option
  val candidates : P.dep -> int
  val root_step : assigned -> name option
  val dep_step : assigned -> crate -> P.dep -> name step
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

  type t = { mutable state : state; mutable trail : entry list }

  let create () =
    {
      state = { rooted = false; queue = Q.empty; act = CM.empty; clock = 0 };
      trail = [];
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

  let rec advance ~assigned st =
    if not st.rooted then
      match D.root_step assigned with
      | Some n -> (st, Some n)
      | None -> (
          let st = { st with rooted = true } in
          match D.meta D.root with
          | None -> (st, None)
          | Some m ->
              let st =
                match D.root_features with
                | Cargo_query.All ->
                    frame st D.root m ~root:true ~all:true SS.empty true
                | Cargo_query.Named { feats; default } ->
                    frame st D.root m ~root:true ~all:false (SS.of_list feats)
                      default
              in
              advance ~assigned st)
    else
      match Q.min_elt_opt st.queue with
      | None -> (st, None)
      | Some it -> (
          let rest = { st with queue = Q.remove it st.queue } in
          match D.dep_step assigned it.parent it.dep with
          | Decide n -> (st, Some n)
          | Skip -> advance ~assigned rest
          | Activated c -> advance ~assigned (activate rest it c))

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
          sync t ~assigned)

  let next t ~assigned open_names =
    sync t ~assigned;
    let st, n = advance ~assigned t.state in
    t.state <- st;
    let n =
      match n with
      | Some n when List.exists (fun (m, _) -> D.equal m n) open_names -> n
      | _ ->
          (* a name nothing cargo activates reached: PubGrub's own order *)
          fst (List.hd open_names)
    in
    t.trail <- { name = n; value = None; pre = st } :: t.trail;
    n
end
