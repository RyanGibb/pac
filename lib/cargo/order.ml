module StringSet = Set.Make (String)

type crate = string * string

let requirements (m : Cargo_parse.ver) ~all feats default =
  let on = ref StringSet.empty and deps = Hashtbl.create 8 in
  let want a f =
    let s = Option.value (Hashtbl.find_opt deps a) ~default:StringSet.empty in
    Hashtbl.replace deps a
      (match f with Some f -> StringSet.add f s | None -> s)
  in
  let rec feature f =
    if not (StringSet.mem f !on) then (
      on := StringSet.add f !on;
      List.iter entry
        (Option.value (List.assoc_opt f m.Cargo_parse.v_feats) ~default:[]))
  and entry = function
    | Cargo_parse.FFeat f -> feature f
    | Cargo_parse.FDep a -> want a None
    | Cargo_parse.FDepFeat (a, f) | Cargo_parse.FWeakFeat (a, f) ->
        want a (Some f)
  in
  (* the default the parser adds to a table lacking one is not a key of
     cargo's, and handle_default requires the key *)
  let declared f =
    f <> Cargo_parse.default_feature || m.Cargo_parse.v_default_declared
  in
  if all then
    List.iter (fun (f, _) -> if declared f then feature f) m.Cargo_parse.v_feats;
  StringSet.iter feature feats;
  if default && declared Cargo_parse.default_feature then
    feature Cargo_parse.default_feature;
  (!on, deps)

(* a path package's dependencies in the order to_real_manifest gathers them
   (util/toml/mod.rs): dependencies, dev- and build-dependencies, then each
   platform's normal, build and dev tables, the platforms and the keys of
   every table being BTreeMaps *)
let manifest_order (ds : Cargo_parse.dep list) =
  let rank (d : Cargo_parse.dep) =
    match (d.Cargo_parse.d_cfg, d.Cargo_parse.d_kind) with
    | "", Cargo_parse.Normal -> ("", 0)
    | "", Cargo_parse.Dev -> ("", 1)
    | "", Cargo_parse.Build -> ("", 2)
    | c, Cargo_parse.Normal -> (c, 0)
    | c, Cargo_parse.Build -> (c, 1)
    | c, Cargo_parse.Dev -> (c, 2)
  in
  List.stable_sort
    (fun (a : Cargo_parse.dep) (b : Cargo_parse.dep) ->
      compare (rank a, a.Cargo_parse.d_alias) (rank b, b.Cargo_parse.d_alias))
    ds

let enabled ~root (m : Cargo_parse.ver) deps =
  List.filter_map
    (fun (d : Cargo_parse.dep) ->
      if d.Cargo_parse.d_kind = Cargo_parse.Dev && not root then None
      else
        match Hashtbl.find_opt deps d.Cargo_parse.d_alias with
        | None when d.Cargo_parse.d_optional -> None
        | fs ->
            let fs = Option.value fs ~default:StringSet.empty in
            Some
              (d, StringSet.union fs (StringSet.of_list d.Cargo_parse.d_feats)))
    (if root then manifest_order m.Cargo_parse.v_deps else m.Cargo_parse.v_deps)

type 'name step = Decide of 'name | Activated of crate | Skip

module type DRIVER = sig
  type name
  type version
  type selection
  type assigned = name -> selection

  val equal : name -> name -> bool
  val decided : assigned -> name -> version option
  val version_equal : version -> version -> bool
  val root : crate
  val root_features : Cargo_query.features
  val meta : crate -> Cargo_parse.ver option
  val candidates : Cargo_parse.dep -> int
  val root_step : assigned -> name option
  val dep_step : assigned -> crate -> Cargo_parse.dep -> name step
  val choose : assigned:assigned -> name -> version list -> version
end

(* activate_deps_loop (core/resolver/mod.rs): pending dependencies are
   ordered by (candidates, frame age, place in the frame), as build_deps
   sorts a frame stably by candidate count (dep_cache.rs) and
   pop_most_constrained (types.rs) takes the oldest frame among equals.  A
   crate activated with new features gets a fresh frame (flag_activated).
   The order is a function of the decisions that stand, as cargo's is of
   the activations in the context it restores on backtracking. *)
module Make (D : DRIVER) = struct
  type item = {
    count : int;
    time : int;
    idx : int;
    parent : crate;
    dep : Cargo_parse.dep;
    feats : StringSet.t;
  }

  module Queue = Set.Make (struct
    type t = item

    let compare a b = compare (a.count, a.time, a.idx) (b.count, b.time, b.idx)
  end)

  module CrateMap = Map.Make (struct
    type t = crate

    let compare = compare
  end)

  (* persistent, so that every trail entry can keep the state it was
     decided from *)
  type state = {
    rooted : bool;
    queue : Queue.t;
    act : StringSet.t CrateMap.t;
    clock : int;
  }

  type entry = { name : D.name; mutable value : D.version option; pre : state }
  type t = { mutable state : state; mutable trail : entry list }

  let create () =
    {
      state =
        { rooted = false; queue = Queue.empty; act = CrateMap.empty; clock = 0 };
      trail = [];
    }

  let frame st p (m : Cargo_parse.ver) ~root ~all feats default =
    let on, deps = requirements m ~all feats default in
    let ds =
      List.stable_sort
        (fun (a, _) (b, _) -> compare a b)
        (List.map
           (fun ((d, _) as e) -> (D.candidates d, e))
           (enabled ~root m deps))
    in
    let time = st.clock + 1 in
    let queue, _ =
      List.fold_left
        (fun (q, idx) (count, (dep, feats)) ->
          (Queue.add { count; time; idx; parent = p; dep; feats } q, idx + 1))
        (st.queue, 0) ds
    in
    let prev =
      Option.value (CrateMap.find_opt p st.act) ~default:StringSet.empty
    in
    {
      st with
      queue;
      clock = time;
      act = CrateMap.add p (StringSet.union on prev) st.act;
    }

  (* flag_activated (context.rs): a crate already activated with every
     feature asked of it, default included where it has one, adds no
     frame *)
  let activate st (it : item) c =
    match D.meta c with
    | None -> st
    | Some m -> (
        let default = it.dep.Cargo_parse.d_default in
        match CrateMap.find_opt c st.act with
        | Some prev
          when StringSet.subset it.feats prev
               && ((not default)
                  || StringSet.mem Cargo_parse.default_feature prev
                  || not m.Cargo_parse.v_default_declared) ->
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
                    frame st D.root m ~root:true ~all:true StringSet.empty true
                | Cargo_query.Named { feats; default } ->
                    frame st D.root m ~root:true ~all:false
                      (StringSet.of_list feats) default
              in
              advance ~assigned st)
    else
      match Queue.min_elt_opt st.queue with
      | None -> (st, None)
      | Some it -> (
          let rest = { st with queue = Queue.remove it st.queue } in
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

  (* [`Pubgrub] leaves both hooks to PubGrub, which is still sound and
     complete, only no longer cargo's answer where the two orders part *)
  let hooks : (unit, D.name, D.selection, D.version) Pac_common.Order.driver =
   fun order () ->
    match order with
    | `Tool ->
        let t = create () in
        Pac_common.Order.make ~next:(next t) ~choose:D.choose ()
    | `Pubgrub -> Pac_common.Order.make ()
    | `Random seed -> Pac_common.Order.random seed
end
