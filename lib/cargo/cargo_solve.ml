open Encoding
module P = Cargo_parse
module Q = Cargo_query
module L = Lookups

type result = {
  crates : (string * string * string list) list;
  parents : (string * string * string * string * string) list;
  nodes : int;
  lookups : int;
}

type run = {
  answer : (result, Pac_common.Report.explanation) Stdlib.result;
  core : unit -> unit;
  n_names : int;
  n_vers : int;
  dropped : int;
  t_parse : float;
}

let decode st (sol : (Cg.NPlus.t * PVersion.t) list) : result =
  let sol =
    List.map
      (fun ((tn, { PVersion.v; _ }) : Cg.NPlus.t * PVersion.t) -> (tn, v))
      sol
  in
  let s = T.PkgSet.ofList sol in
  let crates = Cg.PkgSet.elements (Cg.cargoResolution s) in
  (* the placeholder default the parser gives a crate declaring none
     keeps a depender's default-features request satisfiable; cargo
     records no such feature (dep_cache.rs, handle_default requires
     the key), so Resolve::features has it only where the manifest
     does, and the reported set follows *)
  let feats =
    List.map
      (fun (((n, v), fs) : Cg.Featured.t) ->
        let fs = Cg.FSet.elements fs in
        match L.meta st n v with
        | Some m when not m.P.v_default_declared ->
            ((n, v), List.filter (fun f -> f <> P.default_feature) fs)
        | _ -> ((n, v), fs))
      (Cg.FeaturedSet.elements (Cg.decodeFS s))
  in
  (* decodeParents is the one decoder that reads the instance, and a
     lazy run has no global relation to hand it; the fibres of the
     crates it decodes are all it looks at, since it reads Slots and
     FDefs only at the owner a slot node names and keeps the node
     only when that owner is decoded *)
  let fibres = List.map (L.slots_and_fdefs st) (L.root st :: crates) in
  let slots = Cg.SlotRel.unions (List.map fst fibres) in
  let fdefs = Cg.FDefRel.unions (List.map snd fibres) in
  let parents =
    List.map
      (fun ((((n, v), k), u) : Cg.ParentElt.t) ->
        match L.site_data st (n, v) k with
        | Some sd -> (n, v, Cg.kAlias k, Cg.sTarget sd, u)
        | None -> (n, v, Cg.kAlias k, Cg.kAlias k, u))
      (Cg.ParentRel.elements
         (Cg.decodeParents
            { (L.empty_inst st) with inst_fdefs = fdefs; inst_slots = slots }
            s))
  in
  {
    crates =
      List.map
        (fun ((n, v) as c) ->
          (n, v, Option.value (List.assoc_opt c feats) ~default:[]))
        (List.sort compare crates);
    parents;
    nodes = List.length sol;
    lookups = L.dependency_lookups st;
  }

let solve ?(debug = false) ?(order = `Tool) ~index ~features ~rustv
    (root : Q.root) : run =
  Pubgrub.set_debug debug;
  let ar = Archive.empty index in
  (* cargo's "no matching package named" is its own error, not a failed
     resolve, where the dependency is the root's: nothing else could have
     been chosen instead.  A crate further down is a version that fails. *)
  List.iter
    (fun (d : P.dep) ->
      if not (Archive.listed ar d.P.d_target) then
        Q.refuse "no matching package named `%s` found" d.P.d_target)
    root.Q.ver.P.v_deps;
  Archive.install_root ar root.Q.ver;
  let st = L.create ar root ~features ~rustv in
  let query =
    [
      ( Cg.NPlus.CRoot,
        PG.Ranges.of_list [ L.tag st Cg.NPlus.CRoot Cg.VPlus.WUnit ] );
    ]
  in
  let module O = Order.Make (Pick.Driver (struct
    let pk = Pick.create st
  end))
  in
  let h = O.hooks order () in
  let outcome =
    PG.solve ?next:h.Pac_common.Order.next ?choose:h.Pac_common.Order.choose
      ~vers:(L.pg_versions st) ~deps:(L.pg_dependencies st) query
  in
  h.Pac_common.Order.finish ();
  let answer =
    match outcome with
    | Error inc -> Error (fun ppf -> PG.explain_incompatibility ppf inc)
    | Ok sol -> Ok (decode st sol)
  in
  let core () =
    Pac_common.Core.print ~pp_name:PName.pp ~pp_version:PVersion.pp
      (Pac_common.Core.walk ~versions:(L.pg_versions st)
         ~dependees:(fun (tn, { PVersion.v; _ }) ->
           List.map
             (fun ((m, vs) : T.Dependees.t) ->
               (m, List.map (L.tag st m) (T.VSet.elements vs)))
             (L.dependees st (tn, v)))
         [ Cg.NPlus.CRoot ])
  in
  let stats = Archive.stats ar in
  {
    answer;
    core;
    n_names = stats.Archive.names;
    n_vers = stats.Archive.versions;
    dropped = stats.Archive.dropped;
    t_parse = stats.Archive.parse;
  }

let reaches_registry_root (root : Q.root) (r : result) =
  let rc = Q.crate root in
  (not root.Q.self_patch)
  && List.exists (fun (n, u, _, t, w) -> (t, w) = rc && (n, u) <> rc) r.parents
