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
  cached : int;
  t_parse : float;
}

module Make () = struct
  module Encoding = Encoding.Make ()
  open Encoding
  module Lookups = Lookups.Make (Encoding)
  module Pick = Pick.Make (Encoding) (Lookups)

  let decode st (sol : (Cargo.Reduction.Name.t * PVersion.t) list) : result =
    let sol =
      List.map
        (fun ((tn, { PVersion.v; _ }) : Cargo.Reduction.Name.t * PVersion.t) ->
          (tn, v))
        sol
    in
    let s = Reduced.PackageSet.ofList sol in
    let crates =
      Cargo.PackageSet.elements (Cargo.Reduction.cargoResolution s)
    in
    (* the placeholder default the parser gives a crate declaring none
       keeps a depender's default-features request satisfiable; cargo
       records no such feature (dep_cache.rs, handle_default requires
       the key), so Resolve::features has it only where the manifest
       does, and the reported set follows *)
    let feats =
      List.map
        (fun (((n, v), fs) : Cargo.Featured.t) ->
          let fs = Cargo.FSet.elements fs in
          match Lookups.meta st n v with
          | Some m when not m.Cargo_parse.v_default_declared ->
              ( (n, v),
                List.filter (fun f -> f <> Cargo_parse.default_feature) fs )
          | _ -> ((n, v), fs))
        (Cargo.FeaturedSet.elements (Cargo.Reduction.features s))
    in
    (* parents is the one decoder that reads the instance, and a
       lazy run has no global relation to hand it; the fibres of the
       crates it decodes are all it looks at, since it reads Slots and
       FDefs only at the owner a slot node names and keeps the node
       only when that owner is decoded *)
    let fibres =
      List.map (Lookups.slots_and_fdefs st) (Lookups.root st :: crates)
    in
    let slots = Cargo.SlotRel.unions (List.map fst fibres) in
    let fdefs = Cargo.FeatureDefinitionRel.unions (List.map snd fibres) in
    let parents =
      List.map
        (fun ((((n, v), k), u) : Cargo.ParentElt.t) ->
          match Lookups.site_data st (n, v) k with
          | Some sd -> (n, v, Cargo.siteAlias k, Cargo.sName sd, u)
          | None -> (n, v, Cargo.siteAlias k, Cargo.siteAlias k, u))
        (Cargo.ParentRel.elements
           (Cargo.Reduction.parents
              {
                (Lookups.empty_inst st) with
                inst_fdefs = fdefs;
                inst_slots = slots;
              }
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
      lookups = Lookups.dependency_lookups st;
    }

  let check_answer st (sol : (Cargo.Reduction.Name.t * PVersion.t) list) =
    let s =
      Reduced.PackageSet.ofList
        (List.map (fun (tn, { PVersion.v; _ }) -> (tn, v)) sol)
    in
    let versions tn =
      Reduced.VSet.ofList
        (List.map (fun { PVersion.v; _ } -> v) (Lookups.pg_versions st tn))
    in
    let dependees p = Reduced.DependeeSet.ofList (Lookups.dependees st p) in
    let root =
      Reduced.rootQuery
        (Cargo.Reduction.Name.CRoot, Cargo.Reduction.Version.WUnit)
    in
    match Reduced.check versions dependees root s with
    | None -> ()
    | Some f ->
        Pac_common.Check.fail ~pp_name:PName.pp
          ~pp_version:(fun tn fmt w -> PVersion.pp fmt (Lookups.tag st tn w))
          ~elements:Reduced.VSet.elements f

  let solve ?(debug = false) ?(check = false) ?(order = `Tool) ?cache ~index
      ~features ~rustv (root : Cargo_query.root) : run =
    Pubgrub.set_debug debug;
    let ar = Archive.empty ?cache index in
    (* cargo's "no matching package named" is its own error, not a failed
       resolve, where the dependency is the root's: nothing else could have
       been chosen instead.  A crate further down is a version that fails. *)
    List.iter
      (fun (d : Cargo_parse.dep) ->
        if not (Archive.listed ar d.Cargo_parse.d_name) then
          Cargo_query.refuse "no matching package named `%s` found"
            d.Cargo_parse.d_name)
      root.Cargo_query.ver.Cargo_parse.v_deps;
    Archive.install_root ar root.Cargo_query.ver;
    let st = Lookups.create ar root ~features ~rustv in
    let query =
      [
        ( Cargo.Reduction.Name.CRoot,
          Resolver.Ranges.of_list
            [
              Lookups.tag st Cargo.Reduction.Name.CRoot
                Cargo.Reduction.Version.WUnit;
            ] );
      ]
    in
    let module Order = Order.Make (Pick.Driver (struct
      let pk = Pick.create st
    end))
    in
    let h = Order.hooks order () in
    let outcome =
      Resolver.solve ?next:h.Pac_common.Order.next
        ?choose:h.Pac_common.Order.choose ~vers:(Lookups.pg_versions st)
        ~deps:(Lookups.pg_dependencies st)
        query
    in
    h.Pac_common.Order.finish ();
    let answer =
      match outcome with
      | Error inc -> Error (fun ppf -> Resolver.explain_incompatibility ppf inc)
      | Ok sol ->
          if check then check_answer st sol;
          Ok (decode st sol)
    in
    let core () =
      Pac_common.Core.print ~pp_name:PName.pp ~pp_version:PVersion.pp
        (Pac_common.Core.walk ~versions:(Lookups.pg_versions st)
           ~dependees:(fun (tn, { PVersion.v; _ }) ->
             List.map
               (fun ((m, vs) : Reduced.Dependee.t) ->
                 (m, List.map (Lookups.tag st m) (Reduced.VSet.elements vs)))
               (Lookups.dependees st (tn, v)))
           [ Cargo.Reduction.Name.CRoot ])
    in
    let stats = Archive.stats ar in
    {
      answer;
      core;
      n_names = stats.Archive.names;
      n_vers = stats.Archive.versions;
      dropped = stats.Archive.dropped;
      cached = stats.Archive.cached;
      t_parse = stats.Archive.parse;
    }
end

let reaches_registry_root (root : Cargo_query.root) (r : result) =
  let rc = Cargo_query.crate root in
  (not root.Cargo_query.self_patch)
  && List.exists (fun (n, u, _, t, w) -> (t, w) = rc && (n, u) <> rc) r.parents
