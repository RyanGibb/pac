open Encoding
module P = Cargo_parse
module Q = Cargo_query
module L = Lookups

type result = {
  (* each crate version with the features the solution turns on *)
  crates : (string * string * string list) list;
  (* the parent relation, keyed in the theory by manifest site: one
     crate may depend on a single crate name twice -- under two aliases
     through a rename, or under one alias from two sites -- and the
     copies may land on different granularity classes, so the edge has
     to record which declaration received which version.  ParentElt
     carries only the target's version, since the site already
     determines the slot it came through; the target name is read back
     off that slot here, and the alias is what is reported, because a
     consumer comparing against cargo's (depender, dependee) edges has
     no other way to name the crate the version belongs to and no notion
     of a site at all.
     (owner, owner version, alias, target name, target version) *)
  parents : (string * string * string * string * string) list;
  nodes : int;
  processed : int;
}

(* what one solve read of the index, reported whether or not it found an
   answer *)
type run = {
  answer : (result, Pac_common.Report.explanation) Stdlib.result;
  n_names : int;
  n_vers : int;
  t_parse : float;
}

let decode st (sol : (Cg.NPlus.t * PVersion.t) list) : result =
  let sol =
    List.map
      (fun ((tn, { PVersion.v; _ }) : Cg.NPlus.t * PVersion.t) -> (tn, v))
      sol
  in
  let s = T.PkgSet.ofList sol in
  let crates = Cg.PkgSet.elements (Cg.decodeS s) in
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
  let fibres = List.map (L.fibres_of st) (st.L.rc :: crates) in
  let slots = Cg.SlotRel.unions (List.map (fun r -> r.L.r_slots) fibres) in
  let fdefs = Cg.FDefRel.unions (List.map (fun r -> r.L.r_fdefs) fibres) in
  let parents =
    List.map
      (fun ((((n, v), k), u) : Cg.ParentElt.t) ->
        match L.site_data st (n, v) k with
        | Some sd -> (n, v, Cg.kAlias k, Cg.sTarget sd, u)
        | None -> (n, v, Cg.kAlias k, Cg.kAlias k, u))
      (Cg.ParentRel.elements (Cg.decodeParents fdefs slots st.L.rc s))
  in
  {
    crates =
      List.map
        (fun ((n, v) as c) ->
          (n, v, Option.value (List.assoc_opt c feats) ~default:[]))
        (List.sort compare crates);
    parents;
    nodes = List.length sol;
    (* the crate versions whose manifests became encoded fibres *)
    processed = Hashtbl.length st.L.fibres;
  }

let solve ?(debug = false) ?(order = `Tool) ~index ~features ~rustv
    (root : Q.root) : run =
  Pubgrub.set_debug debug;
  let ar = Archive.empty index in
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
  {
    answer;
    n_names = ar.Archive.n_names;
    n_vers = ar.Archive.n_vers;
    t_parse = ar.Archive.t_parse;
  }

(* cargo tells packages apart by source as well, so without the
   self-patch the registry's crate at the root's name and version is a
   second package, which one node per (name, version) cannot be *)
let reaches_registry_root (root : Q.root) (r : result) =
  let rc = Q.crate root in
  (not root.Q.self_patch)
  && List.exists (fun (n, u, _, t, w) -> (t, w) = rc && (n, u) <> rc) r.parents
