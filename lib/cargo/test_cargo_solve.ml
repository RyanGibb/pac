let dir = "../../test/frontends/cargo.t"

let queries =
  [
    ("a", Cargo_query.All, None);
    ("selfpatch", Cargo_query.All, None);
    ("h", Cargo_query.All, None);
    ("k", Cargo_query.All, None);
    ("k", Cargo_query.Named { feats = []; default = false }, None);
    ("r", Cargo_query.All, None);
    ("rl", Cargo_query.All, None);
    ("ms", Cargo_query.All, Some "1.70");
    ("mu", Cargo_query.All, Some "1.70");
    ("m2", Cargo_query.All, Some "1.70");
    ("m2", Cargo_query.All, None);
    ("app", Cargo_query.All, None);
    ("oa", Cargo_query.All, None);
    ("dv", Cargo_query.All, None);
  ]

let solve (m, features, installed) =
  let root =
    Cargo_query.of_manifest (Printf.sprintf "%s/manifests/%s.toml" dir m)
  in
  let rustv = Cargo_query.toolchain root ~installed in
  let r = Cargo_solve.solve ~index:(dir ^ "/index") ~features ~rustv root in
  match r.Cargo_solve.answer with
  | Error _ -> None
  | Ok a ->
      Some
        ( a.Cargo_solve.crates,
          a.Cargo_solve.feats,
          a.Cargo_solve.parents,
          a.Cargo_solve.nodes,
          a.Cargo_solve.processed,
          r.Cargo_solve.n_names,
          r.Cargo_solve.n_vers )

(* two orders in one process: an answer that depended on what an earlier
   solve left behind would differ between them *)
let () =
  let forward = List.map solve queries in
  let backward = List.rev (List.map solve (List.rev queries)) in
  let fail = ref 0 in
  List.iter2
    (fun (q, f) b ->
      let m, _, _ = q in
      if f <> b then (
        Printf.eprintf "FAIL: %s answers differently after other solves\n" m;
        incr fail);
      if f = None then (
        Printf.eprintf "FAIL: %s is unsatisfiable\n" m;
        incr fail))
    (List.combine queries forward)
    backward;
  if !fail > 0 then exit 1;
  print_endline "cargo_solve: all tests pass"
