let fail = ref 0

let expect what got want =
  if got <> want then (
    Printf.eprintf "FAIL: %s\n" what;
    incr fail)

let () =
  (* each keeps its own range syntax: bare is caret to cargo and equality
     to npm, a comma is cargo's conjunction and || npm's disjunction *)
  let cargo r v = Cargo_version.holds v (Cargo_version.parse_req r) in
  let npm r v = Npm_version.holds v (Npm_version.parse_range r) in
  expect "cargo 1.2.3 admits 1.9.0" (cargo "1.2.3" "1.9.0") true;
  expect "npm 1.2.3 refuses 1.9.0" (npm "1.2.3" "1.9.0") false;
  expect "cargo >=1.2, <1.5 refuses 1.5.0" (cargo ">=1.2, <1.5" "1.5.0") false;
  expect "npm ^1 || ^3 admits 3.1.0" (npm "^1 || ^3" "3.1.0") true;
  expect "npm 1.2.3 - 2.3.4 admits 2.3.4" (npm "1.2.3 - 2.3.4" "2.3.4") true;

  (* the prerelease-admission rule is the same for both *)
  List.iter
    (fun (r, v, want) ->
      expect (Printf.sprintf "cargo %S admits %S" r v) (cargo r v) want;
      expect (Printf.sprintf "npm %S admits %S" r v) (npm r v) want)
    [
      ("^1.0.0", "1.0.1-alpha", false);
      ("*", "1.0.0-alpha", false);
      (">=1.2.3-rc.1", "1.2.3-rc.2", true);
      (">=1.2.3-rc.1", "1.3.0-rc.1", false);
      ("^1.0.0-alpha", "1.0.0-alpha.1", true);
      ("^1.0.0-alpha", "1.0.1-alpha", false);
    ];

  if !fail > 0 then exit 1;
  print_endline "ranges: all tests pass"
