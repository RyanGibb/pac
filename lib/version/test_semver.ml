(* Cargo and npm share the semver core: they agree wherever the semver
   crate and node-semver do, and part only where npm reads loosely and
   where their range syntaxes differ. *)

let fail = ref 0
let sgn x = if x < 0 then -1 else if x > 0 then 1 else 0

let expect what got want =
  if got <> want then (
    Printf.eprintf "FAIL: %s\n" what;
    incr fail)

let () =
  (* versions both specs read the same way: the section 11 ladder, build
     metadata, numeric identifiers, components past 32 bits *)
  let corpus =
    [ "0.0.0"; "0.0.1"; "0.1.0"; "1.0.0-alpha"; "1.0.0-alpha.1";
      "1.0.0-alpha.beta"; "1.0.0-beta"; "1.0.0-beta.2"; "1.0.0-beta.11";
      "1.0.0-rc.1"; "1.0.0"; "1.0.0+build.1"; "1.0.0-alpha+x"; "1.0.0-1";
      "1.0.0-2"; "1.0.0-11"; "1.0.0-alpha.0"; "1.0.0-x-y"; "1.9.0"; "1.10.0";
      "2.0.0"; "2.0.0-rc.1+x"; "1.0.1234567890"; "12345678901.0.0" ]
  in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          let c = sgn (Cargo_version.compare a b)
          and n = sgn (Npm_version.compare a b) in
          expect (Printf.sprintf "cargo %S %S = %d, npm %d" a b c n) c n)
        corpus)
    corpus;
  List.iter
    (fun v ->
      expect ("is_prerelease " ^ v)
        (Cargo_version.is_prerelease v)
        (Npm_version.is_prerelease v))
    corpus;

  (* npm reads loosely, cargo strictly: without its hyphen a prerelease is
     npm's alone *)
  expect "cargo 2.0.14rc1 = 2.0.14"
    (sgn (Cargo_version.compare "2.0.14rc1" "2.0.14"))
    0;
  expect "npm 2.0.14rc1 < 2.0.14"
    (sgn (Npm_version.compare "2.0.14rc1" "2.0.14"))
    (-1);
  expect "cargo is_prerelease 2.0.14rc1"
    (Cargo_version.is_prerelease "2.0.14rc1")
    false;
  expect "npm is_prerelease 2.0.14rc1"
    (Npm_version.is_prerelease "2.0.14rc1")
    true;

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
    [ ("^1.0.0", "1.0.1-alpha", false); ("*", "1.0.0-alpha", false);
      (">=1.2.3-rc.1", "1.2.3-rc.2", true);
      (">=1.2.3-rc.1", "1.3.0-rc.1", false);
      ("^1.0.0-alpha", "1.0.0-alpha.1", true);
      ("^1.0.0-alpha", "1.0.1-alpha", false) ];

  if !fail > 0 then exit 1;
  print_endline "semver: all tests pass"
