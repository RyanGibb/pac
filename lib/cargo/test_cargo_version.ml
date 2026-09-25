let fail = ref 0

let check a b exp =
  let got = Cargo_version.compare a b in
  let sgn x = if x < 0 then -1 else if x > 0 then 1 else 0 in
  if sgn got <> exp then (
    Printf.eprintf "FAIL: compare %S %S = %d, expected sign %d\n" a b got exp;
    incr fail)

let req r v exp =
  let got = Cargo_version.holds v (Cargo_version.parse_req r) in
  if got <> exp then (
    Printf.eprintf "FAIL: %S matches %S = %b, expected %b (bounds %s)\n" r v got
      exp
      (Cargo_version.string_of_req (Cargo_version.parse_req r));
    incr fail)

let () =
  (* the canonical SemVer 2.0.0 pre-release ladder *)
  check "1.0.0-alpha" "1.0.0-alpha.1" (-1);
  check "1.0.0-alpha.1" "1.0.0-alpha.beta" (-1);
  check "1.0.0-alpha.beta" "1.0.0-beta" (-1);
  check "1.0.0-beta" "1.0.0-beta.2" (-1);
  check "1.0.0-beta.2" "1.0.0-beta.11" (-1);
  check "1.0.0-beta.11" "1.0.0-rc.1" (-1);
  check "1.0.0-rc.1" "1.0.0" (-1);
  (* numeric precedence on the core, not lexicographic *)
  check "1.0.0" "2.0.0" (-1);
  check "2.0.0" "2.1.0" (-1);
  check "2.1.0" "2.1.1" (-1);
  check "1.9.0" "1.10.0" (-1);
  check "1.0.2" "1.0.10" (-1);
  check "1.0.0" "1.0.0" 0;
  (* build metadata is ignored *)
  check "1.0.0+build.1" "1.0.0" 0;
  check "1.0.0+build.1" "1.0.0+build.2" 0;
  check "1.0.0-alpha+x" "1.0.0-alpha+y" 0;
  check "1.0.0-alpha+x" "1.0.0" (-1);
  (* numeric identifiers rank below alphanumeric ones *)
  check "1.0.0-1" "1.0.0-alpha" (-1);
  check "1.0.0-1" "1.0.0-2" (-1);
  check "1.0.0-11" "1.0.0-2" 1;
  (* a shorter identifier list ranks below its extension *)
  check "1.0.0-alpha" "1.0.0-alpha.0" (-1);
  (* the semver crate reads a component as a u64, so a timestamp-style
     component stays apart from its neighbour *)
  check "1.0.1234567890" "1.0.1234567891" (-1);
  check "12345678901.0.0" "12345678902.0.0" (-1);
  check "1.0.999999999999999998" "1.0.999999999999999999" (-1);
  check "1.0.9999999999" "1.0.999999999" 1;
  req "=1.0.1234567890" "1.0.1234567891" false;
  req "^1.0.1234567890" "1.0.1234567891" true;

  (* caret is the default, with leftmost-nonzero compatibility *)
  req "^1.2.3" "1.2.3" true;
  req "^1.2.3" "1.9.0" true;
  req "^1.2.3" "1.2.2" false;
  req "^1.2.3" "2.0.0" false;
  req "1.2.3" "1.9.0" true;
  req "1.2" "1.9.0" true;
  req "1" "1.9.0" true;
  req "1" "2.0.0" false;
  (* 0.x: the minor is the granularity class *)
  req "^0.3.1" "0.3.9" true;
  req "^0.3.1" "0.4.0" false;
  req "^0.3.1" "0.3.0" false;
  req "0.3" "0.3.9" true;
  req "0.3" "0.4.0" false;
  (* 0.0.x: the patch is the granularity class *)
  req "^0.0.3" "0.0.3" true;
  req "^0.0.3" "0.0.4" false;
  req "^0.0" "0.0.9" true;
  req "^0.0" "0.1.0" false;
  req "^0" "0.9.0" true;
  req "^0" "1.0.0" false;
  (* tilde pins the minor when it is given *)
  req "~1.2.3" "1.2.9" true;
  req "~1.2.3" "1.3.0" false;
  req "~1.2" "1.2.9" true;
  req "~1.2" "1.3.0" false;
  req "~1" "1.9.9" true;
  req "~1" "2.0.0" false;
  req "=1.2.3" "1.2.3" true;
  req "=1.2.3" "1.2.4" false;
  req "=1.2" "1.2.7" true;
  req "=1.2" "1.3.0" false;
  req ">=1.2.0" "1.2.0" true;
  req ">=1.2.0" "1.1.9" false;
  req ">1.2.0" "1.2.0" false;
  req ">1.2.0" "1.2.1" true;
  req "<1.2.0" "1.1.9" true;
  req "<1.2.0" "1.2.0" false;
  req "<=1.2.0" "1.2.0" true;
  req "<=1.2.0" "1.2.1" false;
  req "*" "0.0.1" true;
  req "*" "99.0.0" true;
  req "1.*" "1.9.9" true;
  req "1.*" "2.0.0" false;
  req "1.2.*" "1.2.9" true;
  req "1.2.*" "1.3.0" false;
  (* comma is conjunction *)
  req ">=1.2, <1.5" "1.4.0" true;
  req ">=1.2, <1.5" "1.5.0" false;
  req ">=1.2, <1.5" "1.1.0" false;
  req ">= 1.2.0, < 1.5.0" "1.3.0" true;

  (* the two tests the ordering cannot express *)
  if Cargo_version.is_prerelease "1.2.3" then (
    Printf.eprintf "FAIL: is_prerelease 1.2.3\n";
    incr fail);
  if not (Cargo_version.is_prerelease "1.2.3-rc.1") then (
    Printf.eprintf "FAIL: is_prerelease 1.2.3-rc.1\n";
    incr fail);
  if not (Cargo_version.same_core "1.2.3-rc.1" "1.2.3") then (
    Printf.eprintf "FAIL: same_core 1.2.3-rc.1 1.2.3\n";
    incr fail);
  if Cargo_version.same_core "1.2.3-rc.1" "1.2.4" then (
    Printf.eprintf "FAIL: same_core 1.2.3-rc.1 1.2.4\n";
    incr fail);

  (* a requirement that names no pre-release admits none, however wide *)
  req "^1.0.0" "1.0.1-alpha" false;
  req "^1.0.0" "1.0.0-alpha" false;
  req "*" "1.0.0-alpha" false;
  req ">=1.0.0" "2.0.0-alpha" false;
  req ">=0.0.0, <9.9.9" "1.2.3-alpha" false;
  (* one that names a pre-release admits others at the same core *)
  req "^1.0.0-alpha" "1.0.0-alpha.1" true;
  req "^1.0.0-alpha" "1.0.0-alpha" true;
  req "^1.0.0-alpha" "1.0.0" true;
  req "^1.0.0-alpha" "1.5.0" true;
  req "^1.0.0-alpha" "0.9.9" false;
  req "=1.2.3-rc.1" "1.2.3-rc.1" true;
  req ">=1.2.3-rc.1" "1.2.3-rc.2" true;
  (* and only at that core: the admission is scoped to the comparator
     set, not to the range's whole interval *)
  req "^1.0.0-alpha" "1.0.1-alpha" false;
  req ">=1.0.0-alpha, <2.0.0" "1.9.0-beta" false;
  req ">=1.0.0-alpha, <2.0.0" "2.0.0-beta" false;
  (* either comparator of the set may be the one that names it *)
  req ">=1.0.0, <2.0.0-rc.1" "2.0.0-rc.0" true;
  req ">=1.0.0, <2.0.0-rc.1" "2.0.0-rc.1" false;

  (* the root manifest's requirements, each verdict cargo 1.97's own *)
  List.iter
    (fun (r, exp) ->
      if Cargo_query.req_ok r <> exp then (
        Printf.eprintf "FAIL: req_ok %S, expected %b\n" r exp;
        incr fail))
    [ ("abc", false); ("1.x.y.z;", false); ("", false); ("*", true);
      ("x", true); ("X", true); ("1", true); ("1.2", true); ("1.2.3", true);
      ("^1.2.3", true); ("~1.2", true); ("~>1.2", false); ("=1.2.3", true);
      ("==1.2.3", false); (">=1.2, <2", true); (">= 1.2 , < 2", true);
      (">=1.2 <2", false); ("1.*", true); ("1.x", true); ("1.2.*", true);
      ("1.*.3", false); ("^1.*", true); (">=1.*", true); ("=1.*", true);
      ("~1.*", true); ("*, 1", false); ("1, *", false); ("01.0", false);
      ("1.02", false); ("1.0.0-alpha.1", true); ("1.0.0-", false);
      ("1.0.0-01", false); ("1.0.0-a..b", false); ("1.0-alpha", false);
      ("1.0.0+build", true); ("1.0.0-a+b", true); ("1.2.3.4", false);
      (" 1.2", true); ("1.2.3 - 2", false); ("x.1", false); ("^*", false);
      ("1.2.3,", false); (",1.2.3", false); ("1,,2", false);
      ("1.2.3-alpha,<2", true); (">1", true); ("1a", false); ("1.2a", false);
      ("-1", false); ("1.0.0-a_b", false); ("1.0.0-a-b", true) ];

  (* the string-scanning comparison agrees with parsing, odd spellings
     included *)
  let corpus =
    [ ""; "0"; "1"; "1.0"; "1.0.0"; "01.2.3"; "1.02.3"; "1..2"; "1.2."; "1.";
      "1.2.3.4"; "1a.2b.3c"; "a.b.c"; "0000000001.0.0"; "1234567890.0.0";
      "123456789.0.0"; "12345678901.0.0"; "999999999.0.0";
      "999999999999999999.0.0"; "1000000000000000000.0.0"; "1.0.1234567891";
      "1.0.00000000001234567890"; "1.0.0+b";
      "1.0.0+b-1"; "1.0.0+"; "1.0.0-alpha"; "1.0.0-"; "1.0.0-+x"; "1.0.0-0";
      "2.0.0-rc.1+x"; "0.14.7"; "0.14.10"; "0.0.3"; "10.0.0"; "9.99.999";
      "1-2.3.4"; "1.2-3.4"; "1.2.3-4.5"; "1+2.3"; "1.0.0-alpha.1";
      "0.14.7-pre"; "0.14.7+x-y" ]
  in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          let sgn x = if x < 0 then -1 else if x > 0 then 1 else 0 in
          let got = sgn (Cargo_version.compare a b)
          and want = sgn (Cargo_version.compare_parsed a b) in
          if got <> want then (
            Printf.eprintf "FAIL: compare %S %S = %d, parsed %d\n" a b got
              want;
            incr fail))
        corpus)
    corpus;

  if !fail > 0 then exit 1;
  print_endline "cargo_version: all tests pass"
