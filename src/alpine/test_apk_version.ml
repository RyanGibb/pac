(* Vectors are the ones confirmed against apk-tools master's own
   test/unit/version.data plus the worked examples in apk-package(5) and
   apk-world(5). *)

let fail = ref 0

let check a b exp =
  let got = Apk_version.compare a b in
  let norm x = if x < 0 then -1 else if x > 0 then 1 else 0 in
  if norm got <> exp then (
    Printf.printf "FAIL compare %S %S = %d, want %d\n" a b (norm got) exp;
    incr fail)

let valid v exp =
  if Apk_version.validate v <> exp then (
    Printf.printf "FAIL validate %S = %b, want %b\n" v (not exp) exp;
    incr fail)

let fuzzy v c exp =
  if Apk_version.prefix_match v c <> exp then (
    Printf.printf "FAIL %S ~ %S = %b, want %b\n" v c (not exp) exp;
    incr fail)

let op v o c exp =
  match Apk_version.op_of_string o with
  | None ->
      Printf.printf "FAIL unknown operator %S\n" o;
      incr fail
  | Some o' ->
      if Apk_version.matches v o' c <> exp then (
        Printf.printf "FAIL %S %s %S = %b, want %b\n" v o c (not exp) exp;
        incr fail)

let () =
  (* numeric components *)
  check "1.0" "1.0" 0;
  check "1.0" "1.1" (-1);
  check "1.10" "1.9" 1;
  check "1.0.0" "1.0" 1;
  check "006" "1.0.0" 1;
  check "02.08.01b" "4.77" (-1);
  check "01.0" "1.0" 0;

  (* leading zeros switch later components to a string sort *)
  check "8.2.0" "8.2.001" (-1);
  check "8.2.0015" "8.2.002" (-1);
  check "1.0.0" "1.00.0" (-1);
  check "1.0.1" "1.0.01" 1;
  check "1.0.00" "1.0.0" 1;

  (* letter suffix *)
  check "1.0" "1.0a" (-1);
  check "1.0a" "1.0b" (-1);
  check "1.0b" "1.0" 1;

  (* suffix classes: alpha < beta < pre < rc < none < cvs < svn < git <
     hg < p *)
  check "1.0_alpha" "1.0_beta" (-1);
  check "1.0_beta" "1.0_pre" (-1);
  check "1.0_pre" "1.0_rc" (-1);
  check "1.0_rc" "1.0" (-1);
  check "1.0" "1.0_cvs" (-1);
  check "1.0_cvs" "1.0_svn" (-1);
  check "1.0_svn" "1.0_git" (-1);
  check "1.0_git" "1.0_hg" (-1);
  check "1.0_hg" "1.0_p" (-1);
  check "1.0_alpha" "1.0_p" (-1);
  check "6.0_pre1" "6.0" (-1);
  check "6.0_p1" "6.0" 1;

  (* numeric suffix parts *)
  check "1.0_pre1" "1.0_pre2" (-1);
  check "1.0_pre" "1.0_pre1" (-1);
  check "1.0_p10" "1.0_p9" 1;
  check "1.0_alpha2" "1.0_beta1" (-1);

  (* commit hash, then revision *)
  check "1.0~1234" "1.0~2345" (-1);
  check "1.0~abc" "1.0~abd" (-1);
  check "1.0" "1.0~abc" (-1);
  check "1.0~1234-r1" "1.0~1234-r0" 1;
  check "1.0~1234-r1" "1.0~2345-r0" (-1);
  check "1.0" "1.0-r1" (-1);
  check "1.0" "1.0-r0" (-1);
  check "2.11-r1" "2.11" 1;
  check "1.0-r01" "1.0-r2" (-1);
  check "1.0-r2" "1.0-r10" (-1);

  (* a version that goes invalid keeps going, so it sorts greater *)
  check "1.0" "1.0bc" (-1);

  (* validation *)
  valid "1.0" true;
  valid "24.08-r0" true;
  valid "1.0a" true;
  valid "1.0_alpha3" true;
  valid "1.0_git20240101_pre1" true;
  valid "1.0~deadbeef" true;
  valid "1.0~deadbeef-r2" true;
  valid "" false;
  valid "1.0bc" false;
  valid "0.1a1" false;
  valid "1.0_post1" false;
  valid "1.0~ABC" false;
  valid "1.0~" false;
  valid "0.1-r" false;
  valid "0.1-r2.1" false;
  valid "0.1-r2-r3" false;
  valid "0.1-r2_pre1" false;

  (* ~ is a token-wise prefix of the constraint, not a string prefix, and
     only the constraint side may run out *)
  fuzzy "1.6" "1.6" true;
  fuzzy "1.6.0" "1.6" true;
  fuzzy "1.6.5" "1.6" true;
  fuzzy "1.6.0_pre1" "1.6" true;
  fuzzy "1.6.9_p1" "1.6" true;
  fuzzy "1.6-r3" "1.6" true;
  fuzzy "1.6a" "1.6" true;
  fuzzy "3.61" "3.6" false;
  fuzzy "3.8" "3.8.1" false;
  fuzzy "3.6.0" "3.8" false;
  fuzzy "3.8.0.1" "3.8.1" false;
  fuzzy "3.12.8-r1" "3.12" true;

  (* ~ is not a range: it matches versions below the constraint too *)
  fuzzy "1.0_pre1" "1.0" true;
  check "1.0_pre1" "1.0" (-1);

  (* operators, including the bit-OR spellings *)
  op "1.0" "=" "1.0" true;
  op "1.0" "=" "1.1" false;
  op "1.2" ">" "1.1" true;
  op "1.1" ">=" "1.1" true;
  op "1.0" "<" "1.1" true;
  op "1.1" "<=" "1.1" true;
  op "1.1" "=<" "1.1" true;
  op "3.12.8" "~" "3.12" true;
  op "3.12.8" "=~" "3.12" true;
  op "3.7" ">~" "3.6" true;
  op "3.5" ">~" "3.6" false;
  op "3.6.0" ">~" "3.6" true;
  op "3.5" "<~" "3.6" true;
  op "3.6.0" "<~" "3.6" true;
  op "3.6.0" "<=" "3.6" false;
  op "3.7" "<~" "3.6" false;
  (* >< pins the C: identity digest, which a version cannot witness *)
  op "1.0" "><" "Q1Io65EOU4TZIqoCav8tqwhqq2RPM=" false;

  if !fail > 0 then exit 1;
  print_endline "apk_version: all tests pass"
