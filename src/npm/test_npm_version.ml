(* Precedence vectors are the ladder from semver.org 2.0.0 section 11;
   the range vectors are the worked examples in npm's semver README, plus
   the prerelease admission rule, which is the one place the OCaml mirror
   has to agree with Npm.csAdmits in the calculus. *)

let fail = ref 0

let check a b exp =
  let got = Npm_version.compare a b in
  let norm x = if x < 0 then -1 else if x > 0 then 1 else 0 in
  if norm got <> exp then (
    Printf.printf "FAIL compare %S %S = %d, want %d\n" a b (norm got) exp;
    incr fail)

let rng s exp =
  let got = Npm_version.string_of_range (Npm_version.parse_range s) in
  if got <> exp then (
    Printf.printf "FAIL parse_range %S = %S, want %S\n" s got exp;
    incr fail)

let sat s v exp =
  let got = Npm_version.holds v (Npm_version.parse_range s) in
  if got <> exp then (
    Printf.printf "FAIL %S matches %S = %b, want %b\n" s v got exp;
    incr fail)

let () =
  (* the canonical precedence ladder *)
  check "1.0.0" "2.0.0" (-1);
  check "2.0.0" "2.1.0" (-1);
  check "2.1.0" "2.1.1" (-1);
  check "1.0.0-alpha" "1.0.0" (-1);
  check "1.0.0-alpha" "1.0.0-alpha.1" (-1);
  check "1.0.0-alpha.1" "1.0.0-alpha.beta" (-1);
  check "1.0.0-alpha.beta" "1.0.0-beta" (-1);
  check "1.0.0-beta" "1.0.0-beta.2" (-1);
  check "1.0.0-beta.2" "1.0.0-beta.11" (-1);
  check "1.0.0-beta.11" "1.0.0-rc.1" (-1);
  check "1.0.0-rc.1" "1.0.0" (-1);
  (* build metadata is ignored, leading zeros carry no value *)
  check "1.0.0+build.1" "1.0.0" 0;
  check "1.0.0+a" "1.0.0+b" 0;
  check "1.01.0" "1.1.0" 0;
  check "1.0.0-1" "1.0.0-01" 0;
  (* numeric identifiers sort below alphanumeric ones *)
  check "1.0.0-1" "1.0.0-alpha" (-1);
  check "1.0.0-2" "1.0.0-10" (-1);
  check "1.0.0-alpha" "1.0.0-alpha.0" (-1);
  (* missing components read as zero *)
  check "1" "1.0.0" 0;
  check "1.2" "1.2.0" 0;

  (* prerelease detection and release cores *)
  if Npm_version.is_prerelease "1.2.3" then (
    Printf.printf "FAIL is_prerelease 1.2.3\n";
    incr fail);
  if not (Npm_version.is_prerelease "1.2.3-rc.1") then (
    Printf.printf "FAIL is_prerelease 1.2.3-rc.1\n";
    incr fail);
  if not (Npm_version.same_core "1.2.3-rc.1" "1.2.3") then (
    Printf.printf "FAIL same_core 1.2.3-rc.1 1.2.3\n";
    incr fail);
  if Npm_version.same_core "1.2.3-rc.1" "1.2.4" then (
    Printf.printf "FAIL same_core 1.2.3-rc.1 1.2.4\n";
    incr fail);

  (* a "v" prefix on the version part is allowed after an operator too *)
  rng "^v1.2.3" ">=1.2.3 <2.0.0";
  rng "~v1.2.3" ">=1.2.3 <1.3.0";
  rng ">=v1.2.3" ">=1.2.3";
  rng "=v1.2.3" "=1.2.3";

  (* bare x/X are semver wildcards, not dist-tags *)
  rng "x" "*";
  rng "X" "*";

  (* caret, including the 0.x and 0.0.x rules *)
  rng "^1.2.3" ">=1.2.3 <2.0.0";
  rng "^0.2.3" ">=0.2.3 <0.3.0";
  rng "^0.0.3" ">=0.0.3 <0.0.4";
  rng "^1.2.x" ">=1.2.0 <2.0.0";
  rng "^0.0.x" ">=0.0.0 <0.1.0";
  rng "^0.0" ">=0.0.0 <0.1.0";
  rng "^1.x" ">=1.0.0 <2.0.0";
  rng "^0.x" ">=0.0.0 <1.0.0";
  (* tilde *)
  rng "~1.2.3" ">=1.2.3 <1.3.0";
  rng "~1.2" ">=1.2.0 <1.3.0";
  rng "~1" ">=1.0.0 <2.0.0";
  rng "~0.2.3" ">=0.2.3 <0.3.0";
  rng "~1.2.x" ">=1.2.0 <1.3.0";
  (* bare, exact and wildcards *)
  rng "1.2.3" "=1.2.3";
  rng "=1.2.3" "=1.2.3";
  rng "1.2" ">=1.2.0 <1.3.0";
  rng "1" ">=1.0.0 <2.0.0";
  rng "1.2.x" ">=1.2.0 <1.3.0";
  rng "1.x" ">=1.0.0 <2.0.0";
  rng "*" "*";
  rng "x" "*";
  rng "" "*";
  (* inequalities, with partial operands widening *)
  rng ">=1.2.3" ">=1.2.3";
  rng ">1.2.3" ">1.2.3";
  rng ">1.2" ">=1.3.0";
  rng ">1" ">=2.0.0";
  rng "<=1.2.3" "<=1.2.3";
  rng "<=1.2" "<1.3.0";
  rng "<1.2.3" "<1.2.3";
  rng ">= 1.2.3" ">=1.2.3";
  (* whitespace is conjunction, || is disjunction *)
  rng ">=1.2.3 <2.0.0" ">=1.2.3 <2.0.0";
  rng "^1 || ^2" ">=1.0.0 <2.0.0 || >=2.0.0 <3.0.0";
  rng "1.2.3 || >=4" "=1.2.3 || >=4.0.0";
  (* hyphen ranges, both ends widening *)
  rng "1.2.3 - 2.3.4" ">=1.2.3 <=2.3.4";
  rng "1.2 - 2.3.4" ">=1.2.0 <=2.3.4";
  rng "1.2.3 - 2.3" ">=1.2.3 <2.4.0";
  rng "1.2.3 - 2" ">=1.2.3 <3.0.0";

  (* satisfaction, and the prerelease rule: a prerelease is admitted only
     by a comparator set that names one at the same release core *)
  sat "^1.2.3" "1.2.3" true;
  sat "^1.2.3" "1.9.9" true;
  sat "^1.2.3" "2.0.0" false;
  sat "^1.2.3" "1.2.2" false;
  sat "^0.2.3" "0.3.0" false;
  sat "^0.0.3" "0.0.4" false;
  sat "1.2.3 - 2.3.4" "2.3.4" true;
  sat "1.2.3 - 2.3.4" "2.3.5" false;
  sat "^1 || ^3" "2.5.0" false;
  sat "^1 || ^3" "3.1.0" true;
  sat "*" "1.0.0" true;
  (* prereleases are excluded unless named *)
  sat "^1.2.3" "1.3.0-rc.1" false;
  sat ">=1.2.3-rc.1" "1.2.3-rc.2" true;
  sat ">=1.2.3-rc.1" "1.3.0-rc.1" false;
  sat ">=1.2.3-rc.1 <2.0.0" "1.2.3" true;
  sat "1.2.3-rc.1" "1.2.3-rc.1" true;
  sat "*" "1.0.0-rc.1" false;
  (* the rule is per comparator set, not per range *)
  sat "^1.2.3 || >=2.0.0-rc.1" "2.0.0-rc.1" true;
  sat "^1.2.3 || >=2.0.0-rc.1" "2.1.0-rc.1" false;

  if !fail = 0 then print_endline "ok"
  else (
    Printf.printf "%d failures\n" !fail;
    exit 1)
