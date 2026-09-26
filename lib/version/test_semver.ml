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
    [
      "0.0.0";
      "0.0.1";
      "0.1.0";
      "1.0.0-alpha";
      "1.0.0-alpha.1";
      "1.0.0-alpha.beta";
      "1.0.0-beta";
      "1.0.0-beta.2";
      "1.0.0-beta.11";
      "1.0.0-rc.1";
      "1.0.0";
      "1.0.0+build.1";
      "1.0.0-alpha+x";
      "1.0.0-1";
      "1.0.0-2";
      "1.0.0-11";
      "1.0.0-alpha.0";
      "1.0.0-x-y";
      "1.9.0";
      "1.10.0";
      "2.0.0";
      "2.0.0-rc.1+x";
      "1.0.1234567890";
      "12345678901.0.0";
    ]
  in
  (* the two agree but where build metadata alone tells two apart, which
     only cargo's order ranks *)
  let core v = fst (Version.Semver.strip_build v) in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          let c = sgn (Version.Semver.Strict.compare a b)
          and n = sgn (Version.Semver.Loose.compare a b) in
          if core a <> core b || a = b then
            expect (Printf.sprintf "strict %S %S = %d, loose %d" a b c n) c n
          else expect (Printf.sprintf "loose %S %S = %d" a b n) n 0)
        corpus)
    corpus;
  expect "strict 1.0.0 < 1.0.0+build.1"
    (sgn (Version.Semver.Strict.compare "1.0.0" "1.0.0+build.1"))
    (-1);
  List.iter
    (fun v ->
      expect ("is_prerelease " ^ v)
        (Version.Semver.Strict.is_prerelease v)
        (Version.Semver.Loose.is_prerelease v))
    corpus;

  (* npm reads loosely, cargo strictly: without its hyphen a prerelease is
     the loose reading's alone *)
  expect "strict 2.0.14rc1 = 2.0.14"
    (sgn (Version.Semver.Strict.compare "2.0.14rc1" "2.0.14"))
    0;
  expect "loose 2.0.14rc1 < 2.0.14"
    (sgn (Version.Semver.Loose.compare "2.0.14rc1" "2.0.14"))
    (-1);
  expect "strict is_prerelease 2.0.14rc1"
    (Version.Semver.Strict.is_prerelease "2.0.14rc1")
    false;
  expect "loose is_prerelease 2.0.14rc1"
    (Version.Semver.Loose.is_prerelease "2.0.14rc1")
    true;

  if !fail > 0 then exit 1;
  print_endline "semver: all tests pass"
