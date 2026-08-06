let check a b exp =
  let got = Opam_version.compare a b in
  let sgn x = if x < 0 then -1 else if x > 0 then 1 else 0 in
  if sgn got <> exp then (
    Printf.eprintf "FAIL: compare %S %S = %d, expected sign %d\n" a b got exp;
    exit 1)

let () =
  (* from the manual: ~~ < ~ < empty-suffix < ordinary *)
  check "1.0~~" "1.0~" (-1);
  check "1.0~" "1.0" (-1);
  check "1.0~beta" "1.0" (-1);
  check "1.0~beta2" "1.0~beta10" (-1);
  check "1.0" "1.0.1" (-1);
  check "0.2" "0.10" (-1);
  check "1.0" "1.0" 0;
  check "0099" "99" 0;
  (* letters before non-letters *)
  check "1.0a" "1.0+" (-1);
  check "1.0alpha" "1.0+" (-1);
  (* digit runs vs empty *)
  check "1" "1.0" (-1);
  check "2.1" "2.0.1" 1;
  (* dev suffixes *)
  check "4.14.0" "4.14.0+options" (-1);
  check "8.5" "8.5~rc1" 1;
  print_endline "opam_version: all tests pass"
