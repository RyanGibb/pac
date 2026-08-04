let check a rel b =
  let c = Debian_frontend.Deb_version.compare a b in
  let got = if c < 0 then "<" else if c > 0 then ">" else "=" in
  if got <> rel then (
    Printf.printf "FAIL: %s %s %s (got %s)\n" a rel b got;
    exit 1)

let () =
  (* Policy 5.6.12 corner cases *)
  check "1.0~rc1" "<" "1.0";
  check "1.0~~" "<" "1.0~";
  check "1.0~" "<" "1.0";
  check "1.0" "<" "1.0a";
  check "1.0a" "<" "1.0+";
  (* letters before non-letters *)
  check "09" "=" "9";
  check "1.2" "<" "1.10";
  check "1.0-1" "<" "1.0-2";
  check "1.0-1" "<" "1.0.1-1";
  check "1:0.5" ">" "2.0";
  check "0:1.0" "=" "1.0";
  check "1.0" "=" "1.0";
  check "2.4.dfsg" "<" "2.4.dfsg.2";
  check "1.0-1~bpo1" "<" "1.0-1";
  print_endline "deb_version: all tests pass"
