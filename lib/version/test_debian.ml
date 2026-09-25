(* Debian's ordering, and opam's as that ordering with no epoch: the two
   agree on every version with no epoch, and only there. *)

let fail = ref 0
let sgn x = if x < 0 then -1 else if x > 0 then 1 else 0

let expect what got want =
  if got <> want then (
    Printf.eprintf "FAIL: %s = %d, want %d\n" what got want;
    incr fail)

let deb a b want =
  expect
    (Printf.sprintf "debian %S %S" a b)
    (sgn (Version.Debian.compare a b))
    want

let opam a b want =
  expect
    (Printf.sprintf "opam %S %S" a b)
    (sgn (Version.Debian.compare_no_epoch a b))
    want

let () =
  (* deb-version(7): '~' before the end, the end before letters, letters
     before other characters, digit runs as numbers *)
  deb "1.0~~" "1.0~" (-1);
  deb "1.0~" "1.0" (-1);
  deb "1.0" "1.0a" (-1);
  deb "1.0a" "1.0+" (-1);
  deb "1.2" "1.10" (-1);
  deb "09" "9" 0;
  deb "1.0-1~bpo1" "1.0-1" (-1);
  deb "1.0-1" "1.0.1-1" (-1);
  deb "1.0-2" "1.0-10" (-1);
  (* the epoch decides first, and 0 is the same as none *)
  deb "1:0.5" "2.0" 1;
  deb "0:1.0" "1.0" 0;
  deb "2:1" "10:0" (-1);
  (* a ':' after a non-digit is no epoch *)
  deb "a:1" "a:2" (-1);
  opam "1:0.5" "2.0" (-1);
  opam "0:1.0" "1.0" (-1);

  (* no epoch, one ordering *)
  let corpus =
    [
      "";
      "0";
      "1";
      "1.";
      "1.0";
      "1.00";
      "1.0~";
      "1.0~~";
      "1.0~rc1";
      "1.0a";
      "1.0+";
      "1.0-";
      "1.0-0";
      "1.0-1";
      "1.0-~";
      "1.0-10";
      "1-2-3";
      "1-2.3";
      "2.0-rc1";
      "2.0~rc1";
      "4.14.0";
      "4.14.0+options";
      "a";
      "a0";
      "0099";
      "99";
      "1.2.3-4.5";
      "1.0-1~bpo1";
      "2.4.dfsg";
      "2.4.dfsg.2";
    ]
  in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          expect
            (Printf.sprintf "debian and opam on %S %S" a b)
            (sgn (Version.Debian.compare_no_epoch a b))
            (sgn (Version.Debian.compare a b)))
        corpus)
    corpus;

  if !fail > 0 then exit 1;
  print_endline "debian: all tests pass"
