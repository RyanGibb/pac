open Debian_frontend
module A = Apt_args

let fails = ref 0

let check what ok =
  if not ok then (
    Printf.printf "FAIL: %s\n" what;
    incr fails)

let st ?(arch = "amd64") ?(provides = []) package version : Deb_packages.stanza
    =
  {
    package;
    version;
    architecture = arch;
    multi_arch = None;
    depends_raw = [];
    recommends_raw = [];
    provides =
      List.map
        (fun (pname, pversion) -> { Deb_packages.pname; pversion })
        provides;
    conflicts = [];
    essential = false;
    important = false;
    priority = Deb_packages.priority_lowest;
    source = (package, version);
  }

let index =
  [
    st "pinv" "1";
    st "pinv" "2";
    st "pinglob" "1.2";
    st "pinglob" "1.23";
    st "pinmix" "1";
    st ~arch:"all" "pinmix" "2";
    st ~provides:[ ("pinself", Some "5") ] "pinself" "1";
    st ~arch:"i386" "xunq" "1";
    st "dup" "1";
    st ~provides:[ ("dupvirt", None) ] "dup" "1";
    st "exv" "1.0";
    st "exv" "1.00";
  ]

let elem arg =
  A.query_element ~native:"amd64" ~arches:[ "amd64"; "i386" ] index arg

let accepts = function A.Any -> "any" | A.Only v -> "=" ^ v

let expect arg key acc =
  match elem arg with
  | Ok (k, a) ->
      check
        (Printf.sprintf "%s -> %s:%s %s (got %s:%s %s)" arg (fst key) (snd key)
           (accepts acc) (fst k) (snd k) (accepts a))
        (k = key && a = acc)
  | Error e ->
      check
        (Printf.sprintf "%s -> %s:%s %s (got refused: %s)" arg (fst key)
           (snd key) (accepts acc) e)
        false

let refused arg msg =
  match elem arg with
  | Error e ->
      check (Printf.sprintf "%s refused as %S (got %S)" arg msg e) (e = msg)
  | Ok _ -> check (Printf.sprintf "%s refused" arg) false

let () =
  (* fnmatch(3) with FNM_CASEFOLD *)
  check "fnmatch *" (A.fnmatch "1.*" "1.2");
  check "fnmatch ?" (A.fnmatch "1.?" "1.2" && not (A.fnmatch "1.?" "1.23"));
  check "fnmatch range"
    (A.fnmatch "[a-c]x" "bx" && not (A.fnmatch "[a-c]x" "dx"));
  check "fnmatch negated" (A.fnmatch "[!a]" "b" && not (A.fnmatch "[^a]" "a"));
  check "fnmatch casefold" (A.fnmatch "ABC" "abc");
  check "fnmatch escape" (A.fnmatch "a\\*" "a*" && not (A.fnmatch "a\\*" "ab"));
  check "fnmatch open bracket" (A.fnmatch "[a" "[a");
  (* the pattern less its trailing '*' is a prefix, or a glob *)
  check "version_matches exact" (A.version_matches "1.2" "1.2");
  check "version_matches case" (A.version_matches "1.0A" "1.0a");
  check "version_matches prefix" (A.version_matches "1.2*" "1.23");
  check "version_matches glob"
    (A.version_matches "1.*2*" "1.2" && not (A.version_matches "1.*2*" "1.23"));
  check "version_matches whole" (not (A.version_matches "1.2" "1.23"));
  (* one element of apt-get install's arguments *)
  expect "pinv" ("pinv", "amd64") A.Any;
  expect "pinv=1" ("pinv", "amd64") (A.Only "1");
  refused "pinv=3" "Version '3' for 'pinv' was not found";
  expect "pinv=*" ("pinv", "amd64") (A.Only "2");
  expect "pinv/candidate" ("pinv", "amd64") (A.Only "2");
  expect "pinv=newest" ("pinv", "amd64") (A.Only "2");
  refused "pinv=installed"
    "Can't select installed version from package pinv as it is not installed";
  refused "pinv/stable" "Release 'stable' for 'pinv' was not found";
  refused "xunq=2" "Version '2' for 'xunq:i386' was not found";
  expect "pinv/*" ("pinv", "amd64") (A.Only "2");
  expect "pinglob=1.*2*" ("pinglob", "amd64") (A.Only "1.2");
  expect "pinglob=1.2*" ("pinglob", "amd64") (A.Only "1.23");
  expect "pinmix:all=1" ("pinmix", "amd64") (A.Only "1");
  expect "pinmix:native" ("pinmix", "amd64") A.Any;
  expect "pinself=5" ("pinself", "amd64") (A.Only "1");
  expect "xunq" ("xunq", "i386") A.Any;
  refused "nothere" "Unable to locate package nothere";
  refused "nothere=1" "Unable to locate package nothere";
  refused "dupvirt" "Package 'dupvirt' has no installation candidate";
  (* the string, not the order: 1.0 and 1.00 compare equal *)
  expect "exv=1.00" ("exv", "amd64") (A.Only "1.00");
  expect "exv=1.0" ("exv", "amd64") (A.Only "1.0");
  (* of two elements naming one package the later wins *)
  let q, named =
    Result.get_ok
      (A.parse_query ~native:"amd64" ~arches:[ "amd64" ] index
         [ "pinv=2"; "pinglob"; "pinv=1"; "exv=1.00" ])
  in
  check "parse_query order"
    (q
    = [
        (("pinglob", "amd64"), A.Any);
        (("pinv", "amd64"), A.Only "1");
        (("exv", "amd64"), A.Only "1.00");
      ]);
  check "parse_query named"
    (Hashtbl.find_opt named ("pinv", "amd64") = Some "1"
    && Hashtbl.length named = 2);
  check "parse_query refused"
    (Result.is_error
       (A.parse_query ~native:"amd64" ~arches:[ "amd64" ] index
          [ "pinv"; "pinv=3" ]));
  (* the candidate: the newest, a named version, the first of two stanzas
     at one version *)
  let versions l =
    List.map (fun (s : Deb_packages.stanza) -> (s.package, s.version)) l
  in
  let kept = A.pin_candidates ~native:"amd64" ~named index in
  check "pin_candidates"
    (versions kept
    = [
        ("pinv", "1");
        ("pinglob", "1.23");
        ("pinmix", "2");
        ("pinself", "1");
        ("xunq", "1");
        ("dup", "1");
        ("exv", "1.00");
      ]);
  check "pin_candidates first read"
    ((List.find (fun (s : Deb_packages.stanza) -> s.package = "dup") kept)
       .provides = []);
  if !fails > 0 then exit 1;
  print_endline "apt_args: all tests pass"
