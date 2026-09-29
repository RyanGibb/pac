let fail = ref 0

let spec = function
  | Npm_parse.Range r -> Npm_version.string_of_range r
  | Star -> "*"
  | Tag t -> "tag " ^ t

let show_ver (v : Npm_parse.ver) =
  Printf.sprintf "%s %s [%s]%s%s" v.v_vers v.v_name
    (String.concat "; "
       (List.map
          (fun (d : Npm_parse.dep) -> d.d_name ^ " " ^ spec d.d_spec)
          v.v_deps))
    (if v.v_deprecated then " deprecated" else "")
    (match v.v_eng_node with
    | Some r -> " node " ^ Npm_version.string_of_range r
    | None -> "")

let load doc =
  let f = Filename.temp_file "packument" ".json" in
  Out_channel.with_open_bin f (fun oc -> output_string oc doc);
  let n = ref 0 in
  let r = Npm_parse.load ~reading:`Npm ~reject:(fun () -> incr n) f in
  Sys.remove f;
  match r with
  | Error e -> "error " ^ e
  | Ok pk ->
      String.concat " | "
        ((match pk.pk_latest with Some l -> "latest " ^ l | None -> "-")
         :: List.map (fun (t, v) -> t ^ "=" ^ v) pk.pk_tags
        @ List.map show_ver pk.pk_vers
        @ [ Printf.sprintf "%d dropped" !n ])

let check doc exp =
  let got = load doc in
  if got <> exp then (
    Printf.printf "FAIL %S\n  got  %S\n  want %S\n" doc got exp;
    incr fail)

let bad = "error not a packument"

let () =
  check
    {|{"dist-tags":{"latest":"1.0.0"},"versions":{"1.0.0":{"name":"a","dependencies":{"b":"^1"},"dist":{"x":1}}}}|}
    "latest 1.0.0 | latest=1.0.0 | 1.0.0 a [b >=1.0.0 <2.0.0] | 0 dropped";
  (* what is skipped is still read as Yojson reads it *)
  check
    {|{"readme":"\n\u00e9\ud83d\ude00\udc00","time":{"a":NaN,"b":-Infinity,"c":1e400,"d":123456789012345678901234},"x":[true,false,null,-0.5E+3,[],{}],"versions":{}}|}
    "- | 0 dropped";
  check {|{"readme":"\ud83d","versions":{}}|} bad;
  check {|{"readme":"\ud83d\u0041","versions":{}}|} bad;
  check {|{"readme":"\x"}|} bad;
  check {|{"readme":"\u12"}|} bad;
  check {|{"readme":"|} bad;
  check {|{"a":01}|} bad;
  check {|{"a":1.}|} bad;
  check {|{"a":.5}|} bad;
  check {|{"a":-}|} bad;
  check {|{"a":tru}|} bad;
  check {|{"a":[1,]}|} bad;
  check {|{"a":1,}|} bad;
  check {|{"a" 1}|} bad;
  check {|{1:2}|} bad;
  check {|{}x|} bad;
  check "" bad;
  check " \n" bad;
  check "[]" bad;
  check {|{"versions":{}}/*|} bad;
  check {|{"versions":{}}/*/|} bad;
  check "/*a*/{// b\n\"versions\"/**/:{\"1.0.0\"://c\n{\"name\":\"a\"}}}//end"
    "- | 1.0.0 a [] | 0 dropped";
  check {|{versions:{"1.0.0":{name:"a",dependencies:{b:"1"}}}}|}
    "- | 1.0.0 a [b >=1.0.0 <2.0.0] | 0 dropped";
  check {|{"vers\u0069ons":{"1.0.0":{"dependenc\u0069es":{"b":"1"}}}}|}
    "- | 1.0.0  [b >=1.0.0 <2.0.0] | 0 dropped";
  (* the first of a repeated key is the one read, and a repeated version
     or tag is kept twice *)
  check
    {|{"versions":{"1.0.0":{"dependencies":{"b":"1"},"dependencies":{"c":"1"},"engines":{"node":">=10","node":">=99"}}},"versions":{"2.0.0":{}}}|}
    "- | 1.0.0  [b >=1.0.0 <2.0.0] node >=10.0.0-0 | 0 dropped";
  check {|{"versions":{"1.0.0":{},"1.0.0":{"name":"b"}}}|}
    "- | 1.0.0  [] | 1.0.0 b [] | 0 dropped";
  check
    {|{"dist-tags":{"latest":"1.0.0","latest":"2.0.0","next":3},"dist-tags":{"latest":"9"}}|}
    "latest 1.0.0 | latest=1.0.0 | latest=2.0.0 | 0 dropped";
  (* a value of the wrong type *)
  check
    {|{"dist-tags":null,"versions":{"1.0.0":null,"2.0.0":[],"3.0.0":{"dependencies":null,"optionalDependencies":{"b":1}}}}|}
    "- | 3.0.0  [] | 3 dropped";
  check {|{"versions":null}|} "- | 0 dropped";
  check {|{"versions":[{"1.0.0":{}}]}|} "- | 0 dropped";
  check
    {|{"versions":{"a":{"deprecated":""},"b":{"deprecated":0},"c":{"deprecated":-0},"d":{"deprecated":false},"e":{"deprecated":null},"f":{"deprecated":0.0},"g":{"deprecated":"x"},"h":{"deprecated":NaN},"i":{"deprecated":{}}}}|}
    "- | a  [] | b  [] | c  [] | d  [] | e  [] | f  [] deprecated | g  [] \
     deprecated | h  [] deprecated | i  [] deprecated | 0 dropped";
  (match
     Npm_parse.load ~reading:`Npm ~reject:ignore "/nonexistent/packument.json"
   with
  | Error "/nonexistent/packument.json: No such file or directory" -> ()
  | _ ->
      print_endline "FAIL a missing file";
      incr fail);
  if !fail > 0 then exit 1 else print_endline "npm_parse: all tests pass"
