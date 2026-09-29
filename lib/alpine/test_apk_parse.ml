let fail = ref 0

let op = function
  | Apk_version.Eq -> "="
  | Lt -> "<"
  | Gt -> ">"
  | Le -> "<="
  | Ge -> ">="
  | Fuzzy -> "~"
  | Gt_fuzzy -> ">~"
  | Lt_fuzzy -> "<~"
  | Hash -> "><"

let dep (d : Apk_parse.dep) =
  (if d.d_neg then "!" else "")
  ^ d.d_name
  ^ match d.d_constr with Any -> "" | Op (o, v) -> op o ^ v

let prov (p : Apk_parse.prov) =
  p.p_name ^ match p.p_ver with None -> "" | Some v -> "=" ^ v

let pkg (p : Apk_parse.pkg) =
  Printf.sprintf "%s %s D[%s] p[%s] i[%s]%s" p.name p.version
    (String.concat "," (List.map dep p.depends))
    (String.concat "," (List.map prov p.provides))
    (String.concat "," (List.map dep p.install_if))
    (match p.priority with None -> "" | Some k -> Printf.sprintf " k%d" k)

(* the calls to reject and broken in order, then the packages *)
let case what index want =
  let path = Filename.temp_file "apkindex" "" in
  Out_channel.with_open_bin path (fun oc -> output_string oc index);
  let log = ref [] in
  let reject () = log := "reject" :: !log in
  let broken ns = log := ("broken " ^ String.concat " " ns) :: !log in
  let pkgs = Apk_parse.parse_file ~reject ~broken path in
  Sys.remove path;
  let got = List.map String.escaped (List.rev !log @ List.map pkg pkgs) in
  if got <> want then (
    Printf.printf "FAIL %s:\n  got  %s\n  want %s\n" what
      (String.concat " | " got) (String.concat " | " want);
    incr fail)

let () =
  case "an empty index" "" [];
  case "no newline at the end" "P:a\nV:1" [ "a 1 D[] p[] i[]" ];
  case "blank lines, and a one-byte line, end a stanza"
    "\n\nP:a\nV:1\nx\nP:b\nV:2\n\n\n"
    [ "a 1 D[] p[] i[]"; "b 2 D[] p[] i[]" ];
  case "a line that is not a field breaks its stanza"
    "P:a\nV:1\np:x=1\nnot a field\n\nP:b\nV:2\n"
    [ "broken a x"; "reject"; "b 2 D[] p[] i[]" ];
  case "a stanza with no P: is none" "V:1\nD:x\n\n" [];
  case "the last P: and V: stand, and either may be empty"
    "P:a\nP:b\nV:1\nV:2\n\nP:\nV:\n"
    [ "b 2 D[] p[] i[]"; "  D[] p[] i[]" ];
  case "a carriage return is part of the value" "P:a\r\nV:1\r\n"
    [ "a\\r 1\\r D[] p[] i[]" ];
  case "atoms are split on spaces alone, and D: lines add up"
    "P:a\nV:1\nD:  b   c \td \nD:\nD:e>=2\n"
    [ "a 1 D[b,c,\\td,e>=2] p[] i[]" ];
  case "any run of < > = ~ is an operator"
    "P:a\nV:1\nD:!b c==1 d<>=2 e><Q1x= f~1.2 g>~3 h=<4\n"
    [ "a 1 D[!b,c=1,d,e><Q1x=,f~1.2,g>~3,h<=4] p[] i[]" ];
  case "a D: atom apk cannot read breaks its stanza"
    "P:a1\n\
     V:1\n\
     p:x=1 y\n\
     D:b@tag\n\n\
     P:a2\n\
     V:1\n\
     D:!\n\n\
     P:a3\n\
     V:1\n\
     D:=1\n\n\
     P:a4\n\
     V:1\n\
     D:b>=\n\n\
     P:a5\n\
     V:1\n\
     D:b>=1.x!\n\n\
     P:a6\n\
     V:1\n\
     D:b\n"
    [
      "broken a1 y x";
      "reject";
      "broken a2";
      "reject";
      "broken a3";
      "reject";
      "broken a4";
      "reject";
      "broken a5";
      "reject";
      "a6 1 D[b] p[] i[]";
    ];
  case "an i: atom apk cannot read drops the rule, earlier lines included"
    "P:a\nV:1\ni:b\ni:c@tag\ni:d !e\n"
    [ "reject"; "a 1 D[] p[] i[d,!e]" ];
  case "p: skips an inequality and ends at an atom apk cannot read"
    "P:a\nV:1\np:x y=1 z>=2 w<>=1 !v =3 u=1\n"
    [ "reject"; "reject"; "reject"; "a 1 D[] p[x,y=1,v] i[]" ];
  case "the last k: that is an integer stands"
    "P:a\nV:1\nk:5\nk:x\nk:0x10\n\nP:b\nV:1\nk:-3\n"
    [ "reject"; "a 1 D[] p[] i[] k16"; "b 1 D[] p[] i[] k-3" ];
  case "unknown fields: lower-case ignored, upper-case breaks the stanza"
    "P:a\nV:1\nq:x\nZ:y\n\nP:b\nV:1\nY:x\n"
    [ "broken b"; "reject"; "a 1 D[] p[] i[]" ];
  if !fail > 0 then exit 1;
  print_endline "apk_parse: all tests pass"
