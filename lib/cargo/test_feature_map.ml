open Cargo_parse

(* feature_map_ok as it stood before it was made linear, a scan per check,
   which the linear one must agree with on every table *)
let reference deps tbl =
  let dep a = List.exists (fun d -> d.d_alias = a) deps in
  let optional a = List.exists (fun d -> d.d_optional && d.d_alias = a) deps in
  let mentions a =
    List.exists
      (fun (_, es) -> List.exists (function FDep b -> b = a | _ -> false) es)
      tbl
  in
  let implicit =
    List.filter_map
      (fun d ->
        if
          d.d_optional
          && (not (List.mem_assoc d.d_alias tbl))
          && not (mentions d.d_alias)
        then Some (d.d_alias, [ FDep d.d_alias ])
        else None)
      deps
  in
  let map = tbl @ implicit in
  let name_ok f =
    let alnum c =
      (c >= 'a' && c <= 'z')
      || (c >= 'A' && c <= 'Z')
      || (c >= '0' && c <= '9')
      || c = '_'
      || Char.code c >= 128
    in
    f <> ""
    && (not (String.starts_with ~prefix:"dep:" f))
    && alnum f.[0]
    && String.for_all (fun c -> alnum c || c = '-' || c = '+' || c = '.') f
  in
  let entry_ok = function
    | FFeat f -> List.mem_assoc f tbl || (optional f && List.mem_assoc f map)
    | FDep a -> optional a
    | FDepFeat (a, f) -> dep a && not (String.contains f '/')
    | FWeakFeat (a, f) -> optional a && not (String.contains f '/')
  in
  let used a =
    List.exists
      (fun (_, es) ->
        List.exists
          (function
            | FDep b | FDepFeat (b, _) | FWeakFeat (b, _) -> b = a
            | FFeat _ -> false)
          es)
      map
  in
  List.for_all (fun (f, es) -> name_ok f && List.for_all entry_ok es) map
  && List.for_all (fun d -> (not d.d_optional) || used d.d_alias) deps

let d ?(optional = false) a =
  {
    d_alias = a;
    d_target = a;
    d_req = Cargo_version.parse_req "*";
    d_feats = [];
    d_optional = optional;
    d_default = true;
    d_kind = Normal;
    d_cfg = "";
  }

let o a = d ~optional:true a
let fail = ref 0

let check name deps tbl exp =
  let tbl = List.map (fun (f, es) -> (f, List.map entry_of es)) tbl in
  let got = feature_map_ok deps tbl and spec = reference deps tbl in
  if got <> exp || spec <> exp then (
    Printf.eprintf "FAIL: %s: feature_map_ok %b, reference %b, expected %b\n"
      name got spec exp;
    incr fail)

let () =
  check "empty" [] [] true;
  check "implicit feature" [ o "a" ] [] true;
  check "implicit feature named" [ o "a" ] [ ("x", [ "a" ]) ] true;
  check "dep: suppresses the implicit feature"
    [ o "a" ]
    [ ("x", [ "dep:a" ]); ("y", [ "a" ]) ]
    false;
  check "dep: uses" [ o "a" ] [ ("x", [ "dep:a" ]) ] true;
  check "explicit feature of the alias's name"
    [ o "a" ]
    [ ("a", [ "dep:a" ]) ]
    true;
  check "explicit feature, dependency unused" [ o "a" ] [ ("a", []) ] false;
  check "weak feature uses" [ o "a" ] [ ("a", []); ("x", [ "a?/f" ]) ] true;
  check "strong feature uses" [ o "a" ] [ ("a", []); ("x", [ "a/f" ]) ] true;
  check "unknown feature" [] [ ("x", [ "y" ]) ] false;
  check "dep: on a non-optional" [ d "b" ] [ ("x", [ "dep:b" ]) ] false;
  check "strong feature on a non-optional" [ d "b" ] [ ("x", [ "b/f" ]) ] true;
  check "weak feature on a non-optional" [ d "b" ] [ ("x", [ "b?/f" ]) ] false;
  check "strong feature on no dependency" [] [ ("x", [ "c/f" ]) ] false;
  check "slash in the dependency's feature"
    [ d "b" ]
    [ ("x", [ "b/f/g" ]) ]
    false;
  check "dep: with a feature" [ o "a" ] [ ("x", [ "dep:a/f" ]) ] false;
  check "empty name" [] [ ("", []) ] false;
  check "dep: name" [] [ ("dep:x", []) ] false;
  check "leading hyphen" [] [ ("-x", []) ] false;
  check "inner punctuation" [] [ ("x-y+z.w", []) ] true;
  check "non-ASCII" [] [ ("\xc3\xa9", []) ] true;
  check "implicit feature's name checked" [ o "+a" ] [] false;
  check "duplicate optional" [ o "a"; o "a" ] [] true;
  check "optional beside non-optional"
    [ d "a"; o "a" ]
    [ ("x", [ "a/f" ]) ]
    true;
  check "feature of a suppressed implicit"
    [ o "a"; o "b" ]
    [ ("x", [ "dep:a"; "b" ]); ("y", [ "a" ]) ]
    false;
  if !fail > 0 then exit 1;
  print_endline "feature_map: all tests pass"
