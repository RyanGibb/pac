(* Trusted (TCB) ingestion of a crates.io-index checkout: one file per
   crate under a two-level prefix directory, one JSON object per line per
   published version.  The frontend desugarings the calculus expects are
   applied here: features2 (the v2 schema's dep:/dep?/ carrying table) is
   merged into features, feature entry strings are classified into the
   four FEntry shapes, and an optional dependency gains the implicit
   feature that activates it unless some entry names it with dep:.
   Unhandled shapes are counted and the enclosing row dropped. *)

type kind = Normal | Build | Dev

type dep = {
  d_alias : string; (* the manifest key: what dep:/a/feat entries name *)
  d_target : string; (* the published crate, differing under a rename *)
  d_req : Cargo_version.req;
  d_feats : string list;
  d_optional : bool;
  d_default : bool;
  d_kind : kind;
  d_cfg : string; (* the target cfg predicate, "" when unconditional *)
}

type fentry =
  | FFeat of string
  | FDep of string
  | FDepFeat of string * string
  | FWeakFeat of string * string

type ver = {
  v_name : string;
  v_vers : string;
  v_deps : dep list;
  v_feats : (string * fentry list) list;
  v_links : string option;
}

let rejected = ref 0
let reject () = incr rejected

(* crate files live at <index>/1/<n>, /2/<n>, /3/<c>/<n> or /<c1c2>/<c3c4>/<n>,
   with the name lowercased *)
let crate_path ~index (name : string) : string =
  let n = String.lowercase_ascii name in
  let l = String.length n in
  let ( / ) = Filename.concat in
  if l = 0 then index / "0"
  else if l = 1 then index / "1" / n
  else if l = 2 then index / "2" / n
  else if l = 3 then index / "3" / String.sub n 0 1 / n
  else index / String.sub n 0 2 / String.sub n 2 2 / n

open Yojson.Safe.Util

let str_opt j = match j with `String s -> Some s | _ -> None

let string_list j =
  match j with
  | `List l -> List.filter_map str_opt l
  | `Null -> []
  | _ ->
      reject ();
      []

let bool_def d j = match j with `Bool b -> b | `Null -> d | _ -> d

let kind_of j =
  match j with
  | `String "dev" -> Dev
  | `String "build" -> Build
  | `String "normal" | `Null -> Normal
  | _ ->
      reject ();
      Normal

let dep_of (j : Yojson.Safe.t) : dep option =
  match member "name" j with
  | `String alias ->
      let target =
        match member "package" j with `String p -> p | _ -> alias
      in
      let req = match member "req" j with `String r -> r | _ -> "*" in
      Some
        {
          d_alias = alias;
          d_target = target;
          d_req = Cargo_version.parse_req req;
          d_feats = string_list (member "features" j);
          d_optional = bool_def false (member "optional" j);
          (* the index omits the key only on very old rows, where cargo's
             own default (default features on) applies *)
          d_default = bool_def true (member "default_features" j);
          d_kind = kind_of (member "kind" j);
          d_cfg = (match member "target" j with `String t -> t | _ -> "");
        }
  | _ ->
      reject ();
      None

(* "dep:a" activates an optional slot, "a?/feat" is the weak form that
   delivers without activating, "a/feat" is the strong form, and a bare
   name is another feature of the same crate *)
let entry_of (s : string) : fentry =
  let dep_prefix = "dep:" in
  let n = String.length s in
  if n > 4 && String.sub s 0 4 = dep_prefix then
    let rest = String.sub s 4 (n - 4) in
    match String.index_opt rest '/' with
    | None -> FDep rest
    | Some i ->
        (* "dep:a/feat" is accepted by cargo as the strong form *)
        let a = String.sub rest 0 i in
        let f = String.sub rest (i + 1) (String.length rest - i - 1) in
        FDepFeat (a, f)
  else
    match String.index_opt s '/' with
    | None -> FFeat s
    | Some i ->
        let a = String.sub s 0 i in
        let f = String.sub s (i + 1) (String.length s - i - 1) in
        if a <> "" && a.[String.length a - 1] = '?' then
          FWeakFeat (String.sub a 0 (String.length a - 1), f)
        else FDepFeat (a, f)

let feature_table (j : Yojson.Safe.t) : (string * fentry list) list =
  let of_assoc j =
    match j with
    | `Assoc l ->
        List.map (fun (k, v) -> (k, List.map entry_of (string_list v))) l
    | `Null -> []
    | _ ->
        reject ();
        []
  in
  let a = of_assoc (member "features" j)
  and b = of_assoc (member "features2" j) in
  (* features2 is an overlay: a key present in both contributes to one
     feature, so merge rather than shadow *)
  let tbl = Hashtbl.create 16 in
  let order = ref [] in
  let add (k, es) =
    (match Hashtbl.find_opt tbl k with
    | None -> order := k :: !order
    | Some _ -> ());
    Hashtbl.replace tbl k
      (es @ match Hashtbl.find_opt tbl k with Some p -> p | None -> [])
  in
  List.iter add a;
  List.iter add b;
  List.rev_map (fun k -> (k, Hashtbl.find tbl k)) !order

let mentions_dep (tbl : (string * fentry list) list) (a : string) : bool =
  List.exists
    (fun (_, es) -> List.exists (function FDep b -> b = a | _ -> false) es)
    tbl

(* "default" always exists, empty when the manifest does not define it:
   every dependency that has not opted out requests it, and cargo treats
   the request as a no-op rather than an error *)
let default_feature = "default"

(* an optional dependency's implicit feature, suppressed by any dep: entry
   naming it and by an explicit feature of the same name *)
let with_implicit_features (deps : dep list) (tbl : (string * fentry list) list)
    : (string * fentry list) list =
  let tbl =
    if List.mem_assoc default_feature tbl then tbl
    else tbl @ [ (default_feature, []) ]
  in
  let extra =
    List.filter_map
      (fun d ->
        if
          d.d_optional
          && (not (List.mem_assoc d.d_alias tbl))
          && not (mentions_dep tbl d.d_alias)
        then Some (d.d_alias, [ FDep d.d_alias ])
        else None)
      deps
  in
  tbl @ extra

let parse_line (line : string) : ver option =
  match Yojson.Safe.from_string line with
  | exception _ ->
      reject ();
      None
  | j -> (
      match (member "name" j, member "vers" j) with
      | `String name, `String vers ->
          if bool_def false (member "yanked" j) then None
          else
            let deps =
              match member "deps" j with
              | `List l -> List.filter_map dep_of l
              | `Null -> []
              | _ ->
                  reject ();
                  []
            in
            let tbl = with_implicit_features deps (feature_table j) in
            Some
              {
                v_name = name;
                v_vers = vers;
                v_deps = deps;
                v_feats = tbl;
                v_links = str_opt (member "links" j);
              }
      | _ ->
          reject ();
          None)

let load_crate ~index (name : string) : ver list =
  let path = crate_path ~index name in
  if not (Sys.file_exists path) then []
  else
    let ic = open_in_bin path in
    let acc = ref [] in
    (try
       while true do
         let line = input_line ic in
         if String.trim line <> "" then
           match parse_line line with Some v -> acc := v :: !acc | None -> ()
       done
     with End_of_file -> ());
    close_in ic;
    List.rev !acc
