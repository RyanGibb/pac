module P = Cargo_parse
module T = Cargo_toml

exception Refused of string

let refuse fmt = Printf.ksprintf (fun s -> raise (Refused s)) fmt

(* Rust's str::trim, which cargo's reading of package.version applies
   (InheritableSemverVersion's deserializer, cargo-util-schemas): it strips
   Unicode's White_Space, not only the ASCII blanks String.trim does *)
let rust_trim s =
  let white u =
    let c = Uchar.to_int u in
    (c >= 0x9 && c <= 0xD)
    || (c >= 0x2000 && c <= 0x200A)
    || List.mem c [ 0x20; 0x85; 0xA0; 0x1680; 0x2028; 0x2029; 0x202F; 0x205F; 0x3000 ]
  in
  let n = String.length s in
  (* the end of the character at i, and whether it is white *)
  let at i =
    let d = String.get_utf_8_uchar s i in
    ( i + Uchar.utf_decode_length d,
      Uchar.utf_decode_is_valid d && white (Uchar.utf_decode_uchar d) )
  in
  let rec left i =
    if i < n then match at i with j, true -> left j | _ -> i else i
  in
  let rec right i last =
    if i < n then match at i with j, true -> right j last | j, _ -> right j j
    else last
  in
  let i = left 0 in
  String.sub s i (right i i - i)

type root = {
  ver : P.ver;
  (* [patch.crates-io] maps the root's own name to it, which is what the
     model's one node per (name, version) already says; without it cargo
     keeps the root apart from the registry's crate of that name *)
  self_patch : bool;
  (* the resolver the manifest selects is 3, the one whose MSRV preference
     reaches version selection *)
  msrv_pref : bool;
}

(* the root's feature request.  All is the lock's: every key of the root's
   feature table, as resolve_with_registry asks with
   CliFeatures::new_all(true).  Named is --features: the named features,
   plus default unless --no-default-features, as CliFeatures reads the
   flags; it resolves afresh rather than filtering the lock. *)
type features = All | Named of { feats : string list; default : bool }

let describe = function
  | T.Str _ -> "a string"
  | T.Int _ -> "an integer"
  | T.Float _ -> "a float"
  | T.Bool _ -> "a boolean"
  | T.Date _ -> "a date"
  | T.Arr _ -> "an array"
  | T.Tbl _ -> "a table"
  | T.ATbl _ -> "an array of tables"

let str where = function
  | T.Str s -> s
  | T.Tbl { fields; _ } when List.mem_assoc "workspace" fields ->
      refuse "%s inherits from a workspace, which a lone manifest has not got"
        where
  | v -> refuse "%s is %s, not a string" where (describe v)

let bool where = function
  | T.Bool b -> b
  | v -> refuse "%s is %s, not a boolean" where (describe v)

let strings where = function
  | T.Arr l -> List.map (str where) l
  | v -> refuse "%s is %s, not an array" where (describe v)

let table where = function
  | T.Tbl t -> t.T.fields
  | v -> refuse "%s is %s, not a table" where (describe v)

let get k fields = List.assoc_opt k fields

let rec split_path s =
  let n = String.length s in
  let rec find i =
    if i + 1 >= n then None
    else if s.[i] = ':' && s.[i + 1] = ':' then Some i
    else find (i + 1)
  in
  match find 0 with
  | Some i -> String.sub s 0 i :: split_path (String.sub s (i + 2) (n - i - 2))
  | None -> [ s ]

(* restricted_names::validate_package_name, whose XID classes are read
   only over ASCII: crates.io publishes no other name *)
let package_name n =
  if not (String.for_all (fun c -> Char.code c < 128) n) then
    refuse "package name `%s`: a non-ASCII name is not modelled" n;
  let letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
  let digit c = c >= '0' && c <= '9' in
  let bad ch reason =
    refuse "invalid character `%c` in package name: `%s`, %s" ch n reason
  in
  List.iter
    (fun part ->
      if part = "" then refuse "package name cannot be empty";
      let c = part.[0] in
      if digit c then bad c "the name cannot start with a digit"
      else if not (letter c || c = '_') then
        bad c
          "the first character must be a Unicode XID start character (most \
           letters or `_`)";
      String.iter
        (fun c ->
          if not (letter c || digit c || c = '_' || c = '-') then
            bad c
              "characters must be Unicode XID characters (numbers, `-`, `_`, \
               or most letters)")
        part)
    (split_path n);
  n

(* dep_to_dependency, for the one source the index form has *)
let dep_of ~kind ~cfg ~where (alias, v) : P.dep =
  let alias = package_name alias in
  let where = Printf.sprintf "%s.%s" where alias in
  let fields =
    match v with T.Str r -> [ ("version", T.Str r) ] | v -> table where v
  in
  List.iter
    (fun (k, _) ->
      match k with
      | "path" | "git" | "branch" | "tag" | "rev" | "base" ->
          refuse
            "%s: a %s source is not a registry crate, and only the registry is \
             modelled"
            where k
      | "registry-index" ->
          refuse "%s: only the crates.io registry is modelled" where
      | "registry" ->
          if str where (List.assoc k fields) <> "crates-io" then
            refuse "%s: only the crates.io registry is modelled" where
      | "workspace" ->
          refuse
            "%s inherits from a workspace, which a lone manifest has not got"
            where
      | "public" ->
          refuse
            "%s: public dependencies are unstable in cargo and not modelled"
            where
      | "artifact" | "lib" | "target" ->
          refuse
            "%s: artifact dependencies are unstable in cargo and not modelled"
            where
      | _ -> ())
    fields;
  let req =
    match get "version" fields with
    | Some r -> str (where ^ ".version") r
    | None ->
        refuse
          "dependency (%s) specified without providing a local path, Git \
           repository, version, or workspace dependency to use"
          alias
  in
  if not (Cargo_version.req_ok req) then
    refuse "failed to parse the version requirement `%s` for dependency `%s`"
      req alias;
  let feats =
    match get "features" fields with
    | Some f -> strings (where ^ ".features") f
    | None -> []
  in
  List.iter
    (fun f ->
      if String.contains f '/' || String.starts_with ~prefix:"dep:" f then
        refuse
          "feature `%s` in dependency `%s` is not allowed to contain slashes \
           or use explicit `dep:` syntax"
          f alias)
    feats;
  let default =
    match (get "default-features" fields, get "default_features" fields) with
    | Some b, _ | None, Some b -> bool (where ^ ".default-features") b
    | None, None -> true
  in
  {
    P.d_alias = alias;
    d_target =
      (match get "package" fields with
      | Some p -> package_name (str (where ^ ".package") p)
      | None -> alias);
    d_req = Cargo_version.parse_req req;
    d_feats = feats;
    d_optional =
      (match get "optional" fields with
      | Some b -> bool (where ^ ".optional") b
      | None -> false);
    d_default = default;
    d_kind = kind;
    d_cfg = cfg;
  }

let kinds =
  [
    ("dependencies", P.Normal);
    ("dev-dependencies", P.Dev);
    ("dev_dependencies", P.Dev);
    ("build-dependencies", P.Build);
    ("build_dependencies", P.Build);
  ]

let deps_of ~cfg ~prefix fields =
  List.concat_map
    (fun (k, kind) ->
      match get k fields with
      | None -> []
      | Some v ->
          let where = prefix ^ k in
          List.map (dep_of ~kind ~cfg ~where) (table where v))
    kinds

(* the edition's resolver when neither [package] nor [workspace] names one
   (Edition::default_resolve_behavior) *)
let resolver_of_edition = function
  | "2015" | "2018" -> 1
  | "2021" -> 2
  | "2024" -> 3
  | e -> refuse "edition %S is not one cargo 1.97 knows" e

let resolver_of = function
  | "1" -> 1
  | "2" -> 2
  | "3" -> 3
  | r -> refuse "resolver %S is not one cargo 1.97 knows" r

let crates_io = [ "crates-io"; "https://github.com/rust-lang/crates.io-index" ]

(* the resolver [package] or [workspace] names, else the edition's *)
let resolver_of_manifest doc pkg =
  let ws_resolver =
    match get "workspace" doc with
    | None -> None
    | Some w ->
        let w = table "workspace" w in
        List.iter
          (fun (k, _) ->
            if k <> "resolver" then
              refuse
                "workspace.%s: a workspace beyond its resolver is not \
                 modelled; the root is one package"
                k)
          w;
        Option.map
          (fun r -> resolver_of (str "workspace.resolver" r))
          (get "resolver" w)
  in
  match
    ( Option.map
        (fun r -> resolver_of (str "package.resolver" r))
        (get "resolver" pkg),
      ws_resolver )
  with
  | Some _, Some _ ->
      refuse
        "cannot specify `resolver` field in both `[workspace]` and `[package]`"
  | Some r, None | None, Some r -> r
  | None, None ->
      resolver_of_edition
        (match get "edition" pkg with
        | Some e -> str "package.edition" e
        | None -> "2015")

(* the unconditional tables, then each [target.'cfg'] one *)
let deps_of_manifest doc =
  deps_of ~cfg:"" ~prefix:"" doc
  @
  match get "target" doc with
  | None -> []
  | Some t ->
      List.concat_map
        (fun (cfg, p) ->
          let prefix = Printf.sprintf "target.'%s'." cfg in
          deps_of ~cfg ~prefix (table ("target." ^ cfg) p))
        (table "target" t)

(* whether [patch.crates-io] maps the root's own name to the root, the one
   patch modelled *)
let self_patch_of doc name =
  match get "patch" doc with
  | None -> false
  | Some p ->
      List.iter
        (fun (reg, entries) ->
          if not (List.mem reg crates_io) then
            refuse "[patch.%s]: only crates.io is modelled" reg;
          List.iter
            (fun (k, v) ->
              let e = table (Printf.sprintf "patch.%s.%s" reg k) v in
              match e with
              | [ ("path", T.Str ("." | "./")) ] when k = name -> ()
              | _ ->
                  refuse
                    "[patch.%s] %s: the only patch modelled maps the root's \
                     own name to the root, { path = \".\" }"
                    reg k)
            (table ("patch." ^ reg) entries))
        (table "patch" p);
      true

let rust_version r =
  let r = str "package.rust-version" r in
  if not (Cargo_version.partial_ok ~rust:true r) then
    refuse "package.rust-version %S is not a version like \"1.32\"" r;
  r

(* as cargo 1.97's util/toml/mod.rs reads a manifest.  The root becomes
   one more crate version, so a field with no place in the index form -- a
   path or git source, another registry, a [patch] other than the root's
   own, workspace inheritance -- would change the question cargo is asked
   without changing ours, and is refused. *)
let of_manifest (path : string) : root =
  let doc =
    try (T.of_file path).T.fields with T.Error e -> refuse "%s: %s" path e
  in
  List.iter
    (fun (k, _) ->
      match k with
      | "cargo-features" ->
          refuse "cargo-features enables unstable cargo, which is not modelled"
      | "project" ->
          refuse "[project] is the old spelling of [package]; use that"
      | "replace" ->
          refuse "[replace] is not modelled; the registry is taken as it is"
      | _ -> ())
    doc;
  let pkg =
    match get "package" doc with
    | Some p -> table "package" p
    | None ->
        refuse "%s has no [package]: a virtual workspace is not a root" path
  in
  let name =
    match get "name" pkg with
    | Some n -> package_name (str "package.name" n)
    | None -> refuse "package.name is missing"
  in
  if String.contains name ':' then
    refuse
      "package name `%s` needs the unstable open-namespaces feature, which is \
       not modelled"
      name;
  let vers =
    match get "version" pkg with
    | Some v ->
        let v = str "package.version" v in
        let t = rust_trim v in
        if not (Cargo_version.version_ok t) then
          refuse "package.version %S is not a semver version like \"1.2.3\"" v;
        t
    | None -> "0.0.0"
  in
  let resolver = resolver_of_manifest doc pkg in
  let deps = deps_of_manifest doc in
  let declared =
    match get "features" doc with
    | None -> []
    | Some f ->
        List.map
          (fun (k, es) ->
            (k, List.map P.entry_of (strings ("features." ^ k) es)))
          (table "features" f)
  in
  if not (P.feature_map_ok deps declared) then
    refuse
      "%s: [features] is not a table cargo accepts: every entry names a \
       feature, an optional dependency (dep:), or a dependency's feature"
      path;
  let self_patch = self_patch_of doc name in
  {
    ver =
      {
        P.v_name = name;
        v_vers = vers;
        v_deps = deps;
        v_feats = P.with_implicit_features deps declared;
        v_links = Option.map (str "package.links") (get "links" pkg);
        v_default_declared = List.mem_assoc P.default_feature declared;
        v_msrv = Option.map rust_version (get "rust-version" pkg);
      };
    self_patch;
    msrv_pref = resolver >= 3;
  }

let crate (r : root) = (r.ver.P.v_name, r.ver.P.v_vers)

(* cargo splits each --features value on spaces and commas, and an empty
   value names nothing: [-F ""] still asks for default.  A name the root's
   table lacks is cargo's MissingFeature; the placeholder default the parser
   adds is not a key of cargo's. *)
let features_of_flags (r : root) (flags : string list) ~(no_default : bool) :
    features =
  if flags = [] && not no_default then All
  else
    let feats =
      List.concat_map
        (fun f ->
          List.filter (( <> ) "")
            (String.split_on_char ','
               (String.map (function ' ' | '\t' -> ',' | c -> c) f)))
        flags
    in
    List.iter
      (fun f ->
        if String.contains f '/' then
          refuse
            "--features %s: a dependency's feature on the command line is not \
             modelled"
            f
        else if
          (not (List.mem_assoc f r.ver.P.v_feats))
          || (f = P.default_feature && not r.ver.P.v_default_declared)
        then
          refuse "the package `%s v%s` does not have the feature `%s`"
            r.ver.P.v_name r.ver.P.v_vers f)
      feats;
    Named { feats; default = not no_default }

(* the toolchain resolve.rs ranks candidates against: the root's own
   rust-version, and only when it declares none the installed rustc; under
   resolvers 1 and 2, nothing *)
let toolchain (r : root) ~(installed : string option) : string option =
  Option.iter
    (fun t ->
      if not (Cargo_version.partial_ok ~rust:false t) then
        refuse "--rust-version %s is not a version like \"1.32\" or \"1.32.0\""
          t)
    installed;
  if not r.msrv_pref then None
  else match r.ver.P.v_msrv with Some m -> Some m | None -> installed
