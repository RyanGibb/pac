(* Trusted (TCB) reading of a Cargo query, a root Cargo.toml, into the root
   package the calculus takes (paper §Cargo), as cargo 1.97's
   util/toml/mod.rs reads one.  The root becomes one more crate version, so every
   field it has is one the index form already carries; a field with no
   place there -- a path or git source, another registry, a [patch] other
   than the root's own, workspace inheritance -- would change the question
   cargo is asked without changing ours, and is refused. *)

module P = Cargo_parse
module T = Cargo_toml

exception Refused of string

let refuse fmt = Printf.ksprintf (fun s -> raise (Refused s)) fmt

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

(* dep_to_dependency, for the one source the index form has *)
let dep_of ~kind ~cfg ~where (alias, v) : P.dep =
  let where = Printf.sprintf "%s.%s" where alias in
  let fields =
    match v with T.Str r -> [ ("version", T.Str r) ] | v -> table where v
  in
  List.iter
    (fun (k, _) ->
      match k with
      | "path" | "git" | "branch" | "tag" | "rev" | "base" ->
          refuse "%s: a %s source is not a registry crate, and only the \
                  registry is modelled" where k
      | "registry-index" ->
          refuse "%s: only the crates.io registry is modelled" where
      | "registry" ->
          if str where (List.assoc k fields) <> "crates-io" then
            refuse "%s: only the crates.io registry is modelled" where
      | "workspace" ->
          refuse "%s inherits from a workspace, which a lone manifest has \
                  not got" where
      | "public" ->
          refuse "%s: public dependencies are unstable in cargo and not \
                  modelled" where
      | "artifact" | "lib" | "target" ->
          refuse "%s: artifact dependencies are unstable in cargo and not \
                  modelled" where
      | _ -> ())
    fields;
  let req =
    match get "version" fields with
    | Some r -> str (where ^ ".version") r
    | None ->
        refuse "dependency (%s) specified without providing a local path, \
                Git repository, version, or workspace dependency to use" alias
  in
  let feats =
    match get "features" fields with
    | Some f -> strings (where ^ ".features") f
    | None -> []
  in
  List.iter
    (fun f ->
      if String.contains f '/' || String.starts_with ~prefix:"dep:" f then
        refuse "feature `%s` in dependency `%s` is not allowed to contain \
                slashes or use explicit `dep:` syntax" f alias)
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
      | Some p -> str (where ^ ".package") p
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

let of_manifest (path : string) : root =
  let doc =
    try (T.of_file path).T.fields with
    | T.Error e -> refuse "%s: %s" path e
    | Sys_error e -> refuse "%s" e
  in
  List.iter
    (fun (k, _) ->
      match k with
      | "cargo-features" ->
          refuse "cargo-features enables unstable cargo, which is not modelled"
      | "project" -> refuse "[project] is the old spelling of [package]; use that"
      | "replace" -> refuse "[replace] is not modelled; the registry is taken as it is"
      | _ -> ())
    doc;
  let pkg =
    match get "package" doc with
    | Some p -> table "package" p
    | None -> refuse "%s has no [package]: a virtual workspace is not a root" path
  in
  let name =
    match get "name" pkg with
    | Some n -> str "package.name" n
    | None -> refuse "package.name is missing"
  in
  let vers =
    match get "version" pkg with
    | Some v -> str "package.version" v
    | None -> "0.0.0"
  in
  let ws_resolver =
    match get "workspace" doc with
    | None -> None
    | Some w ->
        let w = table "workspace" w in
        List.iter
          (fun (k, _) ->
            if k <> "resolver" then
              refuse "workspace.%s: a workspace beyond its resolver is not \
                      modelled; the root is one package" k)
          w;
        Option.map (fun r -> resolver_of (str "workspace.resolver" r)) (get "resolver" w)
  in
  let resolver =
    match
      (Option.map (fun r -> resolver_of (str "package.resolver" r)) (get "resolver" pkg),
       ws_resolver)
    with
    | Some _, Some _ ->
        refuse "cannot specify `resolver` field in both `[workspace]` and `[package]`"
    | Some r, None | None, Some r -> r
    | None, None ->
        resolver_of_edition
          (match get "edition" pkg with
          | Some e -> str "package.edition" e
          | None -> "2015")
  in
  let deps =
    deps_of ~cfg:"" ~prefix:"" doc
    @ (match get "target" doc with
      | None -> []
      | Some t ->
          List.concat_map
            (fun (cfg, p) ->
              let prefix = Printf.sprintf "target.'%s'." cfg in
              deps_of ~cfg ~prefix (table ("target." ^ cfg) p))
            (table "target" t))
  in
  let declared =
    match get "features" doc with
    | None -> []
    | Some f ->
        List.map
          (fun (k, es) -> (k, List.map P.entry_of (strings ("features." ^ k) es)))
          (table "features" f)
  in
  let self_patch =
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
                    refuse "[patch.%s] %s: the only patch modelled maps the \
                            root's own name to the root, { path = \".\" }" reg k)
              (table ("patch." ^ reg) entries))
          (table "patch" p);
        true
  in
  {
    ver =
      {
        P.v_name = name;
        v_vers = vers;
        v_deps = deps;
        v_feats = P.with_implicit_features deps declared;
        v_links =
          Option.map (str "package.links") (get "links" pkg);
        v_default_declared = List.mem_assoc P.default_feature declared;
        v_msrv = Option.map (str "package.rust-version") (get "rust-version" pkg);
      };
    self_patch;
    msrv_pref = resolver >= 3;
  }
