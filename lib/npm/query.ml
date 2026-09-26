module P = Npm_parse

let ( let* ) = Result.bind
let starts = P.starts

(* /^(?:git[+])?[a-z]+:/i *)
let is_url s =
  let s = String.lowercase_ascii s in
  let s = if starts "git+" s then String.sub s 4 (String.length s - 4) else s in
  let n = String.length s in
  let rec go i =
    i < n
    && if s.[i] = ':' then i > 0 else s.[i] >= 'a' && s.[i] <= 'z' && go (i + 1)
  in
  go 0

(* isPosixFile, /^(?:[.]|~[/]|[/]|[a-zA-Z]:)/, or what npa takes for a file
   before it looks for a name: an unscoped name part with a slash or a
   tarball's extension *)
let is_path s =
  starts "." s || starts "~/" s || starts "/" s
  || String.length s >= 2
     && s.[1] = ':'
     && Char.lowercase_ascii s.[0] >= 'a'
     && Char.lowercase_ascii s.[0] <= 'z'
  || (not (starts "@" s))
     && (String.contains s '/'
        || List.exists (Filename.check_suffix s) [ ".tgz"; ".tar.gz"; ".tar" ])

(* /^[^@]+@[^:.]+\.[^:]+:.+$/, an scp-style git remote *)
let is_git s =
  match String.index_opt s '@' with
  | Some i when i > 0 -> (
      let rest = String.sub s (i + 1) (String.length s - i - 1) in
      match String.index_opt rest ':' with
      | Some j -> (
          let host = String.sub rest 0 j in
          j + 1 < String.length rest
          &&
          match String.index_opt host '.' with
          | Some k -> k > 0 && k + 1 < j
          | None -> false)
      | None -> false)
  | _ -> false

(* an argument npa would read as a local path, which the query takes for
   the project's package.json *)
let is_manifest_arg s = (not (is_url s)) && (not (is_git s)) && is_path s

(* validate-npm-package-name 7.0.2's validForOldPackages, which npa
   tests: its errors, and none of its warnings *)
let name_ok n =
  n <> ""
  && (not (starts "." n))
  && (not (starts "-" n))
  && (not (starts "_" n))
  && String.trim n = n
  && (not
        (List.mem (String.lowercase_ascii n) [ "node_modules"; "favicon.ico" ]))
  && (P.uri_safe n
     ||
     match String.index_opt n '/' with
     | Some i when starts "@" n ->
         let pkg = String.sub n (i + 1) (String.length n - i - 1) in
         i > 1
         && (not (String.contains pkg '/'))
         && pkg <> ""
         && (not (starts "." pkg))
         && P.uri_safe (String.sub n 1 (i - 1))
         && P.uri_safe pkg
     | _ -> false)

(* The key and the raw spec: the name ends at the first @ past a scope's
   own, and a bare name or a trailing @ asks for *.  Whether a registry
   spec is a range or a tag is left to [classify], which has the
   packument's dist-tags. *)
let spec_of (arg : string) : (string * string) option =
  let n = String.length arg in
  let at = if n > 1 then String.index_from_opt arg 1 '@' else None in
  let name_part = match at with Some i -> String.sub arg 0 i | None -> arg in
  let raw =
    match at with
    | Some i -> (
        match String.sub arg (i + 1) (n - i - 1) with "" -> "*" | s -> s)
    | None -> "*"
  in
  if is_url arg || is_git arg || is_path name_part || not (name_ok name_part)
  then None
  else if P.is_alias raw then
    (* fromAlias: the target is read again, and must be a named registry
       spec and not itself an alias *)
    match P.split_alias raw with
    | Some (t, rg)
      when name_ok t
           && (not (P.is_alias rg))
           && (not (P.unresolvable rg))
           && P.spec_of_string rg <> None ->
        Some (name_part, raw)
    | _ -> None
  else if is_url raw || is_path raw || P.has_sub raw "/" then None
  else if P.spec_of_string raw = None then None
  else Some (name_part, raw)

(* arborist's addRmPkgDeps.add, lib/add-rm-pkg-deps.js, for a request with
   no --save-* flag: the entry goes to the first field that already names
   it, in inferSaveType's order, else to dependencies, and replaces what is
   there unless it is *.  The fields a save type cannot coexist with lose
   the name, and an optional entry is mirrored into dependencies. *)
let add_to (pkg : Yojson.Safe.t) ((name, raw) : string * string) : Yojson.Safe.t
    =
  let member = P.member and assoc_of = P.assoc_of in
  let has f = List.mem_assoc name (assoc_of (member f pkg)) in
  let target =
    List.find_opt has
      [
        "devDependencies";
        "optionalDependencies";
        "dependencies";
        "peerDependencies";
      ]
    |> Option.value ~default:"dependencies"
  in
  let drop =
    match target with
    | "dependencies" -> [ "devDependencies"; "peerDependencies" ]
    | "devDependencies" -> [ "dependencies" ]
    | "optionalDependencies" -> [ "peerDependencies" ]
    | _ -> [ "dependencies"; "optionalDependencies" ]
  in
  let drop =
    if List.mem "peerDependencies" drop then "peerDependenciesMeta" :: drop
    else drop
  in
  (* a JavaScript object keeps a new key last *)
  let set k v l =
    if List.mem_assoc k l then
      List.map (fun (k', x) -> if k' = k then (k, v) else (k', x)) l
    else l @ [ (k, v) ]
  in
  let fields =
    List.map
      (fun (k, v) ->
        if List.mem k drop then (k, `Assoc (List.remove_assoc name (assoc_of v)))
        else (k, v))
      (assoc_of pkg)
  in
  let cur = assoc_of (member target (`Assoc fields)) in
  let fields =
    if raw <> "*" || not (List.mem_assoc name cur) then
      set target (`Assoc (set name (`String raw) cur)) fields
    else fields
  in
  if target = "optionalDependencies" then
    let spec = member name (member target (`Assoc fields)) in
    set "dependencies"
      (`Assoc (set name spec (assoc_of (member "dependencies" (`Assoc fields)))))
      fields
    |> fun l -> `Assoc l
  else `Assoc fields

let manifest (paths : string list) : (Yojson.Safe.t, string) result =
  match paths with
  | [] -> Ok (`Assoc [])
  | [ p ] -> (
      Pac_common.Input.file p;
      match Yojson.Safe.from_file p with
      | `Assoc _ as j -> Ok j
      | _ | (exception Yojson.Json_error _) -> Error (p ^ ": not a package.json")
      )
  | _ -> Error "more than one package.json"

let not_registry s =
  Error
    (s
   ^ ": not a registry spec (name, name@range, name@tag, key@npm:name@range)")

(* npm refuses a dist-tag that is a range, so a spec the packument tags is
   a tag, and one it does not is a range unless it can only be a tag *)
let classify ar s : ([ `Plain | `Tagged ] * (string * string), string) result =
  match spec_of s with
  | None -> not_registry s
  | Some (k, r) when P.is_alias r || r = "*" -> Ok (`Plain, (k, r))
  | Some (k, r) -> (
      let r' = String.trim r in
      match Archive.dist_tag ar k r' with
      | Some v -> Ok (`Tagged, (k, v))
      | None -> (
          match P.spec_of_string r with
          | Some (P.Tag _) -> Error (s ^ ": no such dist-tag")
          | Some (P.Range _ | P.Star) -> Ok (`Plain, (k, r))
          | None -> not_registry s))

(* arborist's #add resolves a tag to its version only after an await, so
   the other specs are all added first, in order. *)
let resolve_specs ar specs =
  let* classified =
    List.fold_left
      (fun acc s ->
        let* l = acc in
        let* c = classify ar s in
        Ok (c :: l))
      (Ok []) specs
  in
  let only kind =
    List.rev
      (List.filter_map
         (fun (k, e) -> if k = kind then Some e else None)
         classified)
  in
  Ok (only `Plain @ only `Tagged)

let target (k, r) = match P.split_alias r with Some (t, _) -> t | None -> k

(* npm fetches each spec's packument while building the tree, and E404s
   on a name the registry lacks rather than resolving without it *)
let check_published ar specs =
  let unpublished s = Archive.versions_of ar (target s) = [] in
  match List.find_opt unpublished specs with
  | None -> Ok ()
  | Some s ->
      Error
        (Printf.sprintf "no packument for %s under %s%s" (target s)
           ar.Archive.cache
           (if ar.Archive.offline then " (offline)" else ""))

(* arborist names a root with no name by its directory, which is no part
   of the query; "." is a name no registry package can have *)
let root_of ar pkg =
  let str k = match P.member k pkg with `String s -> s | _ -> "" in
  let name = match str "name" with "" -> "." | n -> n in
  match P.ver_of ~reject:(Archive.reject ar) ~root:true (str "version") pkg with
  | Some v -> Ok { v with P.v_name = name }
  | None -> Error "not a package.json"

(* The query is a root package: a project's package.json with the
   arguments of `npm install` added to it.  An argument is read as
   npm-package-arg 13.0.2 (npm 11.17.0) reads it, lib/npa.js, and only its
   registry forms are accepted: name, name@version, name@range, name@tag
   and key@npm:name@range.  Anything npa reads as a file, directory, URL or
   git spec is refused rather than dropped, because a query missing one of
   its arguments asks a different question. *)
let root ar (args : string list) : (P.ver, string) result =
  let paths, specs = List.partition is_manifest_arg args in
  let* pkg = manifest paths in
  let* specs = resolve_specs ar specs in
  let* () = check_published ar specs in
  root_of ar (List.fold_left add_to pkg specs)
