(* Trusted (TCB) ingestion of a registry packument: the JSON document at
   https://registry.npmjs.org/<name>, whose "versions" object maps each
   published version to its package.json manifest.

   What is trusted here, beyond the plumbing:

   - The registry itself.  A packument is taken at face value; nothing is
     checked against the tarball it describes.
   - Range *parsing* (npm_version.ml).  Evaluation is not trusted: a
     dependency carries the parsed comparator sets into the calculus,
     which decides which real versions they admit.
   - The dependency-spec classification below.  npm accepts git, file,
     link, workspace and tag specs that no registry lookup can resolve;
     those dependencies are dropped and counted rather than guessed at.
   Deliberately *not* read: "os", "cpu" and "libc".  npm consults none
   of them when choosing a version -- npm-pick-manifest has no platform
   key at all -- so a package-lock.json records every platform's variant
   of an optional dependency whatever host wrote it, and the filtering
   happens at install time (EBADPLATFORM).  Reading them here would make
   our instance strictly smaller than npm's.

   "engines" is a different case and is read, because npm-pick-manifest
   sorts on it.  It is not a gate: a version the host cannot run is
   ranked below one it can and is still installable when nothing else
   matches, which is why --engine-strict exists to promote the
   install-time warning to an error.  Only the "node" and "npm" sub-keys
   are live, because checkEngine tests those two and nothing else.

   - The optionalDependencies reading.  Such an entry is an ordinary
     dependency that npm abandons in exactly one situation: its manifest
     cannot be fetched, i.e. no published version matches the range.
     Nothing else drops it -- a peer conflict against an optional
     dependency is an ordinary ERESOLVE -- so it is parsed here as an
     ordinary dependency that merely remembers it was optional.  Whether
     the range is satisfiable is a question about the registry, not about this
     manifest, so the drop itself is in npm_solve.  npm documents an
     optionalDependencies entry as overriding a dependencies entry of
     the same name, which is what the dependency assembly below does.

   Not read: bundledDependencies.  npm takes those versions verbatim from
   the tarball, which this frontend neither fetches nor trusts. *)

type dep = {
  d_dir : string; (* the directory key, i.e. the manifest key *)
  d_target : string; (* the registry package, differing under npm: *)
  d_range : Npm_version.range;
  d_dev : bool;
  (* not carried into the calculus: it only tells the solver that this
     dependency may be abandoned when the registry cannot satisfy it *)
  d_optional : bool;
  (* the range was written as the literal "*" or left empty, which npm
     reads apart from every other range that means the same *)
  d_star : bool;
}

type peer = {
  p_name : string;
  p_range : Npm_version.range;
  p_optional : bool;
  p_star : bool;
}

type ver = {
  v_name : string;
  v_vers : string;
  v_deps : dep list;
  v_peers : peer list;
  v_ovr : (string * Npm_version.range) list;
  v_deprecated : bool;
  (* engines.node and engines.npm, the two sub-keys checkEngine tests;
     absent means the version imposes no requirement, which is what makes
     it rank above one whose requirement the host fails *)
  v_eng_node : Npm_version.range option;
  v_eng_npm : Npm_version.range option;
}

type packument = {
  pk_name : string;
  pk_latest : string option;
  pk_tags : (string * string) list;
  pk_vers : ver list;
}

let rejected = ref 0
let optional_count = ref 0
let deprecated_count = ref 0
let reject () = incr rejected

(* Yojson's [member] raises on a non-object; a registry manifest may omit
   any field or give it the wrong shape, so lookups go through this. *)
let member (k : string) (j : Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc l -> ( match List.assoc_opt k l with Some v -> v | None -> `Null)
  | _ -> `Null

let assoc_of j = match j with `Assoc l -> l | _ -> []

(* ---- dependency specifiers ---- *)

let has_sub s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  m = 0 || go 0

let starts p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

(* a bare identifier with no digit and no operator is a dist-tag, which
   only the registry can resolve -- except "x"/"X", which are semver's
   wildcards and mean the same as "*" *)
let looks_like_tag s =
  s <> "" && s <> "x" && s <> "X"
  && String.for_all
       (fun c -> (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '-')
       s

let unresolvable s =
  has_sub s "://" || starts "$" s || starts "git+" s || starts "git:" s
  || starts "file:" s || starts "link:" s || starts "workspace:" s
  || starts "portal:" s || starts "patch:" s
  || (has_sub s "/" && not (starts "npm:" s))
  || looks_like_tag s

(* "npm:bar@^1" and "npm:@scope/bar@^1": the separator is the last @ that
   is not the scope's leading one *)
let split_alias (s : string) : (string * string) option =
  if not (starts "npm:" s) then None
  else
    let body = String.sub s 4 (String.length s - 4) in
    let n = String.length body in
    let rec last i best =
      if i >= n then best
      else last (i + 1) (if body.[i] = '@' && i > 0 then i else best)
    in
    match last 0 (-1) with
    | -1 -> Some (body, "*")
    | i -> Some (String.sub body 0 i, String.sub body (i + 1) (n - i - 1))

let is_star rg =
  let rg = String.trim rg in
  rg = "*" || rg = ""

let dep_of ~dev ~optional (key, spec) : dep option =
  match spec with
  | `String spec -> (
      match split_alias spec with
      | Some (target, rg) ->
          if unresolvable rg then (
            reject ();
            None)
          else
            Some
              {
                d_dir = key;
                d_target = target;
                d_range = Npm_version.parse_range rg;
                d_dev = dev;
                d_optional = optional;
                d_star = is_star rg;
              }
      | None ->
          if unresolvable spec then (
            reject ();
            None)
          else
            Some
              {
                d_dir = key;
                d_target = key;
                d_range = Npm_version.parse_range spec;
                d_dev = dev;
                d_optional = optional;
                d_star = is_star spec;
              })
  | _ ->
      reject ();
      None

let peer_of (meta : (string * Yojson.Safe.t) list) (key, spec) : peer option =
  match spec with
  | `String spec ->
      let optional =
        match List.assoc_opt key meta with
        | Some m -> (
            match member "optional" m with `Bool b -> b | _ -> false)
        | None -> false
      in
      if unresolvable spec then (
        reject ();
        None)
      else
        Some
          {
            p_name = key;
            p_range = Npm_version.parse_range spec;
            p_optional = optional;
            p_star = is_star spec;
          }
  | _ ->
      reject ();
      None

(* ---- manifests ---- *)

(* npm reads overrides from the root project's package.json; only the
   flat "name": "range" form is a static override, so a nested object -- which
   is indexed by the parent chain -- is counted and dropped.  A value of *
   overrides nothing: an edge takes its range from an override only when
   the value is not * (arborist edge.js, spec), and OverrideSet reads an
   empty value as *. *)
let overrides_of (j : Yojson.Safe.t) : (string * Npm_version.range) list =
  List.filter_map
    (fun (k, v) ->
      match v with
      | `String ("*" | "") -> None
      | `String rg when not (unresolvable rg) ->
          Some (k, Npm_version.parse_range rg)
      | _ ->
          reject ();
          None)
    (assoc_of (member "overrides" j))

(* npm-pick-manifest tests !mani.deprecated, so the field deprecates only
   when JavaScript reads it as true: an empty message deprecates nothing *)
let is_deprecated = function
  | `Null | `Bool false | `String "" | `Int 0 -> false
  | _ -> true

(* checkEngine reads eng.node and eng.npm and ignores everything else in
   the object, so a sub-key such as "yarn" is not a requirement at all *)
let engine_of (j : Yojson.Safe.t) (k : string) : Npm_version.range option =
  match member k (member "engines" j) with
  | `String rg -> Some (Npm_version.parse_range rg)
  | _ -> None

let ver_of ~(root : bool) (vers : string) (j : Yojson.Safe.t) : ver option =
  match j with
  | `Assoc _ ->
      let deps_of ~dev ~optional field =
        List.filter_map (dep_of ~dev ~optional) (assoc_of (member field j))
      in
      let meta = assoc_of (member "peerDependenciesMeta" j) in
      (* arborist keeps one edge per name and loads peers first, so a
         dependency of the same name replaces the peer (node.js,
         _loadDeps), whether or not this parser can read its spec *)
      let dep_keys =
        List.concat_map
          (fun f -> List.map fst (assoc_of (member f j)))
          ([ "dependencies"; "optionalDependencies" ]
          @ if root then [ "devDependencies" ] else [])
      in
      let peers =
        List.filter_map (peer_of meta)
          (List.filter
             (fun (k, _) -> not (List.mem k dep_keys))
             (assoc_of (member "peerDependencies" j)))
      in
      let opts = deps_of ~dev:false ~optional:true "optionalDependencies" in
      optional_count := !optional_count + List.length opts;
      let optKeys = List.map (fun d -> d.d_dir) opts in
      let dep = is_deprecated (member "deprecated" j) in
      if dep then incr deprecated_count;
      Some
        {
          v_name = (match member "name" j with `String n -> n | _ -> "");
          v_vers = vers;
          v_deps =
            (* an optionalDependencies entry overrides a dependencies
               entry of the same name, so the plain dependency goes and the
               optional one stands *)
            opts
            @ List.filter
                (fun d -> not (List.mem d.d_dir optKeys))
                (deps_of ~dev:false ~optional:false "dependencies"
                @
                if root then deps_of ~dev:true ~optional:false "devDependencies"
                else []);
          v_peers = peers;
          v_ovr = (if root then overrides_of j else []);
          v_deprecated = dep;
          v_eng_node = engine_of j "node";
          v_eng_npm = engine_of j "npm";
        }
  | _ ->
      reject ();
      None

let of_json ~(root : bool) (j : Yojson.Safe.t) : packument =
  let name = match member "name" j with `String n -> n | _ -> "" in
  let latest =
    match member "latest" (member "dist-tags" j) with
    | `String v -> Some v
    | _ -> None
  in
  let tags =
    List.filter_map
      (function t, `String v -> Some (t, v) | _ -> None)
      (assoc_of (member "dist-tags" j))
  in
  let vers =
    List.filter_map
      (fun (v, m) -> ver_of ~root v m)
      (assoc_of (member "versions" j))
  in
  { pk_name = name; pk_latest = latest; pk_tags = tags; pk_vers = vers }

let load ~(root : bool) (path : string) : packument option =
  match Yojson.Safe.from_file path with
  | exception _ ->
      reject ();
      None
  | j -> Some (of_json ~root j)

(* ---- the query ----

   The query is the root package r_N: a project's package.json with the
   arguments of `npm install` added to it.  An argument is read as
   npm-package-arg 13.0.2 (npm 11.17.0) reads it, lib/npa.js, and only its
   registry forms are accepted: name, name@version, name@range, name@tag
   and key@npm:name@range.  Anything npa reads as a file, directory, URL or
   git spec is refused rather than dropped, because a query missing one of
   its arguments asks a different question. *)

(* /^(?:git[+])?[a-z]+:/i *)
let is_url s =
  let s = String.lowercase_ascii s in
  let s = if starts "git+" s then String.sub s 4 (String.length s - 4) else s in
  let n = String.length s in
  let rec go i =
    i < n && if s.[i] = ':' then i > 0 else s.[i] >= 'a' && s.[i] <= 'z' && go (i + 1)
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
      | Some j ->
          let host = String.sub rest 0 j in
          j + 1 < String.length rest
          && (match String.index_opt host '.' with Some k -> k > 0 && k + 1 < j | None -> false)
      | None -> false)
  | _ -> false

(* an argument npa would read as a local path, which the query takes for
   the project's package.json *)
let is_manifest_arg s = (not (is_url s)) && (not (is_git s)) && is_path s

(* encodeURIComponent(s) === s *)
let uri_safe =
  String.for_all (fun c ->
      (c >= 'a' && c <= 'z')
      || (c >= 'A' && c <= 'Z')
      || (c >= '0' && c <= '9')
      || String.contains "-_.!~*'()" c)

(* validate-npm-package-name's validForOldPackages, less its blocklist of
   core-module names *)
let name_ok n =
  n <> ""
  && String.length n <= 214
  && (not (starts "." n))
  && (not (starts "_" n))
  && (uri_safe n
     ||
     match String.index_opt n '/' with
     | Some i when starts "@" n ->
         i > 1
         && uri_safe (String.sub n 1 (i - 1))
         && uri_safe (String.sub n (i + 1) (String.length n - i - 1))
     | _ -> false)

(* The key and the raw spec: the name ends at the first @ past a scope's
   own, and a bare name or a trailing @ asks for *.  Whether a registry
   spec is a range or a tag is left to the driver, which has the
   packument's dist-tags. *)
let spec_of (arg : string) : (string * string) option =
  let n = String.length arg in
  let at = if n > 1 then String.index_from_opt arg 1 '@' else None in
  let name_part = match at with Some i -> String.sub arg 0 i | None -> arg in
  let raw =
    match at with
    | Some i -> ( match String.sub arg (i + 1) (n - i - 1) with "" -> "*" | s -> s)
    | None -> "*"
  in
  if is_url arg || is_git arg || is_path name_part || not (name_ok name_part) then None
  else if starts "npm:" (String.lowercase_ascii raw) then
    (* fromAlias: the target is read again, and must be a named registry
       spec and not itself an alias *)
    match split_alias ("npm:" ^ String.sub raw 4 (String.length raw - 4)) with
    | Some (t, rg)
      when name_ok t
           && (not (starts "npm:" (String.lowercase_ascii rg)))
           && not (unresolvable rg) ->
        Some (name_part, raw)
    | _ -> None
  else if is_url raw || is_path raw || has_sub raw "/" then None
  else Some (name_part, raw)

(* arborist's addRmPkgDeps.add, lib/add-rm-pkg-deps.js, for a request with
   no --save-* flag: the entry goes to the first field that already names
   it, in inferSaveType's order, else to dependencies, and replaces what is
   there unless it is *.  The fields a save type cannot coexist with lose
   the name, and an optional entry is mirrored into dependencies. *)
let add_to (pkg : Yojson.Safe.t) ((name, raw) : string * string) : Yojson.Safe.t =
  let has f = List.mem_assoc name (assoc_of (member f pkg)) in
  let target =
    List.find_opt has
      [ "devDependencies"; "optionalDependencies"; "dependencies"; "peerDependencies" ]
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
    if List.mem "peerDependencies" drop then "peerDependenciesMeta" :: drop else drop
  in
  (* a JavaScript object keeps a new key last *)
  let set k v l =
    if List.mem_assoc k l then List.map (fun (k', x) -> if k' = k then (k, v) else (k', x)) l
    else l @ [ (k, v) ]
  in
  let fields =
    List.map
      (fun (k, v) ->
        if List.mem k drop then (k, `Assoc (List.remove_assoc name (assoc_of v))) else (k, v))
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
