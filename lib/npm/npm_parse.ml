(* How npa's fromRegistry reads a registry spec: a range where node-semver
   reads one, loosely, and otherwise a dist-tag, which only the target's
   packument resolves.  The literal "*", and the empty range npm reads as
   it, is npm's own case apart from every range meaning the same. *)
type spec = Range of Npm_version.range | Star | Tag of string

type dep = {
  d_dir : string; (* the directory key, i.e. the manifest key *)
  d_target : string; (* the registry package, differing under npm: *)
  d_spec : spec;
  d_dev : bool;
  (* not carried into the calculus: it only tells the solver that this
     dependency may be abandoned when the registry cannot satisfy it *)
  d_optional : bool;
}

type peer = { p_name : string; p_spec : spec; p_optional : bool }

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
  pk_latest : string option;
  pk_tags : (string * string) list;
  pk_vers : ver list;
}

(* Yojson's [member] raises on a non-object; a registry manifest may omit
   any field or give it the wrong shape, so lookups go through this. *)
let member (k : string) (j : Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc l -> ( match List.assoc_opt k l with Some v -> v | None -> `Null)
  | _ -> `Null

let assoc_of j = match j with `Assoc l -> l | _ -> []

let has_sub s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  m = 0 || go 0

let starts p s = String.starts_with ~prefix:p s

(* npa's isAliasSpec, which takes the prefix in any case *)
let is_alias s = starts "npm:" (String.lowercase_ascii s)

(* git, file and URL specs, and the link:, workspace:, portal: and patch:
   specs npa refuses, are dropped and counted rather than guessed at. *)
let unresolvable s =
  has_sub s "://" || starts "$" s || starts "git+" s || starts "git:" s
  || starts "file:" s || starts "link:" s || starts "workspace:" s
  || starts "portal:" s || starts "patch:" s
  || (has_sub s "/" && not (is_alias s))

(* encodeURIComponent(s) === s *)
let uri_safe =
  String.for_all (fun c ->
      (c >= 'a' && c <= 'z')
      || (c >= 'A' && c <= 'Z')
      || (c >= '0' && c <= '9')
      || String.contains "-_.!~*'()" c)

let is_star rg =
  let rg = String.trim rg in
  rg = "*" || rg = ""

(* a tag must be a name encodeURIComponent leaves alone, and npa refuses
   any other (EINVALIDTAGNAME) *)
let spec_of_string (s : string) : spec option =
  if is_star s then Some Star
  else
    match Npm_version.parse_range_opt s with
    | Some rg -> Some (Range rg)
    | None ->
        let t = String.trim s in
        if uri_safe t then Some (Tag t) else None

(* "npm:bar@^1" and "npm:@scope/bar@^1": npa splits at the first @ past
   the scope's; this takes the last, which differs only when the range
   itself holds an @ *)
let split_alias (s : string) : (string * string) option =
  if not (is_alias s) then None
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

let dep_of ~reject ~dev ~optional (key, spec) : dep option =
  let target, rg =
    match spec with
    | `String spec -> (
        match split_alias spec with
        | Some (target, rg) -> (target, Some rg)
        | None -> (key, Some spec))
    | _ -> (key, None)
  in
  match
    Option.bind rg (fun rg ->
        if unresolvable rg then None else spec_of_string rg)
  with
  | Some sp ->
      Some
        {
          d_dir = key;
          d_target = target;
          d_spec = sp;
          d_dev = dev;
          d_optional = optional;
        }
  | None ->
      reject ();
      None

(* A peer names a directory and the calculus reads its range against the
   package of that name, so an alias, which puts another package there, is
   dropped and counted like a spec no registry lookup resolves. *)
let peer_of ~reject (meta : (string * Yojson.Safe.t) list) (key, spec) :
    peer option =
  let optional =
    match List.assoc_opt key meta with
    | Some m -> ( match member "optional" m with `Bool b -> b | _ -> false)
    | None -> false
  in
  match spec with
  | `String spec when not (unresolvable spec || is_alias spec) -> (
      match spec_of_string spec with
      | Some sp -> Some { p_name = key; p_spec = sp; p_optional = optional }
      | None ->
          reject ();
          None)
  | _ ->
      reject ();
      None

(* npm reads overrides from the root project's package.json; only the
   flat "name": "range" form is a static override, so a nested object --
   which is keyed by the parent chain -- is counted and dropped, and so is
   a tag or an alias, which replaces the spec rather than the range.  A
   value of * overrides nothing: an edge takes its range from an override
   only when the value is not * (arborist edge.js, spec), and OverrideSet
   reads an empty value as *. *)
let overrides_of ~reject (j : Yojson.Safe.t) : (string * Npm_version.range) list
    =
  List.filter_map
    (fun (k, v) ->
      match v with
      | `String ("*" | "") -> None
      | `String rg when not (unresolvable rg || is_alias rg) -> (
          match spec_of_string rg with
          | Some (Range r) -> Some (k, r)
          | Some Star -> Some (k, [ [ Npm_version.Any ] ])
          | Some (Tag _) | None ->
              reject ();
              None)
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
  | `String rg -> Some (Npm_version.parse_range ~include_prerelease:true rg)
  | _ -> None

(* "os", "cpu" and "libc" are not read: npm-pick-manifest never consults
   them and npm tests them only once the tree is built
   (#checkEngineAndPlatform), so reading them would make our instance
   strictly smaller than npm's.  bundleDependencies entries stay ordinary
   registry dependencies although npm takes their versions from the
   tarball, which is neither fetched nor trusted here. *)
let ver_of ~reject ~(root : bool) (vers : string) (j : Yojson.Safe.t) :
    ver option =
  match j with
  | `Assoc _ ->
      let deps_of ~dev ~optional field =
        List.filter_map
          (dep_of ~reject ~dev ~optional)
          (assoc_of (member field j))
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
        List.filter_map (peer_of ~reject meta)
          (List.filter
             (fun (k, _) -> not (List.mem k dep_keys))
             (assoc_of (member "peerDependencies" j)))
      in
      let opts = deps_of ~dev:false ~optional:true "optionalDependencies" in
      let optKeys = List.map (fun d -> d.d_dir) opts in
      let dep = is_deprecated (member "deprecated" j) in
      Some
        {
          v_name = (match member "name" j with `String n -> n | _ -> "");
          v_vers = vers;
          v_deps =
            (* arborist loads dependencies, then optionalDependencies,
               then a root's devDependencies, and a later entry of a name
               replaces the earlier (Node _loadDeps) *)
            (let devs =
               if root then deps_of ~dev:true ~optional:false "devDependencies"
               else []
             in
             let devKeys = List.map (fun d -> d.d_dir) devs in
             devs
             @ List.filter
                 (fun d -> not (List.mem d.d_dir devKeys))
                 (opts
                 @ List.filter
                     (fun d -> not (List.mem d.d_dir optKeys))
                     (deps_of ~dev:false ~optional:false "dependencies")));
          v_peers = peers;
          v_ovr = (if root then overrides_of ~reject j else []);
          v_deprecated = dep;
          v_eng_node = engine_of j "node";
          v_eng_npm = engine_of j "npm";
        }
  | _ ->
      reject ();
      None

let of_json ~reject (j : Yojson.Safe.t) : packument =
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
      (fun (v, m) -> ver_of ~reject ~root:false v m)
      (assoc_of (member "versions" j))
  in
  { pk_latest = latest; pk_tags = tags; pk_vers = vers }

(* A packument that will not parse says nothing about the name's versions,
   so it is an error rather than a name with none. *)
let load ~reject (path : string) : (packument, string) result =
  match Yojson.Safe.from_file path with
  | exception Sys_error e -> Error e
  | `Assoc _ as j -> Ok (of_json ~reject j)
  | _ | (exception Yojson.Json_error _) -> Error "not a packument"
