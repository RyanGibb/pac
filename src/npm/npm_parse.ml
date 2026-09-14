(* Trusted (TCB) ingestion of a registry packument: the JSON document at
   https://registry.npmjs.org/<name>, whose "versions" object maps each
   published version to its package.json manifest.

   What is trusted here, beyond the plumbing:

   - The registry itself.  A packument is taken at face value; nothing is
     checked against the tarball it describes.
   - Range *parsing* (npm_version.ml).  Evaluation is not trusted: a row
     carries the parsed comparator sets into the calculus, which decides
     which real versions they admit.
   - The dependency-spec classification below.  npm accepts git, file,
     link, workspace and tag specs that no registry lookup can resolve;
     those rows are dropped and counted rather than guessed at.
   - The engines encoding.  A semver constant is compared inside the
     calculus by the platform valuation's ordering, which is plain string
     order, so numeric components are zero-padded here to make string
     order agree with version order.  Prerelease tags in an engines range
     are dropped.

   Not modelled, and counted where it matters: optionalDependencies
   (use-if-present is a post-resolution decision, not a constraint),
   bundledDependencies (placement), and "deprecated" (npm warns and
   installs anyway).  npm marks an optional dependency by listing the
   same key in both tables, so the optional keys are removed from the
   dependency rows rather than left standing as ordinary ones: keeping
   them would make optional what the calculus reads as mandatory, which
   is the opposite of imposing nothing. *)

type gate =
  | GTrue
  | GFalse
  | GCmp of Npm_version.op * string * string
  | GAnd of gate * gate
  | GOr of gate * gate
  | GNot of gate

type dep = {
  d_dir : string; (* the directory key, i.e. the manifest key *)
  d_target : string; (* the registry package, differing under npm: *)
  d_range : Npm_version.range;
  d_dev : bool;
}

type peer = { p_name : string; p_range : Npm_version.range; p_optional : bool }

type ver = {
  v_name : string;
  v_vers : string;
  v_deps : dep list;
  v_peers : peer list;
  v_gates : gate list;
  v_ovr : (string * Npm_version.range) list;
  v_deprecated : bool;
}

type packument = {
  pk_name : string;
  pk_latest : string option;
  pk_vers : ver list;
}

let rejected = ref 0
let skipped_optional = ref 0
let deprecated_count = ref 0
let reject () = incr rejected

(* Yojson's [member] raises on a non-object; a registry manifest may omit
   any field or give it the wrong shape, so lookups go through this. *)
let member (k : string) (j : Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc l -> ( match List.assoc_opt k l with Some v -> v | None -> `Null)
  | _ -> `Null

let assoc_of j = match j with `Assoc l -> l | _ -> []

let str_list j =
  match j with
  | `List l -> List.filter_map (function `String s -> Some s | _ -> None) l
  | `String s -> [ s ]
  | _ -> []

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

let dep_of ~dev (key, spec) : dep option =
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
          }
  | _ ->
      reject ();
      None

(* ---- platform gates ---- *)

(* the calculus compares a gate's constant with the valuation's ordering,
   which is plain string order, so a version constant is padded until
   string order and version order agree *)
let pad (v : string) : string =
  let p = Npm_version.parse v in
  Printf.sprintf "%05d.%05d.%05d" p.Npm_version.major p.Npm_version.minor
    p.Npm_version.patch

let gate_of_comparator (x : string) (ct : Npm_version.comparator) : gate =
  match ct with
  | Npm_version.Any -> GTrue
  | Npm_version.Cmp (o, c) -> GCmp (o, x, pad c)

let conj = List.fold_left (fun a b -> GAnd (a, b)) GTrue

let disj = function
  | [] -> GFalse
  | g :: gs -> List.fold_left (fun a b -> GOr (a, b)) g gs

let gate_of_range (x : string) (rg : Npm_version.range) : gate =
  disj (List.map (fun cs -> conj (List.map (gate_of_comparator x) cs)) rg)

(* os and cpu are lists whose positives are alternatives and whose
   !-prefixed entries are exclusions *)
let gate_of_list (x : string) (l : string list) : gate option =
  (* "any" is the wildcard, not a platform name: a list that is exactly
     ["any"] declares no restriction at all *)
  if l = [] || l = [ "any" ] then None
  else
    let neg, pos = List.partition (fun s -> starts "!" s) l in
    let neg =
      List.map
        (fun s ->
          GNot (GCmp (Npm_version.Eq, x, String.sub s 1 (String.length s - 1))))
        neg
    in
    let pos =
      match pos with
      | [] -> []
      | _ -> [ disj (List.map (fun s -> GCmp (Npm_version.Eq, x, s)) pos) ]
    in
    match pos @ neg with [] -> None | g :: gs -> Some (conj (g :: gs))

let gates_of (j : Yojson.Safe.t) : gate list =
  (* npm enforces only node and npm from engines; iojs, yarn, pnpm, bun,
     vscode and friends are informational, and treating an unknown key as
     a veto would cut every version of a package that carries one. *)
  let eng =
    List.filter_map
      (fun (k, v) ->
        match v with
        | `String rg when List.mem k [ "node"; "npm" ] && not (unresolvable rg)
          ->
            Some (gate_of_range k (Npm_version.parse_range rg))
        | _ -> None)
      (assoc_of (member "engines" j))
  in
  let plat =
    List.filter_map
      (fun (x, l) -> gate_of_list x (str_list (member l j)))
      [ ("os", "os"); ("cpu", "cpu"); ("libc", "libc") ]
  in
  eng @ plat

(* ---- manifests ---- *)

(* npm reads overrides from the root project's package.json; only the
   flat "name": "range" form is a static row, so a nested object -- which
   is indexed by the parent chain -- is counted and dropped. *)
let overrides_of (j : Yojson.Safe.t) : (string * Npm_version.range) list =
  List.filter_map
    (fun (k, v) ->
      match v with
      | `String rg when not (unresolvable rg) ->
          Some (k, Npm_version.parse_range rg)
      | _ ->
          reject ();
          None)
    (assoc_of (member "overrides" j))

let is_deprecated = function `Null -> false | `Bool b -> b | _ -> true

let ver_of ~(root : bool) (vers : string) (j : Yojson.Safe.t) : ver option =
  match j with
  | `Assoc _ ->
      let deps_of ~dev field =
        List.filter_map (dep_of ~dev) (assoc_of (member field j))
      in
      let meta = assoc_of (member "peerDependenciesMeta" j) in
      let peers =
        List.filter_map (peer_of meta) (assoc_of (member "peerDependencies" j))
      in
      let optKeys = List.map fst (assoc_of (member "optionalDependencies" j)) in
      let opt = List.length optKeys in
      if opt > 0 then skipped_optional := !skipped_optional + opt;
      let dep = is_deprecated (member "deprecated" j) in
      if dep then incr deprecated_count;
      Some
        {
          v_name = (match member "name" j with `String n -> n | _ -> "");
          v_vers = vers;
          v_deps =
            List.filter
              (fun d -> not (List.mem d.d_dir optKeys))
              (deps_of ~dev:false "dependencies"
              @ if root then deps_of ~dev:true "devDependencies" else []);
          v_peers = peers;
          v_gates = gates_of j;
          v_ovr = (if root then overrides_of j else []);
          v_deprecated = dep;
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
  let vers =
    List.filter_map
      (fun (v, m) -> ver_of ~root v m)
      (assoc_of (member "versions" j))
  in
  { pk_name = name; pk_latest = latest; pk_vers = vers }

let load ~(root : bool) (path : string) : packument option =
  match Yojson.Safe.from_file path with
  | exception _ ->
      reject ();
      None
  | j -> Some (of_json ~root j)
