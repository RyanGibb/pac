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
   - The os/cpu/libc encoding.  Each list becomes a platform gate over
     the valuation's variable of that name; npm applies the same test at
     reify time (EBADPLATFORM).  "engines" is deliberately *not* a gate:
     npm never consults it when choosing versions, and --engine-strict
     only promotes the install-time warning to an error, so gating on it
     would make our instance strictly smaller than npm's.

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

   Not modelled, and counted where it matters: bundledDependencies
   (placement) and "deprecated" (npm warns and installs anyway). *)

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
  (* not carried into the calculus: it only tells the solver that this
     dependency may be abandoned when the registry cannot satisfy it *)
  d_optional : bool;
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

let conj = List.fold_left (fun a b -> GAnd (a, b)) GTrue

let disj = function
  | [] -> GFalse
  | g :: gs -> List.fold_left (fun a b -> GOr (a, b)) g gs

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

(* "engines" is not read: see the header.  os/cpu/libc are, because npm
   does refuse a package whose platform its host fails. *)
let gates_of (j : Yojson.Safe.t) : gate list =
  List.filter_map
    (fun (x, l) -> gate_of_list x (str_list (member l j)))
    [ ("os", "os"); ("cpu", "cpu"); ("libc", "libc") ]

(* ---- manifests ---- *)

(* npm reads overrides from the root project's package.json; only the
   flat "name": "range" form is a static override, so a nested object -- which
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
      let deps_of ~dev ~optional field =
        List.filter_map (dep_of ~dev ~optional) (assoc_of (member field j))
      in
      let meta = assoc_of (member "peerDependenciesMeta" j) in
      let peers =
        List.filter_map (peer_of meta) (assoc_of (member "peerDependencies" j))
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
