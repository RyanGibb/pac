type spec = Range of Npm_version.range | Star | Tag of string

type dep = {
  d_dir : string;
  d_name : string;
  d_spec : spec;
  d_dev : bool;
  d_optional : bool;
  d_raw : string;
}

type peer = {
  p_name : string;
  p_dependee_name : string;
  p_spec : spec;
  p_optional : bool;
  p_root : bool;
}

type reading = [ `Npm | `Shared | `Placement ]

type ver = {
  v_name : string;
  v_vers : string;
  v_deps : dep list;
  v_peers : peer list;
  v_ovr : (string * Npm_version.range) list;
  v_deprecated : bool;
  v_eng_node : Npm_version.range option;
  v_eng_npm : Npm_version.range option;
}

type packument = {
  pk_latest : string option;
  pk_tags : (string * string) list;
  pk_vers : ver list;
}

let member (k : string) (j : Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc l -> ( match List.assoc_opt k l with Some v -> v | None -> `Null)
  | _ -> `Null

let assoc_of j = match j with `Assoc l -> l | _ -> []

let set k v l =
  if List.mem_assoc k l then
    List.map (fun (k', x) -> if k' = k then (k, v) else (k', x)) l
  else l @ [ (k, v) ]

let has_sub s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  m = 0 || go 0

let starts p s = String.starts_with ~prefix:p s
let is_alias s = starts "npm:" (String.lowercase_ascii s)

let unresolvable s =
  has_sub s "://" || starts "$" s || starts "git+" s || starts "git:" s
  || starts "file:" s || starts "link:" s || starts "workspace:" s
  || starts "portal:" s || starts "patch:" s
  || (has_sub s "/" && not (is_alias s))

let uri_safe =
  String.for_all (fun c ->
      (c >= 'a' && c <= 'z')
      || (c >= 'A' && c <= 'Z')
      || (c >= '0' && c <= '9')
      || String.contains "-_.!~*'()" c)

let is_star rg =
  let rg = String.trim rg in
  rg = "*" || rg = ""

let spec_of_string (s : string) : spec option =
  if is_star s then Some Star
  else
    match Npm_version.parse_range_opt s with
    | Some rg -> Some (Range rg)
    | None ->
        let t = String.trim s in
        if uri_safe t then Some (Tag t) else None

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
  let raw = match spec with `String s -> s | _ -> "" in
  let name, rg =
    match spec with
    | `String spec -> (
        match split_alias spec with
        | Some (name, rg) -> (name, Some rg)
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
          d_name = name;
          d_spec = sp;
          d_dev = dev;
          d_optional = optional;
          d_raw = raw;
        }
  | None ->
      reject ();
      None

(* A peer names a directory and the npm and shared readings read its range
   against the package of that name, so there an alias, which puts another
   package there, is dropped and counted like a spec no registry lookup
   resolves.  The placement reading keeps it, as a dependency's. *)
let peer_of ~reject ?(berry_only = []) ~aliases
    (meta : (string * Yojson.Safe.t) list) (key, spec) : peer option =
  let optional =
    match List.assoc_opt key meta with
    | Some m -> ( match member "optional" m with `Bool b -> b | _ -> false)
    | None -> false
  in
  let dependee_name, rg =
    match spec with
    | `String s when aliases -> (
        match split_alias s with
        | Some (n, rg) -> (n, Some rg)
        | None -> (key, Some s))
    | `String s when not (is_alias s) -> (key, Some s)
    | _ -> (key, None)
  in
  match
    Option.bind rg (fun rg ->
        if unresolvable rg then None else spec_of_string rg)
  with
  | Some sp ->
      Some
        {
          p_name = key;
          p_dependee_name = dependee_name;
          p_spec = sp;
          p_optional = optional;
          p_root = not (List.mem key berry_only);
        }
  | None ->
      reject ();
      None

(* Berry's normalizePackage (Configuration.ts:1915-2011), for the shared
   reading: the built-in packageExtensions matching the version add
   dependencies and peers the manifest lacks and set peer meta, and a
   peerDependenciesMeta name with no peer is a peer on *.  The optional
   peer on its @types package that Berry gives each other peer is left
   out: those peers are optional and on *, so they never make Berry reject
   an answer, and asking them would tie every @types copy to one version
   per holder (jest's @types/babel__core), which neither tool requires. *)
let extend (name : string) (vers : string) (j : Yojson.Safe.t) :
    Yojson.Safe.t * string list =
  let fields = assoc_of j in
  let get f = assoc_of (member f j) in
  let deps = ref (get "dependencies")
  and peers = ref (get "peerDependencies")
  and meta = ref (get "peerDependenciesMeta") in
  List.iter
    (fun (x : Berry_ext.t) ->
      if Berry_ext.matches vers x then begin
        List.iter
          (fun (k, v) ->
            if not (List.mem_assoc k !deps) then
              deps := !deps @ [ (k, `String v) ])
          x.Berry_ext.x_deps;
        List.iter
          (fun (k, v) ->
            if not (List.mem_assoc k !peers) then
              peers := !peers @ [ (k, `String v) ])
          x.Berry_ext.x_peers;
        List.iter
          (fun (k, o) ->
            meta :=
              List.remove_assoc k !meta
              @ [ (k, `Assoc [ ("optional", `Bool o) ]) ])
          x.Berry_ext.x_meta
      end)
    (Berry_ext.of_name name);
  List.iter
    (fun (k, _) ->
      if not (List.mem_assoc k !peers) then
        peers := !peers @ [ (k, `String "*") ])
    !meta;
  let own = get "peerDependencies" in
  ( `Assoc
      (fields
      |> set "dependencies" (`Assoc !deps)
      |> set "peerDependencies" (`Assoc !peers)
      |> set "peerDependenciesMeta" (`Assoc !meta)),
    List.filter_map
      (fun (k, _) -> if List.mem_assoc k own then None else Some k)
      !peers )

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

(* arborist loads dependencies, then optionalDependencies, then a root's
   devDependencies, and a later entry of a name replaces the earlier (Node
   _loadDeps) *)
let deps_of ~reject ~root (j : Yojson.Safe.t) : dep list =
  let read ~dev ~optional field =
    List.filter_map (dep_of ~reject ~dev ~optional) (assoc_of (member field j))
  in
  let without (l : dep list) =
    List.filter (fun d -> not (List.exists (fun e -> e.d_dir = d.d_dir) l))
  in
  let devs =
    if root then read ~dev:true ~optional:false "devDependencies" else []
  in
  let opts = read ~dev:false ~optional:true "optionalDependencies" in
  devs
  @ without devs
      (opts @ without opts (read ~dev:false ~optional:false "dependencies"))

(* The peers, or None where the shared reading leaves the version out *)
let peers_of ~shared ~aliases ~reject ~root ~berry_only (j : Yojson.Safe.t) :
    peer list option =
  let meta = assoc_of (member "peerDependenciesMeta" j) in
  (* arborist keeps one edge per name and loads peers first, so a
     dependency of the same name replaces the peer (node.js, _loadDeps),
     whether or not this parser can read its spec *)
  let dep_keys =
    List.concat_map
      (fun f -> List.map fst (assoc_of (member f j)))
      ([ "dependencies"; "optionalDependencies" ]
      @ if root then [ "devDependencies" ] else [])
  in
  (* Berry keeps a package's peer beside a dependency of its name (a peer
     with default); the root's it never asks of anyone *)
  let decls =
    List.filter
      (fun (k, _) -> (shared && not root) || not (List.mem k dep_keys))
      (assoc_of (member "peerDependencies" j))
  in
  let peers =
    List.filter_map (peer_of ~reject ~berry_only ~aliases meta) decls
  in
  (* under the shared reading a version with a peer this parser drops is
     left out, as no answer holding it is one both tools are known to
     accept: npm fails on a spec it cannot read (EINVALIDTAGNAME), which
     Berry reads as *, and an alias, a git, file or URL spec, or a value
     that is no string names nothing either reads off the registry *)
  if shared && (not root) && List.length peers < List.length decls then None
  else Some peers

let ver_of ~(reading : reading) ~reject ~(root : bool) (vers : string)
    (j : Yojson.Safe.t) : ver option =
  let shared = reading = `Shared in
  match j with
  | `Assoc _ -> (
      let j, berry_only =
        if shared && not root then
          match member "name" j with
          | `String n -> extend n vers j
          | _ -> (j, [])
        else (j, [])
      in
      match
        peers_of ~shared ~aliases:(reading = `Placement) ~reject ~root
          ~berry_only j
      with
      | None -> None
      | Some peers ->
          Some
            {
              v_name = (match member "name" j with `String n -> n | _ -> "");
              v_vers = vers;
              v_deps = deps_of ~reject ~root j;
              v_peers = peers;
              v_ovr = (if root then overrides_of ~reject j else []);
              v_deprecated = is_deprecated (member "deprecated" j);
              v_eng_node = engine_of j "node";
              v_eng_npm = engine_of j "npm";
            })
  | _ ->
      reject ();
      None

let of_json ~reading ~reject (j : Yojson.Safe.t) : packument =
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
      (fun (v, m) -> ver_of ~reading ~reject ~root:false v m)
      (assoc_of (member "versions" j))
  in
  { pk_latest = latest; pk_tags = tags; pk_vers = vers }

(* Most of a packument is what no reading uses (readmes, the time table,
   each version's dist and scripts), so it is checked in place against the
   grammar Yojson reads (read.mll: comments, NaN and Infinity, unquoted
   keys, a high surrogate escape only with its low one), and only what
   of_json and ver_of read of a registry version is built: Yojson's tree
   with every other member removed. *)
let fail () = raise (Yojson.Json_error "not JSON")
let digit c = c >= '0' && c <= '9'

let rec close s j =
  if j + 1 >= String.length s then fail ()
  else if s.[j] = '*' && s.[j + 1] = '/' then j + 2
  else close s (j + 1)

let rec space s i =
  let n = String.length s in
  if i >= n then i
  else
    match s.[i] with
    | ' ' | '\t' | '\r' | '\n' -> space s (i + 1)
    | '/' when i + 1 < n && s.[i + 1] = '/' -> (
        match String.index_from_opt s i '\n' with
        | Some j -> space s (j + 1)
        | None -> n)
    | '/' when i + 1 < n && s.[i + 1] = '*' -> space s (close s (i + 2))
    | _ -> i

let hex = function
  | '0' .. '9' as c -> Char.code c - 48
  | 'a' .. 'f' as c -> Char.code c - 87
  | 'A' .. 'F' as c -> Char.code c - 55
  | _ -> fail ()

let hex4 s i =
  if i + 4 > String.length s then fail ()
  else
    (hex s.[i] lsl 12)
    lor (hex s.[i + 1] lsl 8)
    lor (hex s.[i + 2] lsl 4)
    lor hex s.[i + 3]

(* the end of the string whose opening quote is at i - 1 *)
let rec str s i =
  if i >= String.length s then fail ()
  else
    match s.[i] with
    | '"' -> i + 1
    | '\\' -> str s (escape s (i + 1))
    | _ -> str s (i + 1)

and escape s i =
  let n = String.length s in
  if i >= n then fail ()
  else
    match s.[i] with
    | '"' | '\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' -> i + 1
    | 'u' ->
        let x = hex4 s (i + 1) in
        if x < 0xD800 || x > 0xDBFF then i + 5
        else if i + 6 < n && s.[i + 5] = '\\' && s.[i + 6] = 'u' then
          let y = hex4 s (i + 7) in
          if y >= 0xDC00 && y <= 0xDFFF then i + 11 else fail ()
        else fail ()
    | _ -> fail ()

let rec digits s j =
  if j < String.length s && digit s.[j] then digits s (j + 1) else j

let number s i =
  let n = String.length s in
  let i = if s.[i] = '-' then i + 1 else i in
  if i >= n || not (digit s.[i]) then fail ()
  else
    let j = if s.[i] = '0' then i + 1 else digits s (i + 1) in
    let j =
      if j + 1 < n && s.[j] = '.' && digit s.[j + 1] then digits s (j + 2)
      else j
    in
    if j < n && (s.[j] = 'e' || s.[j] = 'E') then
      let k =
        if j + 1 < n && (s.[j + 1] = '+' || s.[j + 1] = '-') then j + 2
        else j + 1
      in
      if k < n && digit s.[k] then digits s k else j
    else j

let rec ident s j =
  if
    j < String.length s
    &&
    match s.[j] with
    | 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9' -> true
    | _ -> false
  then ident s (j + 1)
  else j

let rec lit s i w j =
  j = String.length w
  || (i + j < String.length s && s.[i + j] = w.[j] && lit s i w (j + 1))

(* the members from the key at a: [f s a k j] takes the key at [a, k) and
   the value at j and returns the value's end *)
let rec member_at s f a =
  let n = String.length s in
  let k =
    if a >= n then fail ()
    else
      match s.[a] with
      | '"' -> str s (a + 1)
      | 'a' .. 'z' | 'A' .. 'Z' | '_' -> ident s (a + 1)
      | _ -> fail ()
  in
  let c = space s k in
  if c >= n || s.[c] <> ':' then fail ();
  let e = space s (f s a k (space s (c + 1))) in
  if e >= n then fail ()
  else
    match s.[e] with
    | ',' -> member_at s f (space s (e + 1))
    | '}' -> e + 1
    | _ -> fail ()

(* the object whose brace is at i - 1 *)
let members s i f =
  let i = space s i in
  if i < String.length s && s.[i] = '}' then i + 1 else member_at s f i

let rec skip s i =
  if i >= String.length s then fail ()
  else
    match s.[i] with
    | '"' -> str s (i + 1)
    | '{' -> members s (i + 1) skip_member
    | '[' ->
        let j = space s (i + 1) in
        if j < String.length s && s.[j] = ']' then j + 1 else elem s j
    | 't' when lit s i "true" 0 -> i + 4
    | 'f' when lit s i "false" 0 -> i + 5
    | 'n' when lit s i "null" 0 -> i + 4
    | 'N' when lit s i "NaN" 0 -> i + 3
    | 'I' when lit s i "Infinity" 0 -> i + 8
    | '-' when lit s i "-Infinity" 0 -> i + 9
    | '-' | '0' .. '9' -> number s i
    | _ -> fail ()

and skip_member s _ _ j = skip s j

and elem s j =
  let e = space s (skip s j) in
  if e >= String.length s then fail ()
  else
    match s.[e] with
    | ',' -> elem s (space s (e + 1))
    | ']' -> e + 1
    | _ -> fail ()

let rec plain s a k = a >= k || (s.[a] <> '\\' && plain s (a + 1) k)

let skim (s : string) : Yojson.Safe.t =
  let n = String.length s in
  let whole j =
    let e = skip s j in
    (e, Yojson.Safe.from_string (String.sub s j (e - j)))
  in
  let key a k =
    if s.[a] <> '"' then String.sub s a (k - a)
    else if not (plain s a k) then
      match Yojson.Safe.from_string (String.sub s a (k - a)) with
      | `String x -> x
      | _ -> fail ()
    else String.sub s (a + 1) (k - a - 2)
  in
  (* the members of an object that [keep] names a reader for, and anything
     but an object as `Null, which every reader takes as a non-object *)
  let fields keep j =
    if j < n && s.[j] = '{' then begin
      let acc = ref [] in
      let e =
        members s (j + 1) (fun s a k j ->
            let x = key a k in
            match keep x with
            | Some f ->
                let e, v = f j in
                acc := (x, v) :: !acc;
                e
            | None -> skip s j)
      in
      (e, `Assoc (List.rev !acc))
    end
    else (skip s j, `Null)
  in
  let version =
    fields (function
      | "name" | "dependencies" | "optionalDependencies" | "peerDependencies"
      | "peerDependenciesMeta" | "deprecated" | "engines" ->
          Some whole
      | _ -> None)
  in
  let versions = fields (fun _ -> Some version) in
  let e, j =
    fields
      (function
        | "dist-tags" -> Some whole | "versions" -> Some versions | _ -> None)
      (space s 0)
  in
  if space s e <> n then fail ();
  j

let load ~reading ~reject (path : string) : (packument, string) result =
  match In_channel.with_open_bin path In_channel.input_all with
  | exception Sys_error e -> Error e
  | s -> (
      match skim s with
      | `Assoc _ as j -> Ok (of_json ~reading ~reject j)
      | _ | (exception Yojson.Json_error _) -> Error "not a packument")
