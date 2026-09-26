module P = Npm_parse

(* Only a 404 says the registry has no such name; anything else leaves the
   name's versions unknown, and reading them as none would change the
   answer without saying so. *)
exception Fetch_failed of string

(* semver takes a leading v or = on the version it tests, which is the
   shape `node --version` prints; our comparator parses digits only. *)
let host_version (s : string) : string =
  if s <> "" && (s.[0] = 'v' || s.[0] = 'V' || s.[0] = '=') then
    String.sub s 1 (String.length s - 1)
  else s

type t = {
  cache : string;
  offline : bool;
  (* The host npm-pick-manifest ranks engines against.  npm always has
     one, arborist passing process.version as nodeVersion and the CLI its
     own version as npmVersion, but nothing here can read a node that need
     not be installed, so an unset half leaves that sub-key untested
     exactly as checkEngine does for a null version: every candidate then
     passes and the engine keys tie, leaving deprecated and semver to
     decide.  A correspondence harness has to supply both, or the two
     sides rank by different rules. *)
  node : string option;
  npm : string option;
  pkgs : (string, P.ver list) Hashtbl.t;
  latest : (string, string) Hashtbl.t;
  tags : (string, (string * string) list) Hashtbl.t;
  entry : (string * string, P.ver) Hashtbl.t;
  (* peer dependencies keyed by the directory they name *)
  peer_by_name : (string, (string * string) * P.peer) Hashtbl.t;
  (* dependencies keyed by the key they introduce, for the granular
     version lookup's key test *)
  dep_by_key : (string * string, (string * string) * P.dep) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_fetched : int;
  mutable n_dropped : int;
  (* wall time fetching and parsing packuments, which the solve
     interleaves with *)
  mutable t_parse : float;
}

let create ?node ?npm ~cache ~offline () =
  {
    cache;
    offline;
    node = Option.map host_version node;
    npm = Option.map host_version npm;
    pkgs = Hashtbl.create 1024;
    latest = Hashtbl.create 1024;
    tags = Hashtbl.create 1024;
    entry = Hashtbl.create 16384;
    peer_by_name = Hashtbl.create 4096;
    dep_by_key = Hashtbl.create 16384;
    n_names = 0;
    n_vers = 0;
    n_fetched = 0;
    n_dropped = 0;
    t_parse = 0.;
  }

(* npm has no bulk index, so a packument is fetched per name and cached;
   a cached file is reused, which is what makes runs repeatable and lets
   the tests run with no network at all. *)
let escape (n : string) : string =
  String.concat "%2F" (String.split_on_char '/' n)

let cache_file ar n = Filename.concat ar.cache (escape n ^ ".json")

let rec mkdir_p d =
  if d <> "" && d <> "/" && d <> "." && not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Sys.mkdir d 0o755 with Sys_error _ -> ()
  end

let remove f = try Sys.remove f with Sys_error _ -> ()

let slurp f =
  match In_channel.with_open_bin f In_channel.input_all with
  | s -> String.trim s
  | exception Sys_error _ -> ""

(* curl -f exits 22 on every HTTP error status, so the status itself tells
   a name the registry lacks, which is normal -- the registry is full of
   manifests naming packages that were never published -- from a registry
   that failed to answer. *)
let curl ~url ~out =
  let code = out ^ ".code" and err = out ^ ".err" in
  let q = Filename.quote in
  let rc =
    Sys.command
      (Printf.sprintf "curl -fsSL -w '%%{http_code}' -o %s %s > %s 2> %s"
         (q out) (q url) (q code) (q err))
  in
  let status = slurp code and msg = slurp err in
  remove code;
  remove err;
  match (rc, status) with
  | 0, _ -> `Fetched
  | 22, "404" -> `Absent
  | _ ->
      `Failed
        (Printf.sprintf "curl exited %d%s%s" rc
           (if status = "" then "" else ", HTTP " ^ status)
           (if msg = "" then "" else ": " ^ msg))

let download ar n f =
  mkdir_p ar.cache;
  (* one scratch file per process: processes sharing a cache fetch the
     same name at once, and a shared one is renamed away under the other;
     the rename stays within the directory, so it is atomic *)
  let tmp = Printf.sprintf "%s.%d.tmp" f (Unix.getpid ()) in
  let url = "https://registry.npmjs.org/" ^ escape n in
  ar.n_fetched <- ar.n_fetched + 1;
  match curl ~url ~out:tmp with
  | `Fetched -> (
      (* a body that is no packument would be read back from the cache on
         every later run *)
      match P.load ~reject:ignore tmp with
      | Ok _ ->
          Sys.rename tmp f;
          Some f
      | Error e ->
          remove tmp;
          raise (Fetch_failed (Printf.sprintf "fetching %s: %s" url e)))
  | `Absent ->
      remove tmp;
      None
  | `Failed e ->
      remove tmp;
      raise (Fetch_failed (Printf.sprintf "fetching %s: %s" url e))

let reject ar () = ar.n_dropped <- ar.n_dropped + 1

let fetch ar (n : string) : string option =
  let f = cache_file ar n in
  if Sys.file_exists f then Some f
  else if ar.offline then None
  else download ar n f

let tabulate ar (v : P.ver) =
  let p = (v.P.v_name, v.P.v_vers) in
  Hashtbl.replace ar.entry p v;
  List.iter (fun r -> Hashtbl.add ar.peer_by_name r.P.p_name (p, r)) v.P.v_peers;
  List.iter
    (fun d -> Hashtbl.add ar.dep_by_key (d.P.d_dir, d.P.d_target) (p, d))
    v.P.v_deps

let add_name ar n vs =
  Hashtbl.replace ar.pkgs n vs;
  ar.n_names <- ar.n_names + 1;
  ar.n_vers <- ar.n_vers + List.length vs;
  List.iter (tabulate ar) vs

let read_packument ar n f =
  match P.load ~reject:(reject ar) f with
  | Error e -> raise (Fetch_failed (Printf.sprintf "reading %s: %s" f e))
  | Ok pk ->
      Option.iter (Hashtbl.replace ar.latest n) pk.P.pk_latest;
      Hashtbl.replace ar.tags n pk.P.pk_tags;
      (* the name fetched under is authoritative: a manifest's own "name"
         is overwritten, not checked *)
      List.map (fun v -> { v with P.v_name = n }) pk.P.pk_vers

(* There is no cone pass: the transitive closure over every version of
   every dependency is most of the registry, so a packument is fetched
   only when a sub-instance actually reads that name.  That is sound
   because a name only ever reaches one through a declaration of a
   package already loaded -- an exit edge names the key its own
   intermediate carries, and a peer edge names a directory its own
   declarer asked for. *)
let load_name ar (n : string) : P.ver list =
  match Hashtbl.find_opt ar.pkgs n with
  | Some vs -> vs
  | None ->
      let t = Unix.gettimeofday () in
      let vs =
        match fetch ar n with None -> [] | Some f -> read_packument ar n f
      in
      add_name ar n vs;
      ar.t_parse <- ar.t_parse +. (Unix.gettimeofday () -. t);
      vs

(* Prerelease versions stay in: the calculus admits one only inside a
   comparator set that names a prerelease at the same release core. *)
let versions_of ar n = List.map (fun (v : P.ver) -> v.P.v_vers) (load_name ar n)

(* the version a dist-tag names, which arborist's #add reads through
   npm-pick-manifest (index.js, `wanted && type === 'tag'`): the tagged
   version exactly, whatever its engines or deprecation *)
let dist_tag ar (n : string) (tag : string) : string option =
  ignore (load_name ar n);
  Option.bind (Hashtbl.find_opt ar.tags n) (List.assoc_opt tag)

let latest ar n =
  ignore (load_name ar n);
  Hashtbl.find_opt ar.latest n

(* The query is published nowhere, so it enters the archive as the only
   version of its name; a registry package of that name is then out of
   reach, as it would be had it been the root. *)
let add_root ar (v : P.ver) : string * string =
  add_name ar v.P.v_name [ v ];
  (v.P.v_name, v.P.v_vers)

let meta ar p : P.ver option = Hashtbl.find_opt ar.entry p

(* checkEngine, npm-install-checks/lib/index.js: engines.node and
   engines.npm are the two sub-keys it tests, and a null host version
   passes its own sub-key rather than failing it, so a package declaring
   a requirement we have no host for is ranked as though it declared
   none. *)
let engine_ok ar (p : string * string) : bool =
  match meta ar p with
  | None -> true
  | Some v ->
      let ok host rg =
        match (host, rg) with
        | Some h, Some rg -> Npm_version.holds_pre h rg
        | _ -> true
      in
      ok ar.node v.P.v_eng_node && ok ar.npm v.P.v_eng_npm

let deprecated ar (p : string * string) : bool =
  match meta ar p with None -> false | Some v -> v.P.v_deprecated
