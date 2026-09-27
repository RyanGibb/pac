(* Only a 404 says the registry has no such name; anything else leaves the
   name's versions unknown, and reading them as none would change the
   answer without saying so. *)
exception Fetch_failed of string

type t = {
  cache : string;
  offline : bool;
  reading : Npm_parse.reading;
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
  pkgs : (string, Npm_parse.ver list) Hashtbl.t;
  latest : (string, string) Hashtbl.t;
  tags : (string, (string * string) list) Hashtbl.t;
  entry : (string * string, Npm_parse.ver) Hashtbl.t;
  (* peer dependencies keyed by the directory they name *)
  peer_by_name : (string, (string * string) * Npm_parse.peer) Hashtbl.t;
  (* dependencies keyed by the key they introduce, for the granular
     version lookup's key test *)
  dep_by_key : (string * string, (string * string) * Npm_parse.dep) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_fetched : int;
  mutable n_dropped : int;
  (* wall time fetching and parsing packuments, which the solve
     interleaves with *)
  mutable t_parse : float;
}

val create :
  ?node:string ->
  ?npm:string ->
  ?reading:Npm_parse.reading ->
  cache:string ->
  offline:bool ->
  unit ->
  t

val reject : t -> unit -> unit
val shared : t -> bool

(* npm-pick-manifest's sort keys above semver order (index.js:167-181),
   greater for the version it prefers *)
val ver_rank : t -> Npm_parse.ver -> bool * bool * bool

(* Prerelease versions stay in: the calculus admits one only inside a
   comparator set that names a prerelease at the same release core. *)
val versions_of : t -> string -> string list

(* the version a dist-tag names, which arborist's #add reads through
   npm-pick-manifest (index.js, `wanted && type === 'tag'`): the tagged
   version exactly, whatever its engines or deprecation *)
val dist_tag : t -> string -> string -> string option
val latest : t -> string -> string option

(* The query is published nowhere, so it enters the archive as the only
   version of its name; a registry package of that name is then out of
   reach, as it would be had it been the root. *)
val add_root : t -> Npm_parse.ver -> string * string
val meta : t -> string * string -> Npm_parse.ver option
val engine_ok : t -> string * string -> bool
val deprecated : t -> string * string -> bool
