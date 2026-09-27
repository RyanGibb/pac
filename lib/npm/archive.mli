(* Only a 404 says the registry has no such name; anything else leaves the
   name's versions unknown, and reading them as none would change the
   answer without saying so. *)
exception Fetch_failed of string

type t

(* [parse] is the wall time fetching and parsing packuments, which the
   solve interleaves with *)
type stats = {
  names : int;
  versions : int;
  fetched : int;
  dropped : int;
  parse : float;
}

val stats : t -> stats
val cache_dir : t -> string
val offline : t -> bool
val reading : t -> Npm_parse.reading

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

(* the latest tag of a name already loaded, loading nothing *)
val loaded_latest : t -> string -> string option

(* the peer dependencies naming a directory, the latest added first, with
   the package declaring each *)
val peers_naming : t -> string -> ((string * string) * Npm_parse.peer) list
val peer_naming : t -> string -> ((string * string) * Npm_parse.peer) option

(* the dependencies written under a directory, the latest added first,
   with the package declaring each *)
val deps_at : t -> string -> ((string * string) * Npm_parse.dep) list
val engine_ok : t -> string * string -> bool
val deprecated : t -> string * string -> bool
