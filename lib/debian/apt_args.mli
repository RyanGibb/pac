type accepts = Any | Only of string

val stanza_key : native:string -> Deb_packages.stanza -> string * string

val pin_candidates :
  native:string ->
  named:(string * string, string) Hashtbl.t ->
  Deb_packages.stanza list ->
  Deb_packages.stanza list

val fnmatch : string -> string -> bool
val version_matches : string -> string -> bool
val cache_names : Deb_packages.stanza list -> string -> bool

val query_element :
  native:string ->
  arches:string list ->
  located:(string -> bool) ->
  Deb_packages.stanza list ->
  string ->
  ((string * string) * accepts, string) result

val parse_query :
  native:string ->
  arches:string list ->
  Deb_packages.stanza list ->
  string list ->
  ( ((string * string) * accepts) list * (string * string, string) Hashtbl.t,
    string )
  result
