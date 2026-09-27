type archive

type stats = Lookups.stats = {
  names : int;
  versions : int;
  dropped : int;
  parse : float;
}

val stats : archive -> stats
val empty_archive : string -> archive
val default_opam_version : string

val sanitize :
  archive ->
  (string * Opam_parse.vc) list ->
  ((string * Opam_parse.vc) list, string) Stdlib.result

type result = {
  reals : (string * string) list;
  nodes : int;
  lookups : int;
  depexts : string list;
}

val solve :
  ?debug:bool ->
  ?order:Pac_common.Order.t ->
  ?with_test:bool ->
  ?with_doc:bool ->
  ?with_dev_setup:bool ->
  ?opam_version:string ->
  archive ->
  (string * Opam_parse.vc) list ->
  (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit)
