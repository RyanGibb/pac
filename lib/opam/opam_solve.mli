type archive = {
  root : string;
  pkgs : (string, (string * Opam_parse.pkg_meta) list) Hashtbl.t;
  class_table : (string, (string * string) list) Hashtbl.t;
  avoid_table : (string, string list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_dropped : int;
  mutable t_parse : float;
}

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
