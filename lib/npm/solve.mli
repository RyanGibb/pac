type result = {
  installs : ((string * string) * string) list;
  tree : (((string * string) * string) * ((string * string) * string)) list;
  nodes : int;
  lookups : int;
  (* distinct (dependee name, range) pairs the optional-dependency test
     read, and how many of them no published version matches *)
  optional_read : int;
  optional_dropped : int;
}

val solve :
  ?debug:bool ->
  ?order:Pac_common.Order.t ->
  ?omit_dev:bool ->
  ?omit_optional:bool ->
  Archive.t ->
  string * string ->
  (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit)
