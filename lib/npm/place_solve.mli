(* the answer: each occupied location, as its key path, deepest key first,
   and the registry package there *)
type result = {
  layout : (string list * (string * string)) list;
  nodes : int;
  lookups : int;
}

val solve :
  ?debug:bool ->
  ?order:Pac_common.Order.t ->
  ?omit_dev:bool ->
  ?omit_optional:bool ->
  depth:int ->
  Archive.t ->
  string * string ->
  (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit)

(* a lock's packages key, then the package there *)
val print_layout : result -> string list
