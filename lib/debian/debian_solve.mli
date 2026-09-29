type answer = {
  pkgs : (string * string * string) list;
  nodes : int;
  lookups : int;
}

type result = {
  answer : (answer, Pac_common.Report.explanation) Stdlib.result;
  core : unit -> unit;
  names : int;
  versions : int;
  dropped : int;
  (* whether the parsed index was read from the cache *)
  cached : bool;
  t_parse : float;
}

val solve_files :
  debug:bool ->
  order:Pac_common.Order.t ->
  recommends:bool ->
  strict_pinning:bool ->
  native:string ->
  cache:string option ->
  paths:string list ->
  query:string list ->
  (result, string) Stdlib.result
