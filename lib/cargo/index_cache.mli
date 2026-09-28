(* A crate's index file as the parser reads it: its versions, with [reject]
   called once per line dropped, and whether they came from the cache in
   [cache] rather than from the parser.  A name the index has no file for
   has no versions. *)
val load :
  cache:string option ->
  reject:(unit -> unit) ->
  index:string ->
  string ->
  Cargo_parse.ver list * bool
