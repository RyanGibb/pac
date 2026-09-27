module SS : Set.S with type elt = string

type crate = string * string

(* build_requirements (dep_cache.rs): the features a request turns on, and
   what it asks of each dependency, by alias.  A strong a/f over an
   optional a turning on the feature a is already an entry of the table
   (Cargo_parse.with_implicit_features). *)
val requirements :
  Cargo_parse.ver -> all:bool -> SS.t -> bool -> SS.t * (string, SS.t) Hashtbl.t

(* resolve_features: the dependencies a request enables, each with the
   features it asks of its target *)
val enabled :
  root:bool ->
  Cargo_parse.ver ->
  (string, SS.t) Hashtbl.t ->
  (Cargo_parse.dep * SS.t) list

type 'name step = Decide of 'name | Activated of crate | Skip

module type DRIVER = sig
  type name
  type version
  type selection
  type assigned = name -> selection

  val equal : name -> name -> bool
  val decided : assigned -> name -> version option
  val version_equal : version -> version -> bool
  val root : crate
  val root_features : Cargo_query.features
  val meta : crate -> Cargo_parse.ver option
  val candidates : Cargo_parse.dep -> int
  val root_step : assigned -> name option
  val dep_step : assigned -> crate -> Cargo_parse.dep -> name step
  val choose : assigned:assigned -> name -> version list -> version
end

module Make (D : DRIVER) : sig
  val hooks : (unit, D.name, D.selection, D.version) Pac_common.Order.driver
end
