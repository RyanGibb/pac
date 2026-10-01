type ('name, 'version) failure =
  | Subset of ('name * 'version)
  | Version_unique of ('name * 'version)
  | Root_mem of ('name * 'version list)
  | Dep_closure of ('name * 'version) * ('name * 'version list)
  | Reached of ('name * 'version)

exception Failed of string

(* [pp_version] is handed the version's name, which the drivers' printers
   tag a version by. *)
val fail :
  pp_name:(Format.formatter -> 'name -> unit) ->
  pp_version:('name -> Format.formatter -> 'version -> unit) ->
  ('name, 'version) failure ->
  'a
