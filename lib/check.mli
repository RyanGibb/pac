exception Failed of string

(* [pp_version] is handed the version's name, which the drivers' printers
   tag a version by; [elements] lists a dependee's version set. *)
val fail :
  pp_name:(Format.formatter -> 'name -> unit) ->
  pp_version:('name -> Format.formatter -> 'version -> unit) ->
  elements:('vset -> 'version list) ->
  ('name * 'version, 'name * 'vset) Pac.checkFailure ->
  'a
