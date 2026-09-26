(* Prints the core instance reachable from [roots]: every name the edges
   reach, each of its versions, and each version's dependees, the same
   lookups the driver hands PubGrub.  The walk is to a fixpoint, since a
   lazily loaded name can gain versions after it was first expanded, and it
   expands every version rather than the ones a solve would try, so it is
   meant for small instances.  A driver walks once its answer is decoded,
   so that what the walk loads reaches neither the search nor the counts
   the answer reports.

   Names and versions are keyed and sorted by their printed form, as the
   drivers' own orders are preferences rather than a reading order, so the
   printers must tell apart what they print. *)
val print :
  pp_name:(Format.formatter -> 'name -> unit) ->
  pp_version:(Format.formatter -> 'version -> unit) ->
  versions:('name -> 'version list) ->
  dependees:('name * 'version -> ('name * 'version list) list) ->
  'name list ->
  unit
