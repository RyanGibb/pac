(* A core instance (R, Δ).  Names and versions are compared as OCaml
   values, which is sound because the calculus's sets are sorted lists, so
   that values the calculus calls equal are identical; two walks of one
   instance are then equal values whatever lookups each was answered by. *)
type ('name, 'version) t = {
  packages : ('name * 'version) list;
  edges : (('name * 'version) * ('name * 'version list)) list;
}

(* The core instance reachable from [roots], through the same lookups the
   driver hands PubGrub.  The walk is to a fixpoint, since a lazily loaded
   name can gain versions after it was first expanded, and it expands every
   version rather than the ones a solve would try, so it is meant for small
   instances.  A driver walks once its answer is decoded, so that what the
   walk loads reaches neither the search nor the counts the answer reports. *)
val walk :
  versions:('name -> 'version list) ->
  dependees:('name * 'version -> ('name * 'version list) list) ->
  'name list ->
  ('name, 'version) t

(* Sorted by printed form, as the drivers' own orders are preferences
   rather than a reading order, so the printers must tell apart what they
   print. *)
val print :
  pp_name:(Format.formatter -> 'name -> unit) ->
  pp_version:(Format.formatter -> 'version -> unit) ->
  ('name, 'version) t ->
  unit
