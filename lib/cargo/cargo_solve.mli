type result = {
  (* each crate version with the features the solution turns on *)
  crates : (string * string * string list) list;
  (* the parent relation, keyed in the theory by manifest site: one
     crate may depend on a single crate name twice -- under two aliases
     through a rename, or under one alias from two sites -- and the
     copies may land on different granularity classes, so the edge has
     to record which declaration received which version.  ParentElt
     carries only the target's version, since the site already
     determines the slot it came through; the target name is read back
     off that slot here, and the alias is what is reported, because a
     consumer comparing against cargo's (depender, dependee) edges has
     no other way to name the crate the version belongs to and no notion
     of a site at all.
     (owner, owner version, alias, target name, target version) *)
  parents : (string * string * string * string * string) list;
  nodes : int;
  lookups : int;
}

(* what one solve read of the index, reported whether or not it found an
   answer *)
type run = {
  answer : (result, Pac_common.Report.explanation) Stdlib.result;
  core : unit -> unit;
  n_names : int;
  n_vers : int;
  dropped : int;
  t_parse : float;
}

val solve :
  ?debug:bool ->
  ?order:Pac_common.Order.t ->
  index:string ->
  features:Cargo_query.features ->
  rustv:string option ->
  Cargo_query.root ->
  run

(* cargo tells packages apart by source as well, so without the
   self-patch the registry's crate at the root's name and version is a
   second package, which one node per (name, version) cannot be *)
val reaches_registry_root : Cargo_query.root -> result -> bool
