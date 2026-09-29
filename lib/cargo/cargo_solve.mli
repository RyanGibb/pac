type result = {
  (* each crate version with the features the solution turns on *)
  crates : (string * string * string list) list;
  (* (owner, owner version, alias, dependee name, dependee version): a crate
     can depend on one name twice, under two aliases or from two sites, and
     get two versions, so the alias names the edge for a consumer comparing
     against cargo's (depender, dependee) edges. *)
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
  cached : int;
  t_parse : float;
}

module Make () : sig
  val solve :
    ?debug:bool ->
    ?order:Pac_common.Order.t ->
    ?cache:string ->
    index:string ->
    features:Cargo_query.features ->
    rustv:string option ->
    Cargo_query.root ->
    run
end

(* cargo tells packages apart by source as well, so without the
   self-patch the registry's crate at the root's name and version is a
   second package, which one node per (name, version) cannot be *)
val reaches_registry_root : Cargo_query.root -> result -> bool
