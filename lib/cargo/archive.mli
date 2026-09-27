(* The index as a run has read it so far.  There is no cone pass: a crate
   is parsed the first time a sub-instance reads its name, as cargo's
   sparse protocol fetches it, so a run touches the crates the solver asks
   about and no others.  Because the instance is still being uncovered, the
   sub-instance a lookup theorem names must be complete at the moment the
   lookup answers.  Each is complete by construction -- name_set,
   support_of_name and repo_preimage load every name they read whole, and
   meta and the owner scan load the owner -- except the one
   versions_lookupLink names.  Its sub-instance is the preimage of the link
   relation at l -- every crate version declaring l -- and no declaration
   of any one crate names the other declarers, so nothing a loaded crate
   carries can bring them in: links_table holds the declarers among the
   names loaded so far, and may grow after CLink l has answered.
   Lookups.pg_versions answers it afresh each time rather than memoizing
   it. *)
type t = {
  index : string;
  crates : (string, Cargo_parse.ver list) Hashtbl.t;
  entry : (string * string, Cargo_parse.ver) Hashtbl.t;
  links_table : (string, (string * string) list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_dropped : int;
  (* wall time inside the parser, which the solve interleaves with *)
  mutable t_parse : float;
}

val empty : string -> t
val load_name : t -> string -> Cargo_parse.ver list

(* whether the index has a file for the name, yanked versions and all *)
val listed : t -> string -> bool
val versions_of : t -> string -> string list

(* a manifest is read only through its name's load, so a crate version's
   declarations are never taken from a name parsed in part *)
val meta : t -> string -> string -> Cargo_parse.ver option

(* the query's root package, a crate version like any other once its name
   has been read: it takes the place of a registry version at its own
   (name, version), which is the one node the model has there *)
val install_root : t -> Cargo_parse.ver -> unit
val link_preimage : t -> string -> (string * string) list
