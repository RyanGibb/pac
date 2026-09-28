type t

(* [parse] is the wall time inside the parser, or reading its output back
   from the cache, which the solve interleaves with; [cached] counts the
   names read back *)
type stats = {
  names : int;
  versions : int;
  dropped : int;
  cached : int;
  parse : float;
}

val stats : t -> stats

(* [cache] keeps what the parser made of each index file across runs *)
val empty : ?cache:string -> string -> t
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
