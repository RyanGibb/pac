type explanation = Format.formatter -> unit

type loaded = {
  names : int;
  versions : int;
  extra : string list;
  dropped : int;
  parse : float;
}

val root : string -> unit
val section : string -> string list -> unit
val packages : string list -> unit
val encoded : nodes:int -> lookups:int -> unit
val unsatisfiable : explanation -> unit
val loaded : loaded -> solve:float -> unit
