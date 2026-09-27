val find_list : ('a, 'b list) Hashtbl.t -> 'a -> 'b list
val push : ('a, 'b list) Hashtbl.t -> 'a -> 'b -> unit
val memo : ('a, 'b) Hashtbl.t -> 'a -> (unit -> 'b) -> 'b
