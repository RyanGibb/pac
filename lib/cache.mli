(* the entry in the cache [dir] for [key], a hex digest, as written by the
   code whose digest is [format] (gen_format.exe's) *)
val entry : string -> format:string -> string -> string

(* the entry, open at its start, if it is there and whole Marshal values *)
val open_entry : string -> in_channel option

(* the next value of an open entry, which the caller types *)
val value : in_channel -> 'a option

(* the first value of the entry, if it is there and whole *)
val read : string -> 'a option

(* writes the entry with [write], whole or not at all *)
val store : string -> (out_channel -> unit) -> unit
