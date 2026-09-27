(* a directory opens, and only the read fails, with an error that does not
   name the path as open_in's own does *)
val file : string -> unit

(* a missing directory would read as one holding nothing, which makes every
   name unknown rather than the input unreadable *)
val dir : string -> unit
