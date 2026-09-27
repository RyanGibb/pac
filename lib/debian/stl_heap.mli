(* libstdc++'s binary heap (bits/stl_heap.h), reproduced exactly: a
   comparator whose ties nothing else settles leaves the order to the way
   equal elements travel, which a textbook sift-down would change. *)
type 'a t

val create : ('a -> 'a -> bool) -> 'a t
val length : 'a t -> int

(* room for one more element, the fresh cells filled with [x] *)
val grow : 'a array -> int -> 'a -> 'a array
val push : 'a t -> 'a -> unit
val pop : 'a t -> 'a

(* std::remove_if, which is stable, then std::make_heap *)
val filter : 'a t -> ('a -> bool) -> unit
