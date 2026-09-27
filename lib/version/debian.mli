val compare : string -> string -> int

(* opam's OpamVersionCompare: opam versions have no epoch, so a ':' is an
   ordinary character *)
val compare_no_epoch : string -> string -> int
