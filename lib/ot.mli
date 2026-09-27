val r2c : Pac.comparison -> int

module Make (X : sig
  type t

  val compare : t -> t -> int
end) : sig
  type t = X.t

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

module Str : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

val nat_int : Pac.nat -> int
val int_nat : int -> Pac.nat
