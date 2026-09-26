let c2r c = if c < 0 then Pac.Lt else if c > 0 then Pac.Gt else Pac.Eq
let r2c = function Pac.Lt -> -1 | Pac.Eq -> 0 | Pac.Gt -> 1

module Make (X : sig
  type t

  val compare : t -> t -> int
end) =
struct
  type t = X.t

  let compare a b = c2r (X.compare a b)
  let eq_dec a b = X.compare a b = 0
end

module Str = Make (String)

let rec nat_int (n : Pac.nat) : int =
  match n with Pac.O -> 0 | Pac.S k -> 1 + nat_int k

let rec int_nat (k : int) : Pac.nat =
  if k <= 0 then Pac.O else Pac.S (int_nat (k - 1))
