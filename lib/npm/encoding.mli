module E = Pac

module NVerOT : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

(* SemverMatch: the two tests the version order cannot express.  sameCore
   takes the candidate version first and the comparator's constant
   second. *)
module PM : sig
  val isPre : string -> bool
  val sameCore : string -> string -> bool
end

module Np : module type of Pac.Npm (Pac_common.Ot.Str) (NVerOT) (PM)
module R = Np.Reduction
module T = Np.T

val xop : Npm_version.op -> E.cmpOp
val xrange : Npm_version.range -> Np.coq_Range

module PName : sig
  type t = Np.Nm.name

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module PVersion : sig
  type t = Np.Vs.version

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end

module PG : module type of Pubgrub.Make (PName) (PVersion)
