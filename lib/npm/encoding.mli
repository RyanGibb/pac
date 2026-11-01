module E = Pac

val xop : Npm_version.op -> E.cmpOp

module type S = sig
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
  module T = Np.Reduced

  val xrange : Npm_version.range -> Np.coq_Range

  module PName : sig
    type t = Np.Name.name

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module PVersion : sig
    type t = Np.Version.version

    val compare : t -> t -> int
    val equal : t -> t -> bool
    val pp : Format.formatter -> t -> unit
  end

  module PG : module type of Pubgrub.Make (PName) (PVersion)
end

(* generative, and applied by the npm command alone, so that no other
   command pays for applying the extracted functor *)
module Make () : S
