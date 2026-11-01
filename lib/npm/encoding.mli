val xop : Npm_version.op -> Pac.cmpOp

module type S = sig
  module NpmVersionOT : sig
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

  module Npm : module type of Pac.Npm (Pac_common.Ot.Str) (NpmVersionOT) (PM)
  module Reduction = Npm.Reduction
  module Reduced = Npm.Reduced

  val xrange : Npm_version.range -> Npm.coq_Range

  module PName : sig
    type t = Npm.Name.name

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module PVersion : sig
    type t = Npm.Version.version

    val compare : t -> t -> int
    val equal : t -> t -> bool
    val pp : Format.formatter -> t -> unit
  end

  module Resolver : module type of Pubgrub.Make (PName) (PVersion)
end

(* generative, and applied by the npm command alone, so that no other
   command pays for applying the extracted functor *)
module Make () : S
