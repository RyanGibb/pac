module E = Pac
module Ot = Pac_common.Ot

(* A version with its parse, made once per distinct string, ordered as the
   npm reading orders versions (Npm_version.compare). *)
module IVer : sig
  type t = { s : string; p : Version.Semver.t }

  val make : string -> t
  val compare : t -> t -> int
end

module IVerOT : sig
  type t = IVer.t

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

(* SemverMatch over the parsed versions *)
module IPM : sig
  val isPre : IVer.t -> bool
  val sameCore : IVer.t -> IVer.t -> bool
end

module Npl : module type of Pac.NpmPlacement (Pac_common.Ot.Str) (IVerOT) (IPM)
module Pl = Npl.Pl
module R = Pl.Reduction
module T = R.T
module Lk = Npl.Lookup

val xrange : Npm_version.range -> Npl.coq_Range

(* a location, stored deepest key first, as a lock's packages key *)
val lock_path : string list -> string
val occ_compare : Npl.Occ.t -> Npl.Occ.t -> int

(* The orders of the extracted Name and Version, restated in OCaml;
   PAC_NPM_CHECKCMP compares every comparison against the extracted one. *)
module PName : sig
  type t = R.Name.t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module PVersion : sig
  type t = R.Version.t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end

module PG : module type of Pubgrub.Make (PName) (PVersion)
