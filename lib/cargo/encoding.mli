module E = Pac

module CVerOT : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

(* SemverMatch: the two tests a version order cannot express.  sameCore
   takes the candidate first and the comparator's constant second. *)
module PM : sig
  val isPre : string -> bool
  val sameCore : string -> string -> bool
end

module Cg :
    module type of
      Pac.Cargo (Pac_common.Ot.Str) (CVerOT) (Pac_common.Ot.Str) (CVerOT)
        (Pac_common.Ot.Str)
        (Pac_common.Ot.Str)
        (PM)

module T = Cg.T

val root_feats : Cargo_parse.ver -> Cargo_query.features -> string list
val msrv_ok : string -> string option -> bool
val granularity_of : string -> string
val fset_of : string list -> Cg.FSet.t
val xentry : Cargo_parse.fentry -> Cg.FEntry.t
val slots_of : root:bool -> Cargo_parse.ver -> Cargo_parse.dep list
val slot_data : Cargo_parse.dep -> Cg.SlotData.t
val site_key : Cargo_parse.dep -> Cg.SlotKey.t

module PName : sig
  type t = Cg.NPlus.t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module PVersion : sig
  type t = { msrv : bool; v : Cg.VPlus.t }

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module PG : module type of Pubgrub.Make (PName) (PVersion)
