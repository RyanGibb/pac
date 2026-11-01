module type S = sig
  module CargoVersionOT : sig
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

  module Cargo :
      module type of
        Pac.Cargo (Pac_common.Ot.Str) (CargoVersionOT) (Pac_common.Ot.Str)
          (CargoVersionOT)
          (Pac_common.Ot.Str)
          (Pac_common.Ot.Str)
          (PM)

  module Reduced = Cargo.Reduction.Reduced

  val root_feats : Cargo_parse.ver -> Cargo_query.features -> string list
  val msrv_ok : string -> string option -> bool
  val granularity_of : string -> string
  val fset_of : string list -> Cargo.FSet.t
  val xentry : Cargo_parse.fentry -> Cargo.FeatureEntry.t
  val slots_of : root:bool -> Cargo_parse.ver -> Cargo_parse.dep list
  val slot_data : Cargo_parse.dep -> Cargo.DependencyRecord.t
  val site_key : Cargo_parse.dep -> Cargo.Site.t

  module PName : sig
    type t = Cargo.Reduction.Name.t

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module PVersion : sig
    type t = { msrv : bool; v : Cargo.Reduction.Version.t }

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module Resolver : module type of Pubgrub.Make (PName) (PVersion)
end

(* generative, and applied by the cargo command alone, so that no other
   command pays for applying the extracted functor *)
module Make () : S
