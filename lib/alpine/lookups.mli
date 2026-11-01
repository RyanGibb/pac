module ApkVersionOT : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

(* ApkVersionMatch: the two constraints a version order cannot express.  Both
   take the candidate version first and the constraint's operand second. *)
module PM : sig
  val prefix : string -> string -> bool
  val hash : string -> string -> bool
end

module Alpine :
    module type of Pac.Alpine (Pac_common.Ot.Str) (ApkVersionOT) (PM)

type stats = {
  names : int;
  versions : int;
  provides : int;
  install_ifs : int;
  dropped : int;
}

module type S = sig
  module FirstDesignation : sig
    val designation : Alpine.ConditionSet.t -> Alpine.Atom.t option
  end

  module Reduction : module type of Alpine.ReductionUnder (FirstDesignation)
  module PackageFormula = Reduction.PackageFormula
  module PackageFormulaReduction = PackageFormula.Reduction

  type archive

  val stats : archive -> stats
  val load_index : string -> archive

  (* the world's names no package of the index is or provides, which apk
     reports as "no such package" before it solves: it has nothing to select
     for them.  A package it will not install still names one, and a
     negated atom asks for nothing. *)
  val no_such_package : archive -> Apk_parse.dep list -> string list
  val lone_provider : PackageFormula.coq_Formula -> (string * string) option

  val alt_at :
    PackageFormula.coq_Formula list ->
    Pac.nat ->
    (PackageFormula.coq_Formula * bool) option

  val alt_rank : archive -> bool -> PackageFormula.coq_Formula -> int

  module PVersion : sig
    (* [pv] is the version offered at the name being decided, absent for a
       version that is not a provider candidate at a name (the root, and a
       disjunction's positional [Idx]). *)
    type t = {
      pv : string option;
      rank : int;
      ord : int;
      v : PackageFormulaReduction.Version.t;
    }

    val v : t -> PackageFormulaReduction.Version.t
    val bot : t
    val pp : Format.formatter -> t -> unit
    val compare : t -> t -> int
  end

  val tag :
    archive ->
    PackageFormulaReduction.Name.t ->
    PackageFormulaReduction.Version.t ->
    PVersion.t

  val pp_name : Format.formatter -> PackageFormulaReduction.Name.t -> unit

  module FormulaLookups :
      module type of
        Package_formula.Make (Reduction.NameOT) (Reduction.VersionOT)
          (PackageFormula)
          (PVersion)
          (struct
            let pp_name = pp_name
          end)

  module Resolver = FormulaLookups.Resolver

  val lookups : archive -> FormulaLookups.t

  val touch :
    archive ->
    Apk_parse.dep list ->
    FormulaLookups.t ->
    PackageFormulaReduction.Reduced.Package.t ->
    unit
end

(* generative, since each application holds the designations of the one
   index it loads *)
module Make () : S
