module OpamVersionOT : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

type archive

(* [parse] is the wall time inside the parser, which the solve interleaves
   with *)
type stats = { names : int; versions : int; dropped : int; parse : float }

val stats : archive -> stats
val repository : archive -> string
val empty_archive : string -> archive
val versions_of : archive -> string -> string list
val meta_of : archive -> string -> string -> Opam_parse.pkg_meta

(* opam answers opam-version with its own version unless
   OPAMVAR_opam_version or a global or switch variable overrides it
   (opamPackageVar.ml resolve_switch_raw); the harness leaves opam's own
   and pins us to it instead.  Unasked, the value is the opam
   nix/flake.lock fixes, so that a run outside the harness answers about
   the same opam the recorded baselines did *)
val default_opam_version : string
val default_platform : (string * string) list

module Opam :
    module type of
      Pac.Opam (Pac_common.Ot.Str) (OpamVersionOT) (Pac_common.Ot.Str)
        (OpamVersionOT)
        (Pac_common.Ot.Str)

module Reduction = Opam.Reduction
module PackageFormula = Reduction.PackageFormula
module PackageFormulaReduction = PackageFormula.Reduction
module Reduced = PackageFormulaReduction.Reduced

type request = {
  (* the valuation reads only the query's names, not their versions *)
  names : string list;
  with_test : bool;
  with_doc : bool;
  with_dev_setup : bool;
  opam_version : string;
  platform : (string * string) list;
}

val rho : request -> string -> string option
val xvc : Opam_parse.vc -> Opam.coq_VFormula

val depexts_of :
  (string -> string option) -> archive -> (string * string) list -> string list

val pp_name : Format.formatter -> PackageFormulaReduction.Name.t -> unit

module PVersion : sig
  type t = { avoid : bool; v : PackageFormulaReduction.Version.t }

  val v : t -> PackageFormulaReduction.Version.t
  val bot : t
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module FormulaLookups :
    module type of
      Package_formula.Make (Reduction.NameOT) (Reduction.VersionOT)
        (PackageFormula)
        (PVersion)
        (struct
          let pp_name = pp_name
        end)

module Resolver = FormulaLookups.Resolver

val lookups : (string -> string option) -> archive -> FormulaLookups.t

val touch :
  (string -> string option) ->
  archive ->
  (string * Opam_parse.vc) list ->
  FormulaLookups.t ->
  Reduced.Package.t ->
  unit
