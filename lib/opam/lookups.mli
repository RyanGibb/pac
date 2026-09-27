module OVerOT : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

type archive = {
  root : string;
  pkgs : (string, (string * Opam_parse.pkg_meta) list) Hashtbl.t;
  (* class -> its members among the names loaded so far.  Unlike every
     other table here this one is a preimage and so grows as names load;
     see [class_inst]. *)
  class_table : (string, (string * string) list) Hashtbl.t;
  (* the versions a name flags avoid-version or deprecated; a table
     because every version handed to PubGrub is tagged with it, and
     because all but a hundred or so names answer no *)
  avoid_table : (string, string list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_dropped : int;
  (* wall time inside the parser, which the solve interleaves with *)
  mutable t_parse : float;
}

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

module Op :
    module type of
      Pac.Opam (Pac_common.Ot.Str) (OVerOT) (Pac_common.Ot.Str) (OVerOT)
        (Pac_common.Ot.Str)

module Red = Op.Reduction
module PF = Red.PF
module PFR = PF.Reduction
module T = PFR.T

type request = {
  (* the valuation reads only the query's names, not their versions *)
  names : string list;
  with_test : bool;
  with_doc : bool;
  with_dev_setup : bool;
  opam_version : string;
}

val rho : request -> string -> string option
val xvc : Opam_parse.vc -> Op.coq_VConstraint

val depexts_of :
  (string -> string option) -> archive -> (string * string) list -> string list

val pp_name : Format.formatter -> PFR.Name.t -> unit

module PVersion : sig
  type t = { avoid : bool; v : PFR.Version.t }

  val v : t -> PFR.Version.t
  val bot : t
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module L :
    module type of
      Package_formula.Make (Red.TNOT) (Red.TVOT) (PF) (PVersion)
        (struct
          let pp_name = pp_name
        end)

module PG = L.PG

val lookups : (string -> string option) -> archive -> L.t

val touch :
  (string -> string option) ->
  archive ->
  (string * Opam_parse.vc) list ->
  L.t ->
  T.Pkg.t ->
  unit
