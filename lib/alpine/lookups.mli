module P = Apk_parse

module AVerOT : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

(* ApkVerMatch: the two constraints a version order cannot express.  Both take
   the candidate version first and the constraint's operand second. *)
module PM : sig
  val prefix : string -> string -> bool
  val hash : string -> string -> bool
end

module Alp : module type of Pac.Alpine (Pac_common.Ot.Str) (AVerOT) (PM)

module type S = sig
  module FirstDesignation : sig
    val designation : Alp.CondSet.t -> Alp.Atom.t option
  end

  module Red : module type of Alp.Reduct (FirstDesignation)
  module PF = Red.PF
  module PFR = PF.Reduction

  type iif_rule = {
    pkg : string * string;
    conds : Alp.CondSet.t;
    designation : Alp.Atom.t;
  }

  type archive = {
    by_name : (string, P.pkg list) Hashtbl.t;
    meta : (string * string, P.pkg) Hashtbl.t;
    providers : (string, ((string * string) * string option) list) Hashtbl.t;
    (* install-if rules by their designated condition's name: only a package
       bearing that name, or providing it, can carry the rule *)
    iif_by_cond : (string, iif_rule list) Hashtbl.t;
    prio : (string * string, int) Hashtbl.t;
    (* where each package stands in the index: apk_db_pkg_add appends to a
       name's provider list in the order the index is read *)
    pos : (string * string, int) Hashtbl.t;
    mutable n_pkgs : int;
    mutable n_provs : int;
    mutable n_iif : int;
    n_dropped : int;
    (* the names only a stanza the parser dropped holds a provider of *)
    uninstallable : (string, unit) Hashtbl.t;
  }

  val load_index : string -> archive

  (* the world's names no package of the index is or provides, which apk
     reports as "no such package" before it solves: it has nothing to select
     for them.  A package it will not install still names one, and a
     negated atom asks for nothing. *)
  val no_such_package : archive -> P.dep list -> string list
  val lone_provider : PF.coq_Formula -> (string * string) option
  val alt_at : PF.coq_Formula list -> Pac.nat -> (PF.coq_Formula * bool) option
  val alt_rank : archive -> bool -> PF.coq_Formula -> int

  module PVersion : sig
    (* [pv] is the version offered at the name being decided, absent for a
       version that is not a provider candidate at a name (the root, and a
       disjunction's positional [Idx]). *)
    type t = { pv : string option; rank : int; ord : int; v : PFR.Version.t }

    val v : t -> PFR.Version.t
    val bot : t
    val pp : Format.formatter -> t -> unit
    val compare : t -> t -> int
  end

  val tag : archive -> PFR.Name.t -> PFR.Version.t -> PVersion.t
  val pp_name : Format.formatter -> PFR.Name.t -> unit

  module L :
      module type of
        Package_formula.Make (Red.NameOT) (Red.VersionOT) (PF) (PVersion)
          (struct
            let pp_name = pp_name
          end)

  module PG = L.PG

  val lookups : archive -> L.t
  val touch : archive -> P.dep list -> L.t -> PFR.T.Pkg.t -> unit
end

(* generative, since each application holds the designations of the one
   index it loads *)
module Make () : S
