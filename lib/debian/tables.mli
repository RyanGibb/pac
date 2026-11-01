module DebianVersionOT : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

module type ARCH = sig
  val arches : string list
  val native : string
end

type stats = { names : int; versions : int }

(* what the replay is written against; the instance's own types, whatever
   the architectures *)
module type S = sig
  module APx : sig
    module Architecture : sig
      type t = string

      val compare : t -> t -> Pac.comparison
      val eq_dec : t -> t -> bool
      val enum : string list
    end

    val native : string
  end

  module MultiarchDebian :
      module type of
        Pac.MultiarchDebian (Pac_common.Ot.Str) (DebianVersionOT) (APx)

  (* Normalized stanza: apt rewrites arch:all packages to the native arch
     and downgrades all+same to no (arch:all content is arch-invariant).
     Its Depends and Recommends clauses are still the raw field text, and
     are parsed once, on the first sub-instance that reads them. *)
  type nstanza = {
    npkg : MultiarchDebian.Package.t;
    ncls : MultiarchDebian.coq_MAClass;
    raw_deps : string list;
    raw_recs : string list;
    mutable nclauses :
      (MultiarchDebian.Atom.t list list * MultiarchDebian.Atom.t list list)
      option;
    nprovs : (string * MultiarchDebian.Debian.coq_DTop) list;
    nconfs : MultiarchDebian.Atom.t list;
    (* apt ranks the providers claiming a name by these *)
    ness : bool;
    nimp : bool;
    nprio : int;
    nsrc : string * string;
    (* apt keys an arch:all version apart from its native twin
       (Version::All), whatever package arch it was filed under *)
    nall : bool;
  }

  type tables

  (* what build_tables makes at once, which is all a cache need keep: the
     rest is built from it on demand *)
  type eager

  val eager : tables -> eager
  val of_eager : eager -> tables
  val stats : tables -> stats
  val stanza : tables -> MultiarchDebian.Package.t -> nstanza option

  (* the versions of the package [(name, arch)] *)
  val versions_of : tables -> string * string -> string list

  (* every [(arch, version)] of every member of the group [name] *)
  val group_members : tables -> string -> (string * string) list

  (* the packages declaring a Provides of [name], each at the version it
     provides *)
  val providers :
    tables ->
    string ->
    (MultiarchDebian.Package.t * MultiarchDebian.Debian.coq_DTop) list

  (* who names [name] in a Depends or Pre-Depends, and who in a Conflicts or
     Breaks, by the bare name as written *)
  val dependers : tables -> string -> MultiarchDebian.Package.t list
  val conflicters : tables -> string -> MultiarchDebian.Package.t list

  (* the alternative's position in the clause being decided, which is what
     PVersion.compare ranks on; max_int for an atom the clause does not list,
     which cannot arise for a name introduced from that clause *)
  val atom_pos :
    MultiarchDebian.Debian.Clause.t -> MultiarchDebian.Debian.Atom.t -> int

  val build_tables : recommends:bool -> Deb_packages.stanza list -> tables
  val obsolete : tables -> nstanza -> bool
  val deps_of : nstanza -> MultiarchDebian.Atom.t list list
  val recs_of : nstanza -> MultiarchDebian.Atom.t list list

  val ordered_clauses :
    tables ->
    MultiarchDebian.Package.t ->
    (bool
    * MultiarchDebian.Debian.Reduction.Name.t
    * MultiarchDebian.Debian.Atom.t list)
    list

  val sat : MultiarchDebian.Debian.VersionFormula.coq_Formula -> string -> bool

  val pp_mname :
    Format.formatter -> string * MultiarchDebian.coq_ReducedQualifier -> unit

  val pp_atom : Format.formatter -> MultiarchDebian.Debian.Atom.t -> unit

  module PName : sig
    type t = MultiarchDebian.Debian.Reduction.Name.t

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val pp_core : Format.formatter -> t -> unit
  end
end

module Make (_ : ARCH) : S
