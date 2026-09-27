module DebVersionOT : sig
  type t = string

  val compare : t -> t -> Pac.comparison
  val eq_dec : t -> t -> bool
end

module type ARCH = sig
  val arches : string list
  val native : string
end

(* what the replay is written against; the instance's own types, whatever
   the architectures *)
module type S = sig
  module APx : sig
    module A : sig
      type t = string

      val compare : t -> t -> Pac.comparison
      val eq_dec : t -> t -> bool
      val enum : string list
    end

    val native : string
  end

  module DMA :
      module type of Pac.DebianMA (Pac_common.Ot.Str) (DebVersionOT) (APx)

  (* Normalized stanza: apt rewrites arch:all packages to the native arch
     and downgrades all+same to no (arch:all content is arch-invariant).
     Its Depends and Recommends clauses are still the raw field text, and
     are parsed once, on the first sub-instance that reads them. *)
  type nstanza = {
    npkg : DMA.Pkg.t;
    ncls : DMA.coq_MAClass;
    raw_deps : string list;
    raw_recs : string list;
    mutable nclauses : (DMA.Atom.t list list * DMA.Atom.t list list) option;
    nprovs : (string * DMA.Deb.coq_DTop) list;
    nconfs : DMA.Atom.t list;
    (* apt ranks the providers claiming a name by these *)
    ness : bool;
    nimp : bool;
    nprio : int;
    nsrc : string * string;
    (* apt keys an arch:all version apart from its native twin
       (Version::All), whatever package arch it was filed under *)
    nall : bool;
  }

  type tables = {
    versions_table : (string * string, string list) Hashtbl.t;
    stanza_table : (DMA.Pkg.t, nstanza) Hashtbl.t;
    group_table : (string, (string * string) list) Hashtbl.t;
    providers_table : (string, (DMA.Pkg.t * DMA.Deb.coq_DTop) list) Hashtbl.t;
    (* who names a package in a Depends or Pre-Depends, and who in a
       Conflicts or Breaks, by the bare name as written: the watch lists
       apt's Reject propagation walks, built from the field text alone, so
       no clause is parsed for them; only the tool order asks *)
    rev_dep_table : (string, DMA.Pkg.t list) Hashtbl.t Lazy.t;
    rev_conf_table : (string, DMA.Pkg.t list) Hashtbl.t Lazy.t;
    (* the binaries each source name builds, for apt's obsolescence test,
       likewise asked for by the tool order alone *)
    source_table : (string, nstanza list) Hashtbl.t Lazy.t;
    (* selector preimages by name, and a package's clauses in field order,
       both asked for again by every depender and by the rejection cascade *)
    sel_cache :
      (string * DMA.coq_NameArch, DMA.Deb.PkgSet.t * DMA.Deb.Prov.t) Hashtbl.t;
    oc_cache :
      (DMA.Pkg.t, (bool * DMA.Deb.Name.t * DMA.Deb.Atom.t list) list) Hashtbl.t;
  }

  val find_list : ('a, 'b list) Hashtbl.t -> 'a -> 'b list
  val stanza : tables -> DMA.Pkg.t -> nstanza option

  (* the alternative's position in the clause being decided, which is what
     PVersion.compare ranks on; max_int for an atom the clause does not list,
     which cannot arise for a name introduced from that clause *)
  val atom_pos : DMA.Deb.Clause.t -> DMA.Deb.Atom.t -> int
  val build_tables : recommends:bool -> Deb_packages.stanza list -> tables
  val obsolete : tables -> nstanza -> bool
  val deps_of : nstanza -> DMA.Atom.t list list
  val recs_of : nstanza -> DMA.Atom.t list list

  val ordered_clauses :
    tables -> DMA.Pkg.t -> (bool * DMA.Deb.Name.t * DMA.Deb.Atom.t list) list

  val sat : DMA.Deb.Ver.coq_Formula -> string -> bool
  val pp_mname : Format.formatter -> string * DMA.coq_NameArch -> unit
  val pp_atom : Format.formatter -> DMA.Deb.Atom.t -> unit

  module PName : sig
    type t = DMA.Deb.Name.t

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val pp_core : Format.formatter -> t -> unit
  end
end

module Make (_ : ARCH) : S
