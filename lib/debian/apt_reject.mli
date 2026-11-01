(* What the replay reads of a solve: the tables, the candidate order PubGrub
   decides by and what its partial solution says. *)
module type SEARCH = sig
  module Tables : Tables.S

  module PVersion : sig
    type t = {
      pos : int;
      v : Tables.MultiarchDebian.Debian.Reduction.Version.t;
      tgt : (string * Tables.MultiarchDebian.coq_ReducedQualifier) option;
    }

    val compare : t -> t -> int
  end

  module Resolver : sig
    module Ranges : sig
      type t

      val contains : PVersion.t -> t -> bool
    end

    type selection = Unselected | Entailed of Ranges.t | Decided of PVersion.t
  end

  val tables : Tables.tables

  val tag :
    Tables.MultiarchDebian.Debian.Reduction.Name.t ->
    Tables.MultiarchDebian.Debian.Reduction.Version.t ->
    PVersion.t

  val cands_of :
    Tables.MultiarchDebian.Debian.Reduction.Name.t -> PVersion.t list

  val dependees_of :
    Tables.MultiarchDebian.Debian.Reduction.Name.t ->
    Tables.MultiarchDebian.Debian.Reduction.Version.t ->
    (Tables.MultiarchDebian.Debian.Reduction.Name.t * PVersion.t list) list

  val has_ref : Tables.MultiarchDebian.Debian.Reduction.Name.t -> bool

  val free_of :
    assigned:
      (Tables.MultiarchDebian.Debian.Reduction.Name.t -> Resolver.selection) ->
    Tables.MultiarchDebian.Debian.Reduction.Name.t ->
    PVersion.t list ->
    PVersion.t list

  val greatest : PVersion.t list -> PVersion.t
end

module Make (S : SEARCH) : sig
  open S
  open Tables

  type name = MultiarchDebian.Debian.Reduction.Name.t
  type assigned = name -> Resolver.selection

  (* apt's Reject propagation (Solver::Propagate, solver3.cc), which PubGrub
     learns only on deciding the package: a package is rejected once a hard
     clause of its loses its last solution or a package it conflicts with is
     installed, and the rejection cascades one queue entry at a time, as apt
     assigns a rejection at once and propagates it when the queue reaches
     it.  An installed package's own Conflicts reject the other's version
     var first, and its package var follows; a conflict declared against
     something installed rejects the declarer's package var first, and its
     version var follows.  A solution is the var apt made it: the package
     var for an unversioned atom on a name nothing provides
     (Defer-Version-Selection), else a version var. *)
  type state

  (* one queue entry of the cascade: a version var or a package var
     assigned false, whose propagation waits for its turn *)
  type rejection =
    [ `Ver of MultiarchDebian.Package.t | `Pkg of string * string ]

  val create_state : unit -> state
  val forget_rejections : state -> unit

  (* the atoms clauses on [name] were narrowed to by folding, each with the
     depender whose clause it was, the latest first *)
  val narrowings :
    state ->
    name ->
    (MultiarchDebian.Package.t * MultiarchDebian.Debian.Atom.t) list

  val stanza : MultiarchDebian.Package.t -> nstanza option

  (* the declared Provides of [n] that meet the formula *)
  val provides_matching :
    nstanza ->
    string ->
    MultiarchDebian.Debian.VersionFormula.coq_Formula ->
    (string * MultiarchDebian.Debian.coq_DTop) list

  (* whether the package, a Multi-Arch: foreign one of the atom's name, meets
     it from another architecture *)
  val sibling_provides :
    MultiarchDebian.Package.t ->
    nstanza ->
    MultiarchDebian.Debian.Atom.t ->
    bool

  val alt_name : MultiarchDebian.Debian.Atom.t -> name
  val orig_versions : name -> (PVersion.t * string) list
  val deferred : state -> MultiarchDebian.Debian.Atom.t -> bool

  val live_at :
    state ->
    pkgvar:bool ->
    string * MultiarchDebian.coq_ReducedQualifier ->
    string ->
    bool

  val solutions :
    state -> assigned option -> MultiarchDebian.Debian.Atom.t -> int

  val installed_at : assigned:assigned -> MultiarchDebian.Package.t -> bool
  val assign : state -> assigned:assigned -> rejection list -> rejection list

  val conflicts :
    state -> assigned:assigned -> MultiarchDebian.Package.t -> rejection list

  val group_conflicts :
    state -> assigned:assigned -> MultiarchDebian.Package.t -> rejection list

  val conflicted_by :
    state -> assigned:assigned -> MultiarchDebian.Package.t -> rejection list

  val propagate :
    state -> assigned:assigned -> rejection -> rejection list * name list

  val register :
    state ->
    MultiarchDebian.Package.t ->
    (name, MultiarchDebian.Debian.Atom.t) Work_heap.clause list
    * (name, MultiarchDebian.Debian.Atom.t) Work_heap.clause list

  val head :
    state ->
    assigned:assigned ->
    MultiarchDebian.Debian.Atom.t list ->
    (name, PVersion.t) Work_heap.unit_head option

  val negation :
    state -> assigned:assigned -> name -> PVersion.t -> rejection list
end
