(* What the replay reads of a solve: the tables, the candidate order PubGrub
   decides by and what its partial solution says. *)
module type SEARCH = sig
  module T : Tables.S

  module PVersion : sig
    type t = { pos : int; v : T.DMA.Deb.Version.t }

    val compare : t -> t -> int
  end

  module PG : sig
    module Ranges : sig
      type t

      val contains : PVersion.t -> t -> bool
    end

    type selection = Unselected | Entailed of Ranges.t | Decided of PVersion.t
  end

  val tables : T.tables
  val tag : T.DMA.Deb.Name.t -> T.DMA.Deb.Version.t -> PVersion.t
  val cands_of : T.DMA.Deb.Name.t -> PVersion.t list

  val dependees_of :
    T.DMA.Deb.Name.t ->
    T.DMA.Deb.Version.t ->
    (T.DMA.Deb.Name.t * PVersion.t list) list

  val has_ref : T.DMA.Deb.Name.t -> bool

  val free_of :
    assigned:(T.DMA.Deb.Name.t -> PG.selection) ->
    T.DMA.Deb.Name.t ->
    PVersion.t list ->
    PVersion.t list

  val greatest : PVersion.t list -> PVersion.t
end

module Make (S : SEARCH) : sig
  open S
  open T

  type name = DMA.Deb.Name.t
  type assigned = name -> PG.selection

  (* apt's Reject propagation (Solver::Propagate, solver3.cc): a package is
     rejected the moment a hard clause of its loses its last solution, or a
     package it conflicts with is installed, and the rejection cascades
     through the discovered closure along the watch lists.  PubGrub learns
     the same only when it decides the package, so without this the live
     solution counts and the choice among alternatives would see
     alternatives apt has already crossed off.  apt assigns a rejection the
     moment it is derived and propagates it only when the queue reaches it,
     so each step of the cascade is one queue entry, which the shadow heap
     holds; and a package is two literals, whose order the cascade
     alternates: the installed package's own Conflicts reject the other's
     version var (its solutions are versions) and its package var follows
     through the SelectVersion clause, while a conflict declared against
     something installed rejects the declarer's package var, the reason of
     its clauses, and its version var follows through the version's own
     clause.  A solution reads the literal apt made it: the package var for
     an unversioned atom on a name nothing provides (Defer-Version-Selection),
     a version var otherwise. *)
  type state

  (* one queue entry of the cascade: a version var or a package var
     assigned false, whose propagation waits for its turn *)
  type rejection = [ `Ver of DMA.Pkg.t | `Pkg of string * string ]

  val create_state : unit -> state
  val forget_rejections : state -> unit

  (* the atoms clauses on [name] were narrowed to by folding, each with the
     depender whose clause it was, the latest first *)
  val narrowings : state -> name -> (DMA.Pkg.t * DMA.Deb.Atom.t) list
  val stanza : DMA.Pkg.t -> nstanza option

  (* the declared Provides of [n] that meet the formula *)
  val provides_matching :
    nstanza ->
    string ->
    DMA.Deb.Ver.coq_Formula ->
    (string * DMA.Deb.coq_DTop) list

  val alt_name : DMA.Deb.Atom.t -> name
  val orig_versions : name -> (PVersion.t * string) list
  val deferred : state -> DMA.Deb.Atom.t -> bool

  val live_at :
    state -> pkgvar:bool -> string * DMA.coq_NameArch -> string -> bool

  val solutions : state -> assigned option -> DMA.Deb.Atom.t -> int
  val installed_at : assigned:assigned -> DMA.Pkg.t -> bool
  val assign : state -> assigned:assigned -> rejection list -> rejection list
  val conflicts : state -> assigned:assigned -> DMA.Pkg.t -> rejection list
  val conflicted_by : state -> assigned:assigned -> DMA.Pkg.t -> rejection list

  val propagate :
    state -> assigned:assigned -> rejection -> rejection list * name list

  val register :
    state ->
    DMA.Pkg.t ->
    (name, DMA.Deb.Atom.t) Work_heap.clause list
    * (name, DMA.Deb.Atom.t) Work_heap.clause list

  val head :
    state ->
    assigned:assigned ->
    DMA.Deb.Atom.t list ->
    (name, PVersion.t) Work_heap.unit_head option

  val negation :
    state -> assigned:assigned -> name -> PVersion.t -> rejection list
end
