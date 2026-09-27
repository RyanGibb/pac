(* The split apt makes between what it unit-propagates (Enqueue) and what it
   queues as a work item, seen through the synthetic names of the
   encoding. *)
type kind =
  (* a real package name: apt enqueues the package var *)
  | Package
  (* a clause package whose Clause has eager = true *)
  | Hard
  (* an optional (Recommends) clause package *)
  | Soft
  (* a lone alternative standing in for its own clause *)
  | Alternative

(* One clause of a decided package as apt registers it: [name] stands for
   it -- its clause package, or the one target of a bare Depends, which apt
   enqueues rather than queues as work -- and is None for a clause folded
   into an earlier one. *)
type ('name, 'atom) clause = {
  optional : bool;
  name : 'name option;
  atoms : 'atom list;
}

(* the one live alternative of a clause found unit, apt's Enqueue of that
   solution, with the package and candidate version it stands for where the
   solution is a version var *)
type ('name, 'version) unit_head = {
  solution : 'name;
  version_var : ('name * 'version) option;
}

module type DRIVER = sig
  (* the rejections assigned so far, and what the driver caches over the
     instance *)
  type state
  type name
  type version
  type atom

  (* what the partial solution says about a name, as the solver hands it to
     the [next] hook *)
  type assigned

  val kind : name -> kind

  (* the alternatives of the clause [name] stands for *)
  val clause_atoms : name -> atom list option

  (* apt's solution count for one alternative: the target packages it can
     still be discharged by, live under the partial solution and over the
     candidates-only instance respectively (apt's static count also takes
     in the versions Strict-Pinning rejected) *)
  val solutions : state -> assigned:assigned -> atom -> int
  val static_solutions : state -> atom -> int

  (* some package the alternative can be discharged by is obsolete to apt
     (Obsolete, solver3.cc:890-925): a binary of its source comes from a
     newer source version *)
  val obsolete : atom -> bool

  (* the value the partial solution has decided [name] at, if any *)
  val decided : assigned -> name -> version option

  (* apt's ELIDED: some solution of the clause [name] stands for is already
     in the partial solution, so deciding it installs nothing *)
  val satisfied : assigned -> name -> bool

  (* one entry of apt's propagation queue that is a rejection: a literal
     assigned false the moment it was derived, and propagated to what
     watches it only when the queue reaches it *)
  type rejection

  (* a package decision now stands: the rejections its own Conflicts
     assign as its clauses are examined, each to be queued for propagation
     at that point, those not already assigned and not of a package the
     partial solution installs *)
  val conflicts :
    state -> assigned:assigned -> name -> version -> rejection list

  (* the rejections assigned as the decided version's var propagates: the
     declarers of a conflict it matches, each to be queued at that point *)
  val conflicted_by :
    state -> assigned:assigned -> name -> version -> rejection list

  (* runs one entry, assigning and returning the rejections it derives in
     turn, with the clauses of installed packages it leaves unit, whose one
     solution apt enqueues there and then *)
  val propagate :
    state -> assigned:assigned -> rejection -> rejection list * name list

  (* forgets every rejection, ahead of the standing decisions being
     replayed *)
  val reset : state -> unit

  (* assigns rejections derived outside the driver's own propagation, as
     [conflicts] assigns its own *)
  val assign : state -> assigned:assigned -> rejection list -> rejection list
  val version_equal : version -> version -> bool

  (* the propagation wave a standing decision sets off: the decided
     package's clauses in control-file order, first those apt registers on
     the package var, walked as the package pops, then those it registers
     on the version var, walked one queue entry later as the version pops *)
  val registered :
    state ->
    name ->
    version ->
    (name, atom) clause list * (name, atom) clause list

  (* what apt's Assume of the alternative a clause was decided to enqueues:
     its selector, or its package where the alternative is deferred *)
  val continuation : name -> version -> name list

  (* the package a decided selector forces, where apt would have enqueued
     that package at the selector's own queue slot rather than reaching it
     through a version's SelectVersion clause at the back *)
  val forced_to : state -> name -> version -> name option

  (* the package and version a decided selector settles on, where that
     decision is apt's version var popping: the clauses registered on the
     version are walked then, and its package var joins the queue *)
  val version_of : state -> name -> version -> (name * version) option

  (* the unit head of a clause found unit: its version var is there only
     for an atom neither deferred nor matched by a provider, whose package
     var apt reaches only as the version pops *)
  val head :
    state -> assigned:assigned -> atom list -> (name, version) unit_head option

  val same_name : name -> name -> bool

  (* the literal apt's Pop asserts against a decision it undoes: the
     solution the decision installed, rejected *)
  val negation : state -> assigned:assigned -> name -> version -> rejection list
end

module Make (D : DRIVER) : sig
  type t

  val create : D.state -> t
  val state : t -> D.state
  val kept : t -> D.name -> D.version option
  val next : t -> assigned:D.assigned -> (D.name * int) list -> D.name
  val report : t -> unit
end
