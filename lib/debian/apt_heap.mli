(* The split apt makes between what it unit-propagates (Enqueue) and what it
   queues as a work item, seen through the synthetic names of the
   encoding. *)
type kind =
  (* a real package name: apt enqueues the package var *)
  | Package
  (* a clause package whose Clause carries eager = true *)
  | Hard
  (* an optional (Recommends) clause package *)
  | Soft
  (* a lone alternative standing in for its own clause *)
  | Alternative

module type DRIVER = sig
  type name
  type version
  type atom

  (* what the partial solution says about a name, as the solver hands it to
     the [next] hook *)
  type assigned

  val pp_name : Format.formatter -> name -> unit
  val pp_atom : Format.formatter -> atom -> unit
  val kind : name -> kind

  (* the alternatives of the clause [name] stands for *)
  val clause_atoms : name -> atom list option

  (* apt's solution count for one alternative: the target packages it can
     still be discharged by, live under the partial solution and over the
     candidates-only instance respectively (apt's static count also takes
     in the versions Strict-Pinning rejected) *)
  val atom_count : assigned -> atom -> int
  val atom_static : atom -> int

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

  val pp_rejection : Format.formatter -> rejection -> unit

  (* a package decision now stands: the rejections its own Conflicts assign
     as its clauses are examined, and those assigned as its version var
     propagates -- the declarers of a conflict it matches -- each to be
     queued for propagation at that point; [propagate] runs one entry,
     assigning and returning the rejections it derives in turn, with the
     clauses of installed packages it leaves unit, whose one solution apt
     enqueues there and then; [reset] forgets every rejection, ahead of the
     standing decisions being replayed *)
  val conflicts : assigned -> name -> version -> rejection list
  val conflicted_by : assigned -> name -> version -> rejection list
  val propagate : assigned -> rejection -> rejection list * name list
  val reset : unit -> unit
  val version_equal : version -> version -> bool

  (* the propagation wave a standing decision sets off: the decided
     package's clauses in control-file order, each as its optional flag, the
     name that stands for it -- its clause package, or the one target of a
     bare Depends, which apt enqueues rather than queues as work -- and its
     alternatives; first those apt registers on the package var, walked as
     the package pops, then those it registers on the version var, walked
     one queue entry later as the version pops *)
  val wave :
    name ->
    version ->
    (bool * name option * atom list) list
    * (bool * name option * atom list) list

  (* what apt's Assume of the alternative a clause was decided to enqueues:
     its selector, or its package where the alternative is deferred *)
  val continuation : name -> version -> name list

  (* the package a decided selector forces, where apt would have enqueued
     that package at the selector's own queue slot rather than reaching it
     through a version's SelectVersion clause at the back *)
  val forced_to : name -> version -> name option

  (* the package and version a decided selector settles on, where that
     decision is apt's version var popping: the clauses registered on the
     version are walked then, and its package var joins the queue *)
  val version_of : name -> version -> (name * version) option

  (* the one live alternative of a clause found unit -- apt's Enqueue is of
     that solution -- as its name, with the package and candidate version it
     stands for where the solution is a version var: an atom neither
     deferred nor matched by a provider, whose package var apt reaches only
     as the version pops *)
  val head : assigned -> atom list -> (name * (name * version) option) option
  val same_name : name -> name -> bool

  (* the literal apt's Pop asserts against a decision it undoes: the
     solution the decision installed, rejected *)
  val negation : assigned -> name -> version -> rejection list

  (* assign rejections derived outside the driver's own propagation, as
     [conflicts] assigns its own: those not already assigned, and not of a
     package the partial solution installs *)
  val assign : assigned -> rejection list -> rejection list
end

module Make (D : DRIVER) : sig
  type t

  val create : unit -> t

  (* PubGrub's [next] hook: sync the trail against the partial solution
     (replaying any backjump as Solver::Pop), push the waves of the newly
     standing decisions -- their unit clauses' targets into apt's
     propagation queue, the rest onto the heap -- then drain the queue
     before answering from the heap *)
  val next : t -> assigned:D.assigned -> (D.name * int) list -> D.name

  (* the version a name undone by a backjump but standing for apt is to be
     decided at again *)
  val kept : t -> D.name -> D.version option

  (* scheduling counters, under PACSHADOW *)
  val report : t -> unit
end
