(* A shadow of apt's Solver::Work heap (apt-pkg/solver3.cc), driven by a
   PubGrub search rather than by apt: work items are the driver's clause
   gadgets, pushed in the propagation waves of the decisions that stand,
   popped to answer PubGrub's [next] hook, and re-added level by level when
   PubGrub backjumps, which is apt's Solver::Pop.  What the shadow knows of
   the instance it schedules is the [DRIVER] below and nothing else. *)

(* The split apt makes between what it unit-propagates (Enqueue) and what it
   queues as a work item, seen through the gadget names of the encoding. *)
type kind =
  (* a guard: apt never queues one *)
  | Forced
  (* a real package name: apt enqueues the package var *)
  | Package
  (* a clause gadget whose Clause carries eager = true *)
  | Hard
  (* an optional (Recommends) clause gadget *)
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
     whole instance respectively *)
  val atom_count : assigned -> atom -> int
  val atom_static : atom -> int

  (* the value the partial solution has decided [name] at, if any *)
  val decided : assigned -> name -> version option
  val version_equal : version -> version -> bool

  (* the propagation wave a standing decision sets off: the decided
     package's clauses in control-file order, each as its optional flag, the
     work item it contributes (none where the whole chain is forced, which
     is apt's Enqueue) and its alternatives *)
  val wave : name -> version -> (bool * name option * atom list) list

  (* the name a clause decided to one of its alternatives leaves pending:
     the same step of apt's, half-done *)
  val continuation : name -> version -> name option

  (* the ingredients of the fallback key, used only where the heap has
     nothing to offer: apt's rank group, and the name's candidate count *)
  val fallback_key : name -> int * int
end

module Make (D : DRIVER) : sig
  type t

  val create : unit -> t

  (* first sighting of a name, standing in for apt's propagation queue
     order; the caller stamps a decided package's clause targets in field
     order, which is the order apt enqueues them *)
  val discover : t -> D.name -> unit

  (* PubGrub's [next] hook: sync the trail against the partial solution
     (replaying any backjump as Solver::Pop), push the waves of the newly
     standing decisions, then answer from the heap *)
  val next : t -> assigned:D.assigned -> (D.name * int) list -> D.name

  (* scheduling counters, under PACSHADOW *)
  val report : t -> unit
end
