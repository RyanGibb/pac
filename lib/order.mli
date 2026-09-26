type t = [ `Tool | `Pubgrub | `Random of int ]

(* PubGrub's next and choose hooks, [None] where PubGrub keeps its own.
   [finish] runs once the solve returns, for a driver's diagnostics. *)
type ('name, 'selection, 'version) hooks = {
  next : (assigned:('name -> 'selection) -> ('name * int) list -> 'name) option;
  choose :
    (assigned:('name -> 'selection) -> 'name -> 'version list -> 'version)
    option;
  finish : unit -> unit;
}

(* The type every lib/<eco>/order.ml gives its [hooks]: the context is what
   that driver's tool order reads, and [`Random seed] is always [random]. *)
type ('ctx, 'name, 'selection, 'version) driver =
  t -> 'ctx -> ('name, 'selection, 'version) hooks

val make :
  ?next:(assigned:('name -> 'selection) -> ('name * int) list -> 'name) ->
  ?choose:(assigned:('name -> 'selection) -> 'name -> 'version list -> 'version) ->
  ?finish:(unit -> unit) ->
  unit ->
  ('name, 'selection, 'version) hooks

(* Every open name and every candidate is a sound pick, so a uniform one
   exercises answers neither ordered search reaches. *)
val random : int -> ('name, 'selection, 'version) hooks

(* The first of the greatest, which is PubGrub's own choice. *)
val greatest : ('v -> 'v -> int) -> 'v list -> 'v
