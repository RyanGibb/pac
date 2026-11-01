module Make (Place_encoding : Place_encoding.S) : sig
  open Place_encoding

  (* An occupant's edge as arborist's Edge holds one: its directory, the
     package and range it accepts there (an npm: alias's or a root
     override's), whether it is a peer, and whether nothing need meet it.  A
     node keeps one edge per directory, a dependency over a peer.  It accepts
     only the package it names, unlike npm's satisfiedBy.  [id] names the
     accepted set, shared by edges asking one range of one package. *)
  type edge = {
    e : NpmPlacement.coq_Edge;
    acc : Placement.VSet.t;
    accepts : NpmPlacement.Occupant.t list;
    id : int;
  }

  type t

  val create : depth:int -> Archive.t -> string * string -> t
  val archive : t -> Archive.t
  val depth : t -> int
  val meta : t -> NpmPlacement.Occupant.t -> Npm_parse.ver option
  val edges : t -> NpmPlacement.Occupant.t -> edge list
  val versions : t -> PName.t -> PVersion.t list

  (* what one part of a name's dependees reads, so that the solve converts
     each part once *)
  type part

  (* a root's or an occupant's dependees, in parts; None for a walk's or an
     absent location's *)
  val parts :
    t ->
    PName.t ->
    PVersion.t ->
    (part * (unit -> Reduced.Dependee.t list)) list option

  val dependees : t -> PName.t * PVersion.t -> Reduced.Dependee.t list
end
