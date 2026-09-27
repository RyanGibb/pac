open Place_encoding

(* An occupant's edge, as the extracted edgesOf gives it, with the
   occupants it accepts.  [id] names the accepted set, shared by every
   edge asking the same range of the same package. *)
type edge = {
  e : Npl.coq_Edge;
  acc : Pl.VSet.t;
  accepts : Npl.Occ.t list;
  id : int;
}

type t

(* [optional] false is --omit=optional: an optional dependency is then
   dropped from the instance outright *)
val create : optional:bool -> depth:int -> Archive.t -> string * string -> t
val archive : t -> Archive.t
val depth : t -> int

(* the distinct names whose versions were asked *)
val names_asked : t -> int
val meta : t -> Npl.Occ.t -> Npm_parse.ver option
val edges : t -> Npl.Occ.t -> edge list

(* the registry packages each key has been seen to name, as the manifests
   loaded so far alias them there *)
val key_names : t -> string -> string list
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
  (part * (unit -> T.Dependees.t list)) list option

val dependees : t -> PName.t * PVersion.t -> T.Dependees.t list

(* PAC_NPM_STATS: seconds spent in each named part of the lookups *)
val timed : string -> (unit -> 'a) -> 'a
val print_prof : unit -> unit
