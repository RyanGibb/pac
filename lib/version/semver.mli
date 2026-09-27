type t = { major : int; minor : int; patch : int; pre : string list }

(* A component of a partial version, as a range names one: 1.2.x and 1.2
   are not versions but bounds to widen. *)
type comp = Num of int | Star | Absent

(* for test_semver, which tells apart versions differing only in build
   metadata *)
val strip_build : string -> string * string
val num_or : int -> comp -> int
val vstr : ?pre:string -> int -> int -> int -> string

(* The semver crate's reading: a prerelease follows a hyphen and nothing
   else.  Cargo and npm differ only in how a string becomes a version, so
   each reading is a module of its own rather than a flag. *)
module Strict : sig
  val parse : string -> t
  val is_prerelease : string -> bool
  val same_core : string -> string -> bool
  val admits : string -> string list -> bool
  val parse_partial : string -> comp * comp * comp * string
  val top : string -> string
  val compare_parsed : string -> string -> int
  val compare : string -> string -> int
end

(* node-semver's loose reading, which npm passes for every version and
   range it reads. *)
module Loose : sig
  val parse : string -> t
  val is_prerelease : string -> bool
  val same_core : string -> string -> bool
  val admits : string -> string list -> bool
  val parse_partial : string -> comp * comp * comp * string
  val compare : string -> string -> int
end
