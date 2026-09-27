type t = Version.Semver.t = {
  major : int;
  minor : int;
  patch : int;
  pre : string list;
}

val parse : string -> t
val compare : string -> string -> int

(* [compare] off the parsed versions, without its string fast path; only
   test_cargo_version asks, to check the two agree *)
val compare_parsed : string -> string -> int
val is_prerelease : string -> bool
val same_core : string -> string -> bool

type op = Ge | Gt | Le | Lt | Eq

(* a conjunction; [] is any version *)
type req = (op * string) list

val comparator : string -> req
val parse_req : string -> req
val holds : string -> req -> bool

(* for test_cargo_version's failure messages alone *)
val string_of_req : req -> string

(* VersionReq::from_str of the semver crate cargo 1.97 links.  The index
   is cargo-validated, so this runs on the root alone; without it
   parse_req would read a malformed requirement as "*".
   Stricter than parse_req: no "==", a wildcard only in trailing
   components or as the whole requirement, no leading zeros, and a comma
   between comparators. *)
val req_ok : string -> bool

(* Version::from_str of the semver crate *)
val version_ok : string -> bool

(* PartialVersion::from_str (cargo-util-schemas): a whole semver version,
   or one to three numbers read as a caret requirement written without its
   '^'.  A rust-version is one with neither prerelease nor build
   (RustVersion::try_from); the toolchain rustc reports may carry either. *)
val partial_ok : rust:bool -> string -> bool
