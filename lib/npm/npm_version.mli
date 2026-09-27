val compare : string -> string -> int
val is_prerelease : string -> bool
val release : string -> string
val same_core : string -> string -> bool

type op = Ge | Gt | Le | Lt | Eq
type comparator = Any | Cmp of op * string
type range = comparator list list

(* None where node-semver's Range refuses the string, every set having
   been thrown out, and npa then reads the spec as a dist-tag.
   include_prerelease reads the range as semver's includePrerelease does,
   for [holds_pre]. *)
val parse_range_opt : ?include_prerelease:bool -> string -> range option

(* satisfies catches the TypeError of a range semver refuses and answers
   false, so such a range, with no set at all, matches nothing *)
val parse_range : ?include_prerelease:bool -> string -> range

(* for testing the grammar from OCaml: a dependency range is evaluated
   against the real version set by the calculus, not here *)
val holds : string -> range -> bool

(* semver's includePrerelease, which checkEngine passes and a dependency
   range never does: cs_admits is dropped, so a prerelease version is
   ordered by an ordinary comparator rather than refused by one that
   names no prerelease.  It matters only for a prerelease host -- an
   engines range is matched against the running node or npm, not against
   a published version -- and the range must be parsed with
   ~include_prerelease for its -0 bounds. *)
val holds_pre : string -> range -> bool
val string_of_range : range -> string
