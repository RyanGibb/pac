type t = {
  x_range : Npm_version.range;
  x_deps : (string * string) list;
  x_peers : (string * string) list;
  x_meta : (string * bool) list;
}

val of_name : string -> t list

(* Berry's satisfiesWithPrereleases (yarnpkg-core/sources/semverUtils.ts):
   the range with prereleases included, and failing that the version with
   its prerelease tags dropped.  Berry drops the comparators' tags too, but
   node-semver compares a comparator by its text, which keeps them, so
   3.13.0 does not match 3.13.0-next.1. *)
val matches : string -> t -> bool
