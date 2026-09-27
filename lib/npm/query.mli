(* The query is a root package: a project's package.json with the
   arguments of `npm install` added to it.  An argument is read as
   npm-package-arg 13.0.2 (npm 11.17.0) reads it, lib/npa.js, and only its
   registry forms are accepted: name, name@version, name@range, name@tag
   and key@npm:name@range.  Anything npa reads as a file, directory, URL or
   git spec is refused rather than dropped, because a query missing one of
   its arguments asks a different question. *)
val root : Archive.t -> string list -> (Npm_parse.ver, string) result
