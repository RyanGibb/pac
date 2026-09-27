type cmp = Ge | Gt | Le | Lt | Eq
type arch_qual = Unqual | AnyArch | NativeArch | ExplicitArch of string
type atom = { name : string; aqual : arch_qual; constr : (cmp * string) option }
type provide = { pname : string; pversion : string option }

(* Depends and Recommends are held as the unparsed field text -- Pre-Depends
   then Depends, in that order -- because they hold the bulk of an archive's
   relationship atoms while a lookup reduces a few dozen of its ~69k stanzas.
   Keeping 340k atom records and list cells live in the major heap cost more
   than reading the whole file did; whoever needs a stanza's clauses calls
   parse_depends_fields on them and keeps only those.  Provides are parsed
   here because their reverse table is a preimage that no single stanza's
   clauses can reach. *)
type stanza = {
  package : string;
  version : string;
  architecture : string;
  multi_arch : string option;
  depends_raw : string list;
  (* same syntax as depends (Policy 7.2), and kept apart from it because a
     recommends clause need not be satisfiable for the solve to succeed *)
  recommends_raw : string list;
  provides : provide list;
  (* and Breaks: to apt's solver both only exclude, and they differ in the
     unpack order dpkg keeps, which is no part of a resolution *)
  conflicts : atom list;
  essential : bool;
  (* apt folds Protected into the same flag as Important (deblistparser.cc
     UsePackage), so the two fields are read as one here *)
  important : bool;
  priority : int;
  (* apt's SourcePkgName and SourceVerStr: a Source field naming no version
     leaves the binary's own, and a stanza with none its own name too *)
  source : string * string;
}

val priority_lowest : int
val parse_depends : string -> atom list list
val parse_depends_fields : string list -> atom list list
val parse_file : reject:(unit -> unit) -> string -> stanza list
