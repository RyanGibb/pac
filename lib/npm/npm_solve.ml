(* Trusted here (TCB): the parser, the version comparator, the engines
   evaluation (Npm_version.holds_pre), the registry fetch, the policy
   constants in Pick and Order, PubGrub, whose solution is decoded
   unchecked, and the plumbing. *)

module Archive = Archive
module Query = Query
module Solve = Solve
module Print = Print
