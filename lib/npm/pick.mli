open Encoding

val pick : Archive.t -> string -> PVersion.t list -> PVersion.t

(* npm's pick for a range over every published version, under the root's
   flat override as the calculus reads one *)
val pick_in : Lookup.t -> string -> Np.coq_Range -> string option
