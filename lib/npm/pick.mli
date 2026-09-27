open Encoding

val pick : Archive.t -> string -> PVersion.t list -> PVersion.t

(* npm's pick for a range over every published version of a name *)
val pick_in : Lookup.t -> string -> Np.coq_Range -> string option
