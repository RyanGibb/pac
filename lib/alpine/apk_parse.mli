type constr = Any | Op of Apk_version.op * string
type dep = { d_neg : bool; d_name : string; d_constr : constr }

(* A versioned provides is one apk treats as a real package of the
   provided name; a bare one offers the empty version, below every
   version, and claims no name. *)
type prov = { p_name : string; p_ver : string option }

type pkg = {
  name : string;
  version : string;
  depends : dep list;
  provides : prov list;
  install_if : dep list;
  priority : int option;
}

val parse_file :
  reject:(unit -> unit) -> broken:(string list -> unit) -> string -> pkg list

(* A goal argument is an /etc/apk/world line: a dependency atom.  apk
   refuses the whole world over an atom it cannot parse, one whose version
   is not a version, or one tagged with a repository it lacks -- and no
   repository here is tagged -- and skips an empty one. *)
val world_of_args : string list -> (dep list, string) result
