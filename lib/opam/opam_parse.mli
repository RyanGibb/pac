type op = Ge | Gt | Le | Lt | Eq | Ne

type filt =
  | FT
  | FF
  | FCmp of op * string * string (* op, variable, constant *)
  | FDef of string
  | FAnd of filt * filt
  | FOr of filt * filt
  | FNot of filt

type vc = VTop | VCmp of op * string | VAnd of vc * vc | VOr of vc * vc
type off = OAtom of string * filt * vc | OAnd of off * off | OOr of off * off

type pkg_meta = {
  depends : off option;
  conflicts : (string * (filt * vc)) list;
  classes : string list;
  available : filt;
  depexts : (string * filt) list;
  pindeps : ((string * string) * string) list;
  (* opam 2.1's avoid-version and 2.2's deprecated: "select this version
     only if nothing else works".  Not a constraint -- a flagged version
     stays installable -- so they are recorded here and spent on solver
     preference, never on the declarations. *)
  avoid_version : bool;
  deprecated : bool;
}

val empty_meta : pkg_meta
val off_names : string list -> off -> string list
val string_of_op : op -> string
val query_of_args : string list -> ((string * vc) list, string) result

val parse_file :
  reject:(unit -> unit) -> name:string -> version:string -> string -> pkg_meta
