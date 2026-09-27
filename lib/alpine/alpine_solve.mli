module Make () : sig
  type iif_rule = {
    pkg : string * string;
    conds : Lookups.Alp.CondSet.t;
    designation : Lookups.Alp.Atom.t;
  }

  type archive = {
    by_name : (string, Apk_parse.pkg list) Hashtbl.t;
    meta : (string * string, Apk_parse.pkg) Hashtbl.t;
    providers : (string, ((string * string) * string option) list) Hashtbl.t;
    iif_by_cond : (string, iif_rule list) Hashtbl.t;
    prio : (string * string, int) Hashtbl.t;
    pos : (string * string, int) Hashtbl.t;
    mutable n_pkgs : int;
    mutable n_provs : int;
    mutable n_iif : int;
    n_dropped : int;
    uninstallable : (string, unit) Hashtbl.t;
  }

  type result = { pkgs : (string * string) list; nodes : int; lookups : int }

  val load_index : string -> archive
  val no_such_package : archive -> Apk_parse.dep list -> string list

  val solve :
    ?debug:bool ->
    ?order:Pac_common.Order.t ->
    archive ->
    Apk_parse.dep list ->
    (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit)
end
