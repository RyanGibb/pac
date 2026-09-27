type stats = Lookups.stats = {
  names : int;
  versions : int;
  provides : int;
  install_ifs : int;
  dropped : int;
}

module Make () : sig
  type archive
  type result = { pkgs : (string * string) list; nodes : int; lookups : int }

  val load_index : string -> archive
  val stats : archive -> stats
  val no_such_package : archive -> Apk_parse.dep list -> string list

  val solve :
    ?debug:bool ->
    ?order:Pac_common.Order.t ->
    archive ->
    Apk_parse.dep list ->
    (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit)
end
