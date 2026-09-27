(* cargo's candidate policy over one solve's lookups, and its memos *)
type t

val create : Lookups.state -> t

module Driver (_ : sig
  val pk : t
end) :
  Order.DRIVER
    with type name = Encoding.Cg.NPlus.t
     and type version = Encoding.PVersion.t
     and type selection = Encoding.PG.selection
