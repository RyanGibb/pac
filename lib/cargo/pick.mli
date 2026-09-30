module Make
    (Encoding : Encoding.S)
    (L : module type of Lookups.Make (Encoding)) : sig
  (* cargo's candidate policy over one solve's lookups, and its memos *)
  type t

  val create : L.state -> t

  module Driver (_ : sig
    val pk : t
  end) :
    Order.DRIVER
      with type name = Encoding.Cg.Reduction.NPlus.t
       and type version = Encoding.PVersion.t
       and type selection = Encoding.PG.selection
end
