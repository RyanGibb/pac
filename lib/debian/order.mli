module Make (S : Apt_reject.SEARCH) : sig
  (* the context is the requested packages in the order apt enqueues them *)
  val hooks :
    ( S.Tables.MultiarchDebian.Debian.Reduction.Name.t list,
      S.Tables.MultiarchDebian.Debian.Reduction.Name.t,
      S.Resolver.selection,
      S.PVersion.t )
    Pac_common.Order.driver
end
