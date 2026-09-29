module Make (S : Apt_reject.SEARCH) : sig
  (* the context is the requested packages in the order apt enqueues them *)
  val hooks :
    ( S.T.DMA.Deb.Name.t list,
      S.T.DMA.Deb.Name.t,
      S.PG.selection,
      S.PVersion.t )
    Pac_common.Order.driver
end
