module Make (S : Apt_reject.SEARCH) : sig
  val hooks :
    ( unit,
      S.T.DMA.Deb.Name.t,
      S.PG.selection,
      S.PVersion.t )
    Pac_common.Order.driver
end
