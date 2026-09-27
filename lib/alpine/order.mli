module Make (Lk : Lookups.S) : sig
  val hooks :
    ( Lk.archive,
      Lk.PFR.Name.t,
      Lk.PG.selection,
      Lk.PVersion.t )
    Pac_common.Order.driver
end
