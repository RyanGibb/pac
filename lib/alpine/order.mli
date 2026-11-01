module Make (Lk : Lookups.S) : sig
  val hooks :
    ( Lk.archive,
      Lk.PackageFormulaReduction.Name.t,
      Lk.Resolver.selection,
      Lk.PVersion.t )
    Pac_common.Order.driver
end
