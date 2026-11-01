val hooks :
  ( Lookups.archive
    * (string * Opam_parse.vc) list
    * Lookups.FormulaLookups.t
    * (Lookups.Reduced.Package.t -> unit),
    Lookups.PackageFormulaReduction.Name.t,
    Lookups.Resolver.selection,
    Lookups.PVersion.t )
  Pac_common.Order.driver
