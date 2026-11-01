val hooks :
  ( Lookups.archive
    * (string * Opam_parse.vc) list
    * Lookups.L.t
    * (Lookups.T.Package.t -> unit),
    Lookups.PFR.Name.t,
    Lookups.PG.selection,
    Lookups.PVersion.t )
  Pac_common.Order.driver
