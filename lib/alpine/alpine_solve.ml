type stats = Lookups.stats = {
  names : int;
  versions : int;
  provides : int;
  install_ifs : int;
  dropped : int;
}

module Make () = struct
  open Lookups
  module Lookups = Make ()
  include Lookups
  module Order = Order.Make (Lookups)

  type result = { pkgs : (string * string) list; nodes : int; lookups : int }

  let solve ?(debug = false) ?(check = false) ?(order = `Tool) (ar : archive)
      (world : Apk_parse.dep list) :
      (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit) =
    Pubgrub.set_debug debug;
    let st = lookups ar in
    let touch = touch ar world st in
    let r =
      FormulaLookups.solve st ~check ~touch (Order.hooks order ar)
      |> Result.map (fun (s_pf, nodes) ->
          let pkgs =
            Alpine.PackageSet.elements (Reduction.alpineResolution s_pf)
          in
          {
            pkgs = List.sort compare pkgs;
            nodes;
            lookups = FormulaLookups.lookups st;
          })
    in
    (r, fun () -> FormulaLookups.core st ~touch)
end
