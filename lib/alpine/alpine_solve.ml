module Make () = struct
  open Lookups
  module Lk = Make ()
  include Lk
  module Order = Order.Make (Lk)

  type result = { pkgs : (string * string) list; nodes : int; lookups : int }

  let solve ?(debug = false) ?(order = `Tool) (ar : archive)
      (world : P.dep list) :
      (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit) =
    Pubgrub.set_debug debug;
    let st = lookups ar in
    let touch = touch ar world st in
    let r =
      L.solve st ~touch (Order.hooks order ar)
      |> Result.map (fun (s_pf, nodes) ->
          let pkgs = Alp.PkgSet.elements (Red.alpineResolution s_pf) in
          { pkgs = List.sort compare pkgs; nodes; lookups = L.lookups st })
    in
    (r, fun () -> L.core st ~touch)
end
