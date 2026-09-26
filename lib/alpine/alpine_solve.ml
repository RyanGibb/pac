include Lookups

type result = { pkgs : (string * string) list; nodes : int; lookups : int }

let solve ?(debug = false) ?(order = `Tool) (ar : archive) (world : P.dep list)
    : (result, Pac_common.Report.explanation) Stdlib.result =
  Pubgrub.set_debug debug;
  let st = lookups ar in
  L.solve st ~touch:(touch ar world st) (Order.hooks order ar)
  |> Result.map (fun (s_pf, nodes) ->
      let pkgs = Alp.PkgSet.elements (Red.alpineResolution s_pf) in
      { pkgs = List.sort compare pkgs; nodes; lookups = L.lookups st })
