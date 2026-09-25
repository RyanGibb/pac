include Lookups

type result = {
  reals : (string * string) list;
  nodes : int;
  depexts : string list;
}

let solve ?(debug = false) ?(order = `Tool) ?(with_test = false)
    ?(with_doc = false) ?(with_dev_setup = false)
    ?(opam_version = default_opam_version) ar
    (query : (string * Opam_parse.vc) list) : result option =
  Pubgrub.set_debug debug;
  let rho =
    rho
      {
        names = List.map fst query;
        with_test;
        with_doc;
        with_dev_setup;
        opam_version;
      }
  in
  let st = lookups rho ar in
  let touch = touch rho ar query st in
  let next = Order.next order ar query st ~touch in
  match L.solve st ~touch ~next () with
  | None -> None
  | Some (s_pf, nodes) ->
      (* the package formula's packages decode to opam's through the second
         of the two layers the reduction composes *)
      let reals = List.sort compare (Op.PkgSet.elements (Red.decodeS s_pf)) in
      Some { reals; nodes; depexts = depexts_of rho ar reals }
