include Lookups

(* OpamSolution.sanitize_atom_list as opam install runs it, permissively: a
   name matches regardless of case when it matches one name alone
   (fuzzy_name), and an atom no version meets, available or not, is refused
   with not_found_message's words *)
let sanitize ar (query : (string * Opam_parse.vc) list) =
  let names = lazy (Sys.readdir (Filename.concat ar.root "packages")) in
  let fuzzy name =
    let l = String.lowercase_ascii name in
    match
      List.filter
        (fun n -> String.lowercase_ascii n = l && versions_of ar n <> [])
        (Array.to_list (Lazy.force names))
    with
    | [ n ] -> n
    | _ -> name
  in
  let rec go acc = function
    | [] -> Ok (List.rev acc)
    | (name, c) :: rest -> (
        let name = fuzzy name in
        let vs = versions_of ar name in
        if List.exists (Op.vcHolds (xvc c)) vs then go ((name, c) :: acc) rest
        else
          match c with
          | Opam_parse.VCmp (o, w) when vs <> [] ->
              Error
                (Printf.sprintf "Package %s has no version %s%s." name
                   (if o = Opam_parse.Eq then "" else Opam_parse.string_of_op o)
                   w)
          | _ -> Error (Printf.sprintf "No package named %s found." name))
  in
  go [] query

type result = {
  reals : (string * string) list;
  nodes : int;
  lookups : int;
  depexts : string list;
}

let solve ?(debug = false) ?(order = `Tool) ?(with_test = false)
    ?(with_doc = false) ?(with_dev_setup = false)
    ?(opam_version = default_opam_version) ar
    (query : (string * Opam_parse.vc) list) :
    (result, Pac_common.Report.explanation) Stdlib.result =
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
  L.solve st ~touch (Order.hooks order (ar, query, st, touch))
  |> Result.map (fun (s_pf, nodes) ->
      (* the package formula's packages decode to opam's through the
            second of the two layers the reduction composes *)
      let reals =
        List.sort compare (Op.PkgSet.elements (Red.opamResolution s_pf))
      in
      {
        reals;
        nodes;
        lookups = L.lookups st;
        depexts = depexts_of rho ar reals;
      })
