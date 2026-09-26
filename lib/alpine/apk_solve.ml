include Lookups

type result = { pkgs : (string * string) list; nodes : int; processed : int }

let solve ?(debug = false) ?(order = `Tool) (ar : archive) (world : P.dep list)
    : (result, Pac_common.Report.explanation) Stdlib.result =
  Pubgrub.set_debug debug;
  let st = lookups ar in
  L.solve st ~touch:(touch ar world st) (Order.hooks order ar)
  |> Result.map (fun (s_pf, nodes) ->
      let pkgs = Alp.PkgSet.elements (Red.alpineResolution s_pf) in
      { pkgs = List.sort compare pkgs; nodes; processed = L.processed st })

(* A goal argument is an /etc/apk/world line: a dependency atom.  apk
   refuses the whole world over an atom it cannot parse, one whose version
   is not a version, or one tagged with a repository it lacks -- and no
   repository here is tagged -- and skips an empty one. *)
let world_of_args (args : string list) : (P.dep list, string) Stdlib.result =
  let rec go acc = function
    | [] -> Ok (List.rev acc)
    | "" :: rest -> go acc rest
    | a :: rest -> (
        match P.parse_atom a with
        | Some (d, true) -> go (d :: acc) rest
        | Some (_, false) -> Error (Printf.sprintf "%S: not a valid version" a)
        | None when String.contains a '@' ->
            Error (Printf.sprintf "%S: no repository has that tag" a)
        | None -> Error (Printf.sprintf "%S: not a dependency atom" a))
  in
  go [] args
