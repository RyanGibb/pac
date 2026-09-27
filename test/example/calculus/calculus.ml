module Core = Pac_common.Core
module Order = Pac_common.Order

module PG =
  Pubgrub.Make
    (struct
      type t = string

      let compare = String.compare
      let pp = Format.pp_print_string
    end)
    (struct
      type t = int

      let compare = Int.compare
      let pp = Format.pp_print_int
    end)

let fig1 =
  {
    Core.packages =
      [ ("A", 1); ("B", 1); ("C", 1); ("D", 1); ("D", 2); ("D", 3) ];
    edges =
      [
        (("A", 1), ("B", [ 1 ]));
        (("A", 1), ("C", [ 1 ]));
        (("B", 1), ("D", [ 1; 2 ]));
        (("C", 1), ("D", [ 2; 3 ]));
      ];
  }

let extended =
  {
    Core.packages = fig1.packages @ [ ("E", 1) ];
    edges =
      fig1.edges @ [ (("D", 3), ("E", [ 1 ])); (("E", 1), ("D", [ 1; 2 ])) ];
  }

let missing =
  { fig1 with packages = List.filter (( <> ) ("D", 2)) fig1.packages }

(* the first open name in this list, so that D is reached while 3 is still
   one of its candidates *)
let order = [ "D"; "E"; "C"; "B"; "A" ]

let replace_all ~sub ~by s =
  let n = String.length sub and b = Buffer.create (String.length s) in
  let rec go i =
    if i > String.length s - n then
      Buffer.add_substring b s i (String.length s - i)
    else if String.sub s i n = sub then (
      Buffer.add_string b by;
      go (i + n))
    else (
      Buffer.add_char b s.[i];
      go (i + 1))
  in
  go 0;
  Buffer.contents b

(* The debug trace prints an incompatibility with its whole derivation, on
   every line that mentions it, so each is named I1, I2, ... on the line
   that introduces it, and the name stands for it from then on. *)
let abbreviate trace =
  let named = ref [] in
  let short s =
    List.fold_left (fun s (inc, l) -> replace_all ~sub:inc ~by:l s) s !named
  in
  let intro =
    [ "\t"; "prior cause "; "no versions found, adding incompatiblity " ]
  in
  List.iter
    (fun line ->
      match
        List.find_opt (fun p -> String.starts_with ~prefix:p line) intro
      with
      | Some p ->
          let inc =
            String.sub line (String.length p)
              (String.length line - String.length p)
          in
          let l = Printf.sprintf "I%d" (List.length !named + 1) in
          Printf.printf "%s%s = %s\n" p l (short inc);
          named := (inc, l) :: !named
      | None -> print_endline (short line))
    (String.split_on_char '\n' (String.trim trace))

let solve (h : _ Order.hooks) (i : _ Core.t) =
  Core.print ~pp_name:Format.pp_print_string ~pp_version:Format.pp_print_int i;
  let at k l =
    List.filter_map (fun (j, x) -> if j = k then Some x else None) l
  in
  let trace = Buffer.create 4096
  and out = Format.pp_get_formatter_out_functions Format.std_formatter () in
  Format.pp_set_formatter_output_functions Format.std_formatter
    (Buffer.add_substring trace)
    ignore;
  Pubgrub.set_debug true;
  let r =
    PG.solve ?next:h.next ?choose:h.choose
      ~vers:(fun n -> at n i.packages)
      ~deps:(fun n v ->
        List.map (fun (m, vs) -> (m, PG.Ranges.of_list vs)) (at (n, v) i.edges))
      [ ("A", PG.Ranges.of_list [ 1 ]) ]
  in
  Pubgrub.set_debug false;
  Format.pp_set_formatter_out_functions Format.std_formatter out;
  abbreviate (Buffer.contents trace);
  match r with
  | Ok sol -> List.iter (fun (n, v) -> Format.printf "%s %d@." n v) sol
  | Error inc -> Format.printf "%a@." PG.explain_incompatibility inc

let () =
  match Sys.argv with
  | [| _; "extended" |] ->
      solve
        (Order.make
           ~next:(fun ~assigned:_ open_names ->
             List.find (fun n -> List.mem_assoc n open_names) order)
           ~choose:(fun ~assigned:_ _ vs -> Order.greatest Int.compare vs)
           ())
        extended
  | [| _; "missing" |] -> solve (Order.make ()) missing
  | _ -> invalid_arg "calculus (extended | missing)"
