exception Failed of string

let fail ~pp_name ~pp_version ~elements f =
  let pkg fmt (n, v) = Format.fprintf fmt "%a %a" pp_name n (pp_version n) v in
  let dependee fmt (n, vs) =
    Format.fprintf fmt "%a {%a}" pp_name n
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         (pp_version n))
      (elements vs)
  in
  let why =
    match f with
    | Pac.CheckSubset p ->
        Format.asprintf "res_subset: %a is not among its name's versions" pkg p
    | Pac.CheckVersionUnique p ->
        Format.asprintf "res_version_unique: %a has another version beside it"
          pkg p
    | Pac.CheckRootMem h ->
        Format.asprintf "res_root_mem: the query's %a is unmet" dependee h
    | Pac.CheckDepClosure (p, h) ->
        Format.asprintf "res_dep_closure: %a's dependee %a is unmet" pkg p
          dependee h
    | Pac.CheckReached p ->
        Format.asprintf "%a is not reached from the root" pkg p
  in
  raise (Failed ("the core answer fails the check, " ^ why))
