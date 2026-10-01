type ('name, 'version) failure =
  | Subset of ('name * 'version)
  | Version_unique of ('name * 'version)
  | Root_mem of ('name * 'version list)
  | Dep_closure of ('name * 'version) * ('name * 'version list)
  | Reached of ('name * 'version)

exception Failed of string

let fail ~pp_name ~pp_version f =
  let pkg fmt (n, v) = Format.fprintf fmt "%a %a" pp_name n (pp_version n) v in
  let dependee fmt (n, vs) =
    Format.fprintf fmt "%a {%a}" pp_name n
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         (pp_version n))
      vs
  in
  let why =
    match f with
    | Subset p ->
        Format.asprintf "res_subset: %a is not among its name's versions" pkg p
    | Version_unique p ->
        Format.asprintf "res_version_unique: %a has another version beside it"
          pkg p
    | Root_mem h ->
        Format.asprintf "res_root_mem: the query's %a is unmet" dependee h
    | Dep_closure (p, h) ->
        Format.asprintf "res_dep_closure: %a's dependee %a is unmet" pkg p
          dependee h
    | Reached p -> Format.asprintf "%a is not reached from the root" pkg p
  in
  raise (Failed ("the core answer fails the check, " ^ why))
