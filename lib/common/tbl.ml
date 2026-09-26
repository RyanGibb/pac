let find_list tbl k = Option.value (Hashtbl.find_opt tbl k) ~default:[]
let push tbl k v = Hashtbl.replace tbl k (v :: find_list tbl k)

let memo tbl k f =
  match Hashtbl.find_opt tbl k with
  | Some v -> v
  | None ->
      let v = f () in
      Hashtbl.replace tbl k v;
      v
