let find_list tbl k = Option.value (Hashtbl.find_opt tbl k) ~default:[]
let push tbl k v = Hashtbl.replace tbl k (v :: find_list tbl k)
