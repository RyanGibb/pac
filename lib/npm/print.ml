let node n v = if v = "" then n else Printf.sprintf "%s %s" n v

let show (a, t) v =
  if a = t then node t v else Printf.sprintf "%s at %s" (node t v) a

let root (n, v) = node n v

let packages (r : Solve.result) =
  List.map (fun (k, v) -> show k v) r.Solve.installs

let tree (r : Solve.result) =
  List.map
    (fun ((ck, cv), (pk, pv)) ->
      Printf.sprintf "%s <- %s" (show pk pv) (show ck cv))
    r.Solve.tree
