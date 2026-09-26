module S = Solve

let node n v = if v = "" then n else Printf.sprintf "%s %s" n v

let show (a, t) v =
  if a = t then node t v else Printf.sprintf "%s at %s" (node t v) a

let root (n, v) = node n v
let packages (r : S.result) = List.map (fun (k, v) -> show k v) r.S.installs

let tree (r : S.result) =
  List.map
    (fun ((ck, cv), (pk, pv)) ->
      Printf.sprintf "%s <- %s" (show pk pv) (show ck cv))
    r.S.tree
