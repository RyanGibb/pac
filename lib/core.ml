let show pp x = Format.asprintf "%a" pp x

type walk = {
  names : string list;
  pkgs : ((string * string) * (string * string list) list) list;
}

let walk ~pp_name ~pp_version ~versions ~dependees roots =
  let names = Hashtbl.create 64 in
  let edges = Hashtbl.create 256 in
  let rec reach n =
    let k = show pp_name n in
    if not (Hashtbl.mem names k) then begin
      Hashtbl.replace names k n;
      expand n
    end
  and expand n =
    List.iter
      (fun v ->
        let p = (show pp_name n, show pp_version v) in
        if not (Hashtbl.mem edges p) then begin
          let ds = dependees (n, v) in
          Hashtbl.replace edges p
            (List.sort compare
               (List.map
                  (fun (m, vs) ->
                    ( show pp_name m,
                      List.sort_uniq String.compare
                        (List.map (show pp_version) vs) ))
                  ds));
          List.iter (fun (m, _) -> reach m) ds
        end)
      (versions n)
  in
  List.iter reach roots;
  let rec settle () =
    let before = Hashtbl.length edges in
    Hashtbl.iter (fun _ n -> expand n) (Hashtbl.copy names);
    if Hashtbl.length edges > before then settle ()
  in
  settle ();
  {
    names =
      List.sort String.compare (Hashtbl.fold (fun k _ l -> k :: l) names []);
    pkgs =
      List.sort compare (Hashtbl.fold (fun p es l -> (p, es) :: l) edges []);
  }

let output w =
  let n_edges = List.fold_left (fun n (_, es) -> n + List.length es) 0 w.pkgs in
  Printf.printf "core: %d packages, %d edges\n" (List.length w.pkgs) n_edges;
  let listed = Hashtbl.create 64 in
  List.iter
    (fun ((n, v), es) ->
      Hashtbl.replace listed n ();
      Printf.printf "%s %s\n" n v;
      List.iter
        (fun (m, vs) ->
          Printf.printf "  -> %s {%s}\n" m (String.concat ", " vs))
        es)
    w.pkgs;
  (* a name with no versions is still reached, and an edge to it can never
     be met, which is worth seeing *)
  List.iter
    (fun n -> if not (Hashtbl.mem listed n) then Printf.printf "%s (none)\n" n)
    w.names;
  flush stdout

let print ~pp_name ~pp_version ~versions ~dependees roots =
  output (walk ~pp_name ~pp_version ~versions ~dependees roots)
