type ('name, 'version) t = {
  packages : ('name * 'version) list;
  edges : (('name * 'version) * ('name * 'version list)) list;
}

let walk ~versions ~dependees roots =
  let names = Hashtbl.create 64 in
  let deps = Hashtbl.create 256 in
  let rec reach n =
    if not (Hashtbl.mem names n) then begin
      Hashtbl.replace names n ();
      expand n
    end
  and expand n =
    List.iter
      (fun v ->
        if not (Hashtbl.mem deps (n, v)) then begin
          let ds = dependees (n, v) in
          Hashtbl.replace deps (n, v) ds;
          List.iter (fun (m, _) -> reach m) ds
        end)
      (versions n)
  in
  List.iter reach roots;
  let rec settle () =
    let before = Hashtbl.length deps in
    Hashtbl.iter (fun n () -> expand n) (Hashtbl.copy names);
    if Hashtbl.length deps > before then settle ()
  in
  settle ();
  {
    packages = List.sort compare (Hashtbl.fold (fun p _ l -> p :: l) deps []);
    edges =
      List.sort_uniq compare
        (Hashtbl.fold
           (fun p ds l ->
             List.map (fun (m, vs) -> (p, (m, List.sort_uniq compare vs))) ds
             @ l)
           deps []);
  }

let print ~pp_name ~pp_version c =
  let name = Format.asprintf "%a" pp_name in
  let version = Format.asprintf "%a" pp_version in
  let pkg (n, v) = (name n, version v) in
  let packages = List.sort_uniq compare (List.map pkg c.packages) in
  let edges =
    List.sort_uniq compare
      (List.map
         (fun (p, (m, vs)) ->
           (pkg p, (name m, List.sort_uniq String.compare (List.map version vs))))
         c.edges)
  in
  Printf.printf "core: %d packages, %d edges\n" (List.length packages)
    (List.length edges);
  let from = Hashtbl.create 64 and listed = Hashtbl.create 64 in
  List.iter (fun (p, e) -> Hashtbl.add from p e) edges;
  List.iter
    (fun ((n, v) as p) ->
      Hashtbl.replace listed n ();
      Printf.printf "%s %s\n" n v;
      List.iter
        (fun (m, vs) ->
          Printf.printf "  -> %s {%s}\n" m (String.concat ", " vs))
        (List.sort compare (Hashtbl.find_all from p)))
    packages;
  (* a name with no versions is still reached, and an edge to it can never
     be met, which is worth seeing *)
  List.iter
    (fun m -> if not (Hashtbl.mem listed m) then Printf.printf "%s (none)\n" m)
    (List.sort_uniq String.compare (List.map (fun (_, (m, _)) -> m) edges));
  flush stdout
