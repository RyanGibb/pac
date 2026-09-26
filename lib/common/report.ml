type explanation = Format.formatter -> unit

type loaded = {
  names : int;
  versions : int;
  extra : string list;
  dropped : int;
  parse : float;
}

let root s = Printf.printf "root %s\n%!" s

let section title rows =
  Printf.printf "%s (%d):\n" title (List.length rows);
  List.iter (Printf.printf "  %s\n") rows

let packages = section "packages"

let encoded ~nodes ~lookups =
  Printf.printf "encoded solution: %d core nodes (%d lookups)\n" nodes lookups

let unsatisfiable (why : explanation) = Format.printf "unsatisfiable:@.%t@." why

let loaded l ~solve =
  Printf.printf "loaded: %s\n"
    (String.concat ", "
       (Printf.sprintf "%d names" l.names
       :: Printf.sprintf "%d versions" l.versions
       :: l.extra));
  if l.dropped > 0 then
    Printf.printf "parser dropped %d declarations\n" l.dropped;
  Printf.printf "parse %.2fs\nsolve %.2fs\n" l.parse solve
