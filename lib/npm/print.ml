open Encoding
module A = Archive
module S = Solve

let node n v = if v = "" then n else Printf.sprintf "%s %s" n v

let show (a, t) v =
  if a = t then node t v else Printf.sprintf "%s at %s" (node t v) a

let root (n, v) = Printf.printf "root %s\n%!" (node n v)

let unsat inc =
  Format.printf "unsatisfiable:@.%a@." PG.explain_incompatibility inc

let tree ~full (r : S.result) =
  if full then begin
    Printf.printf "node_modules (%d edges):\n" (List.length r.S.tree);
    List.iter
      (fun ((ck, cv), (pk, pv)) ->
        Printf.printf "  %s <- %s\n" (show pk pv) (show ck cv))
      r.S.tree
  end
  else Printf.printf "node_modules edges: %d\n" (List.length r.S.tree)

(* the packuments the run read, known only once it is over: there is no
   cone, so this is what the solver asked for and nothing more *)
let stats ar (r : S.result) =
  Printf.printf "loaded: %d packages, %d versions, %d packuments fetched\n"
    ar.A.n_names ar.A.n_vers ar.A.n_fetched;
  if !Npm_parse.rejected > 0 then
    Printf.printf "parser dropped %d declarations\n" !Npm_parse.rejected;
  if r.S.optional_read > 0 then
    Printf.printf
      "optionalDependencies: %d of %d distinct (target, range) pairs dropped\n"
      r.S.optional_dropped r.S.optional_read;
  Printf.printf "encoded solution: %d core nodes (%d lookups)\n" r.S.nodes
    r.S.lookups

let answer ~full ~elapsed ar (r : S.result) =
  Printf.printf "packages (%d):\n" (List.length r.S.installs);
  List.iter (fun (k, v) -> Printf.printf "  %s\n" (show k v)) r.S.installs;
  tree ~full r;
  stats ar r;
  Printf.printf "solve %.2fs\n" elapsed
