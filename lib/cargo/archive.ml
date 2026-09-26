module P = Cargo_parse

(* The index as a run has read it so far.  There is no cone pass: a crate
   is parsed the first time a sub-instance reads its name, as cargo's
   sparse protocol fetches it, so a run touches the crates the solver asks
   about and no others.  Because the instance is still being uncovered, the
   sub-instance a lookup theorem names must be complete at the moment the
   lookup answers.  Each is complete by construction -- name_set,
   support_of_name and repo_preimage load every name they read whole, and
   meta and the owner scan load the owner -- except the one
   versions_lookupLink names.  Its sub-instance is the preimage of the link
   relation at l -- every crate version declaring l -- and no declaration
   of any one crate names the other declarers, so nothing a loaded crate
   carries can bring them in: links_table holds the declarers among the
   names loaded so far, and may grow after CLink l has answered.
   Lookups.pg_versions answers it afresh each time rather than memoizing
   it. *)
type t = {
  index : string;
  crates : (string, P.ver list) Hashtbl.t;
  entry : (string * string, P.ver) Hashtbl.t;
  links_table : (string, (string * string) list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_dropped : int;
  (* wall time inside the parser, which the solve interleaves with *)
  mutable t_parse : float;
}

let empty index =
  {
    index;
    crates = Hashtbl.create 4096;
    entry = Hashtbl.create 65536;
    links_table = Hashtbl.create 256;
    n_names = 0;
    n_vers = 0;
    n_dropped = 0;
    t_parse = 0.;
  }

(* Pre-release versions stay in the index.  The calculus admits one only
   inside a comparator set that names a pre-release at the same release
   core, so no filtering is needed here; yanked versions are dropped by
   the parser instead, which is a repository fact rather than a policy. *)
let load_name ar (n : string) : P.ver list =
  match Hashtbl.find_opt ar.crates n with
  | Some vs -> vs
  | None ->
      let t = Unix.gettimeofday () in
      let vs =
        P.load_crate
          ~reject:(fun () -> ar.n_dropped <- ar.n_dropped + 1)
          ~index:ar.index n
      in
      ar.t_parse <- ar.t_parse +. (Unix.gettimeofday () -. t);
      Hashtbl.replace ar.crates n vs;
      ar.n_names <- ar.n_names + 1;
      ar.n_vers <- ar.n_vers + List.length vs;
      List.iter
        (fun (v : P.ver) ->
          Hashtbl.replace ar.entry (n, v.P.v_vers) v;
          Option.iter
            (fun l -> Pac_common.Tbl.push ar.links_table l (n, v.P.v_vers))
            v.P.v_links)
        vs;
      vs

(* whether the index has a file for the name, yanked versions and all *)
let listed ar n = Sys.file_exists (P.crate_path ~index:ar.index n)
let versions_of ar n = List.map (fun (v : P.ver) -> v.P.v_vers) (load_name ar n)

(* a manifest is read only through its name's load, so a crate version's
   declarations are never taken from a name parsed in part *)
let meta ar n v : P.ver option =
  ignore (load_name ar n);
  Hashtbl.find_opt ar.entry (n, v)

(* the query's root package, a crate version like any other once its name
   has been read: it takes the place of a registry version at its own
   (name, version), which is the one node the model has there *)
let install_root ar (v : P.ver) =
  let n = v.P.v_name and u = v.P.v_vers in
  let vs = List.filter (fun (w : P.ver) -> w.P.v_vers <> u) (load_name ar n) in
  Hashtbl.replace ar.crates n (vs @ [ v ]);
  Hashtbl.replace ar.entry (n, u) v;
  Hashtbl.filter_map_inplace
    (fun _ ps ->
      match List.filter (( <> ) (n, u)) ps with [] -> None | ps -> Some ps)
    ar.links_table;
  Option.iter (fun l -> Pac_common.Tbl.push ar.links_table l (n, u)) v.P.v_links

let link_preimage ar (l : string) = Pac_common.Tbl.find_list ar.links_table l
