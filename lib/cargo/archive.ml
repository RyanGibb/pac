module P = Cargo_parse

(* The index as a run has read it so far.  There is no cone pass: a crate
   is parsed the first time a sub-instance reads its name, as cargo's
   sparse protocol fetches it, so a run touches the crates the solver asks
   about and no others.  Because the instance is still being uncovered, the
   sub-instance a lookup theorem names must be complete at the moment the
   lookup answers.  Each is complete by construction -- name_set,
   support_of_name and repo_preimage load every name they read whole, and
   meta and the owner scan load the owner -- except a links value's: every
   crate version declaring it, which no one crate's declarations name.
   links_table holds the declarers among the names loaded so far, so the
   value's versions may grow after the lookup has answered.  The resolver's
   contract allows that: versions may only grow (versions_link_mono); a
   package's dependees are fixed, and the value's package has none; every
   range onto it is an exact set of listed versions, the singleton of the
   declarer whose edge it is, loaded before its edges are asked. *)
type t = {
  index : string;
  cache : string option;
  crates : (string, P.ver list) Hashtbl.t;
  entry : (string * string, P.ver) Hashtbl.t;
  links_table : (string, (string * string) list) Hashtbl.t;
  mutable n_names : int;
  mutable n_vers : int;
  mutable n_dropped : int;
  mutable n_cached : int;
  (* wall time inside the parser or the cache, which the solve interleaves
     with *)
  mutable t_parse : float;
}

type stats = {
  names : int;
  versions : int;
  dropped : int;
  cached : int;
  parse : float;
}

let stats ar =
  {
    names = ar.n_names;
    versions = ar.n_vers;
    dropped = ar.n_dropped;
    cached = ar.n_cached;
    parse = ar.t_parse;
  }

let empty ?cache index =
  {
    index;
    cache;
    crates = Hashtbl.create 4096;
    entry = Hashtbl.create 65536;
    links_table = Hashtbl.create 256;
    n_names = 0;
    n_vers = 0;
    n_dropped = 0;
    n_cached = 0;
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
      let vs, hit =
        Index_cache.load ~cache:ar.cache
          ~reject:(fun () -> ar.n_dropped <- ar.n_dropped + 1)
          ~index:ar.index n
      in
      if hit then ar.n_cached <- ar.n_cached + 1;
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

let listed ar n = Sys.file_exists (P.crate_path ~index:ar.index n)
let versions_of ar n = List.map (fun (v : P.ver) -> v.P.v_vers) (load_name ar n)

let meta ar n v : P.ver option =
  ignore (load_name ar n);
  Hashtbl.find_opt ar.entry (n, v)

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
