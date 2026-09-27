open Place_encoding
module L = Place_lookup

type result = {
  layout : (string list * (string * string)) list;
  nodes : int;
  lookups : int;
  names : int;
}

(* A dependee's versions as runs of the name's own sorted versions rather
   than as one point per version, as the npm reading's runs, found from
   each version's place in the name's list.  A run is closed at its last
   version rather than at the next one in the list: a key's versions grow
   when a manifest aliasing another package to it is loaded, and a run
   reaching up to the next version would then take in whatever was
   inserted before it. *)
type index = {
  list : PVersion.t list;
  arr : PVersion.t array;
  pos : (PVersion.t, int) Hashtbl.t;
}

let index_of tbl (n : PName.t) (all : PVersion.t list) =
  match Hashtbl.find_opt tbl n with
  | Some i when i.list == all -> i
  | _ ->
      let arr = Array.of_list all in
      let pos = Hashtbl.create (Array.length arr) in
      Array.iteri (fun i v -> Hashtbl.replace pos v i) arr;
      let i = { list = all; arr; pos } in
      Hashtbl.replace tbl n i;
      i

let runs (ix : index Lazy.t) (vs : PVersion.t list) : PG.Ranges.t =
  if List.compare_length_with vs 32 <= 0 then PG.Ranges.of_list vs
  else begin
    let ix = Lazy.force ix in
    let close acc lo hi =
      PG.Ranges.union acc
        (PG.Ranges.union
           (PG.Ranges.between ix.arr.(lo) ix.arr.(hi))
           (PG.Ranges.singleton ix.arr.(hi)))
    in
    (* the places of vs, ascending; a version the name does not offer the
       solver never considers *)
    let ps =
      List.sort_uniq Int.compare (List.filter_map (Hashtbl.find_opt ix.pos) vs)
    in
    let rec go acc lo hi = function
      | [] -> close acc lo hi
      | p :: rest when p = hi + 1 -> go acc lo p rest
      | p :: rest -> go (close acc lo hi) p p rest
    in
    match ps with
    | [] -> PG.Ranges.empty
    | p :: rest -> go PG.Ranges.empty p p rest
  end

(* PubGrub widens each dependency's depender range by asking for the
   dependencies of the depender's neighbouring versions, and at a location
   every version of the key is a neighbour, each with the same Tree atom.
   A location's dependees are therefore built from parts each converted
   once. *)
let stats = Array.make_matrix 3 3 0.
let kind = function R.Name.Root -> 0 | R.Name.Loc _ -> 1 | R.Name.Walk _ -> 2

let dependencies st cache =
  let part_cache = Hashtbl.create 65536 in
  let indices = Hashtbl.create 65536 in
  let conv hs =
    List.map
      (fun ((m, vs) : T.Dependees.t) ->
        ( m,
          runs
            (lazy
              (let k =
                 match m with
                 | R.Name.Loc (l, a) when List.length l < L.depth st ->
                     R.Name.Loc ([], a)
                 | _ -> m
               in
               index_of indices k (L.versions st m)))
            (T.VSet.elements vs) ))
      hs
  in
  fun n (u : PVersion.t) ->
    let s = stats.(kind n) in
    s.(0) <- s.(0) +. 1.;
    (* a location's Tree atom reads its parent's key, whose packages grow
       as aliasing manifests load *)
    let g =
      match n with
      | R.Name.Loc (b :: _, _) -> List.length (L.key_names st b)
      | _ -> 0
    in
    Pac_common.Tbl.memo cache (n, u, g) (fun () ->
        let t = Unix.gettimeofday () in
        let r =
          match L.parts st n u with
          | Some ps ->
              List.concat_map
                (fun (k, f) ->
                  Pac_common.Tbl.memo part_cache k (fun () ->
                      let h = f () in
                      L.timed "conv" (fun () -> conv h)))
                ps
          | None -> conv (L.dependees st (n, u))
        in
        s.(1) <- s.(1) +. 1.;
        s.(2) <- s.(2) +. (Unix.gettimeofday () -. t);
        r)

(* PAC_NPM_STATS: where the lookups' time goes, by the kind of name *)
let print_stats () =
  if Sys.getenv_opt "PAC_NPM_STATS" <> None then begin
    L.print_prof ();
    Array.iteri
      (fun i s ->
        Printf.eprintf "dependees %s: %.0f asked, %.0f computed, %.2fs\n"
          [| "root"; "location"; "walk" |].(i)
          s.(0) s.(1) s.(2))
      stats
  end

(* through the soundness decoder, placementResolution *)
let decode st ~lookups sol =
  {
    layout =
      List.sort
        (fun (l, _) (l', _) -> compare (lock_path l) (lock_path l'))
        (List.filter_map
           (fun (l, (a, x)) ->
             match x with
             | Npl.Occ.Reg (m, v) -> Some (a :: l, (m, v.IVer.s))
             | Npl.Occ.Top -> None)
           (Pl.Layout.elements (R.placementResolution (T.PkgSet.ofList sol))));
    nodes = List.length sol;
    lookups;
    names = L.names_asked st;
  }

let rec walk tbl (l : string list) (a : string) =
  if Hashtbl.mem tbl (a :: l) then Some (a :: l)
  else match l with [] -> None | _ :: t -> walk tbl t a

(* npm resolves dev and optional dependencies whatever --omit says, and
   leaves out of what it installs only the packages that every path from
   the root reaches through an omitted edge (calc-dep-flags.js, and
   Node.shouldOmit): here, the occupants reached through the other edges,
   each edge through its walk. *)
let drop ~dev ~optional st r =
  let tbl = Hashtbl.create 256 in
  List.iter
    (fun (l, (m, v)) -> Hashtbl.replace tbl l (Npl.Occ.Reg (m, IVer.make v)))
    r.layout;
  let omitted (x : Npl.Occ.t) (e : Npl.coq_Edge) =
    if e.Npl.e_peer then optional && e.Npl.e_opt
    else
      match L.meta st x with
      | Some m ->
          List.exists
            (fun (d : Npm_parse.dep) ->
              d.Npm_parse.d_dir = e.Npl.e_dir
              && ((dev && d.Npm_parse.d_dev)
                 || (optional && d.Npm_parse.d_optional)))
            m.Npm_parse.v_deps
      | None -> false
  in
  let kept = Hashtbl.create 256 in
  let rec reach l (x : Npl.Occ.t) =
    List.iter
      (fun (ed : L.edge) ->
        let e = ed.L.e in
        if not (omitted x e) then
          match walk tbl l e.Npl.e_dir with
          | Some l' when not (Hashtbl.mem kept l') ->
              Hashtbl.replace kept l' ();
              reach l' (Hashtbl.find tbl l')
          | _ -> ())
      (L.edges st x)
  in
  reach [] Npl.Occ.Top;
  { r with layout = List.filter (fun (l, _) -> Hashtbl.mem kept l) r.layout }

let solve ?(debug = false) ?(order = `Tool) ?(omit_dev = false)
    ?(omit_optional = false) ~depth ar (root : string * string) :
    (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit) =
  Pubgrub.set_debug debug;
  let st = L.create ~depth ar root in
  let h = Place_order.hooks order st in
  let timed a f x =
    let t = Unix.gettimeofday () in
    let r = f x in
    a := !a +. (Unix.gettimeofday () -. t);
    r
  in
  let tv = ref 0. and tn = ref 0. and tc = ref 0. in
  (* each node whose dependencies the solve looked up *)
  let asked = Hashtbl.create 65536 in
  let next =
    Option.map
      (fun f ~assigned o -> timed tn (fun o -> f ~assigned o) o)
      h.Pac_common.Order.next
  and choose =
    Option.map
      (fun f ~assigned n c -> timed tc (fun c -> f ~assigned n c) c)
      h.Pac_common.Order.choose
  in
  let r =
    PG.solve ?next ?choose
      ~vers:(timed tv (L.versions st))
      ~deps:(dependencies st asked)
      [ (R.Name.Root, PG.Ranges.of_list [ R.Version.Occ Npl.Occ.Top ]) ]
  in
  h.Pac_common.Order.finish ();
  print_stats ();
  if Sys.getenv_opt "PAC_NPM_STATS" <> None then
    Printf.eprintf "versions %.2fs, next %.2fs, choose %.2fs\n" !tv !tn !tc;
  let r =
    match r with
    | Error inc ->
        Error
          (fun ppf ->
            Format.fprintf ppf "(within depth %d)@." depth;
            PG.explain_incompatibility ppf inc)
    | Ok sol ->
        let r = decode st ~lookups:(Hashtbl.length asked) sol in
        Ok
          (if omit_dev || omit_optional then
             drop ~dev:omit_dev ~optional:omit_optional st r
           else r)
  in
  let core () =
    match
      Pac_common.Core.walk ~versions:(L.versions st)
        ~dependees:(fun p ->
          List.map
            (fun ((m, vs) : T.Dependees.t) -> (m, T.VSet.elements vs))
            (L.dependees st p))
        [ R.Name.Root ]
    with
    | c -> Pac_common.Core.print ~pp_name:PName.pp ~pp_version:PVersion.pp c
    | exception Archive.Fetch_failed e ->
        Printf.printf "core: incomplete, %s\n%!" e
  in
  (r, core)

let print_layout (r : result) =
  List.map
    (fun (l, (m, v)) -> Printf.sprintf "%s %s@%s" (lock_path l) m v)
    r.layout
