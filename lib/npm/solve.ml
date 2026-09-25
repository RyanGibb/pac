open Encoding
module P = Npm_parse

(* Tool replays npm's own order (Order); Pubgrub leaves PubGrub's
   heuristics, next and choose both, as they are. *)
type order = Tool | Pubgrub

type result = {
  installs : ((string * string) * string) list;
  tree : (((string * string) * string) * ((string * string) * string)) list;
  nodes : int;
  lookups : int;
  (* distinct (target, range) pairs the optional-dependency test read, and
     how many of them no published version matches *)
  optional_read : int;
  optional_dropped : int;
}

(* A dependee's versions as runs of the name's own sorted versions rather
   than as one point per version.  The solver tests every version of a name
   against its range on each assignment and each decision, and a union of
   points costs a comparison per point, so a wide name under "*" -- 2364
   versions of @types/node -- made each test quadratic, and that was most
   of the solve time of a seven-node goal.  A run [lo, next) holds exactly
   the same versions of this name, and the solver considers no others.  A
   few points cost less than asking for the name's versions, which the
   solver may never need. *)
let runs (all : PVersion.t list Lazy.t) (vs : PVersion.t list) : PG.Ranges.t =
  if List.compare_length_with vs 32 <= 0 then PG.Ranges.of_list vs
  else begin
    let inside = Hashtbl.create (List.length vs) in
    List.iter (fun v -> Hashtbl.replace inside v ()) vs;
    let close acc = function
      | Some l -> PG.Ranges.union acc (PG.Ranges.higher_than l)
      | None -> acc
    in
    let rec go acc lo = function
      | [] -> close acc lo
      | v :: rest when Hashtbl.mem inside v ->
          go acc (if lo = None then Some v else lo) rest
      | v :: rest -> (
          match lo with
          | Some l -> go (PG.Ranges.union acc (PG.Ranges.between l v)) None rest
          | None -> go acc None rest)
    in
    go PG.Ranges.empty None (Lazy.force all)
  end

(* PubGrub widens each dependency's depender range by asking for the
   dependencies of the depender's neighbouring versions, once per
   dependency, so the same node is asked for over and over *)
let dependencies st =
  let cache = Hashtbl.create 65536 in
  fun n (u : Np.Vs.version) ->
    Lookup.memo cache (n, u) (fun () ->
        List.map
          (fun ((m, vs) : T.Dependees.t) ->
            (m, runs (lazy (Lookup.versions st m)) (T.VSet.elements vs)))
          (Lookup.dependees st (n, u)))

let hooks order st =
  match order with
  | Pubgrub -> (None, None)
  | Tool ->
      let o = Order.create st in
      (Some (Order.next o), Some (Order.choose o))

let decode st sol =
  let s = T.PkgSet.ofList sol in
  let read, dropped = Lookup.optional_verdicts st in
  {
    installs = List.sort compare (Np.PkgSet.elements (R.npmResolution s));
    tree = List.sort compare (Np.Conc.ParentRel.elements (R.npmParents s));
    nodes = List.length sol;
    lookups = st.Lookup.n_lookups;
    optional_read = read;
    optional_dropped = dropped;
  }

(* npm resolves dev dependencies whatever --omit says, and leaves out of
   what it installs only the packages that dev edges alone reach
   (calc-dep-flags.js), so a dev dependency still shapes the versions the
   rest gets.  A package reaches its depender's directory either as one of
   its dependencies or as the peer of one, so a copy at the root is kept
   when the root depends on it outside devDependencies, peers on it
   itself, or holds a kept copy that peers on it; below the root, a kept
   copy keeps all it holds. *)
let kept_without_dev ar (root : string * string) r =
  let top = ((fst root, fst root), snd root) in
  let held = Hashtbl.create 64 in
  List.iter (fun (c, p) -> Hashtbl.add held p c) r.tree;
  let at_top = Hashtbl.find_all held top in
  let peers_on ((k, v) : (string * string) * string) a =
    match Archive.meta ar (snd k, v) with
    | Some m -> List.exists (fun (q : P.peer) -> q.P.p_name = a) m.P.v_peers
    | None -> false
  in
  let prod_dir a =
    match Archive.meta ar root with
    | Some m ->
        List.exists
          (fun (d : P.dep) -> d.P.d_dir = a && not d.P.d_dev)
          m.P.v_deps
    | None -> false
  in
  let kept = Hashtbl.create 64 in
  let rec keep n =
    if not (Hashtbl.mem kept n) then begin
      Hashtbl.replace kept n ();
      List.iter keep (Hashtbl.find_all held n);
      if List.mem n at_top then
        List.iter
          (fun ((c, _) as x) -> if peers_on n (fst c) then keep x)
          at_top
    end
  in
  Hashtbl.replace kept top ();
  List.iter
    (fun ((c, _) as x) ->
      if prod_dir (fst c) || peers_on top (fst c) then keep x)
    at_top;
  kept

let drop_dev ar root r =
  let kept = kept_without_dev ar root r in
  let k n = Hashtbl.mem kept n in
  {
    r with
    installs = List.filter k r.installs;
    tree = List.filter (fun (c, p) -> k c && k p) r.tree;
  }

let solve ?(debug = false) ?(order = Tool) ?(omit_dev = false)
    ?(omit_optional = false) ar (root : string * string) =
  Pubgrub.set_debug debug;
  let st = Lookup.create ~optional:(not omit_optional) ar root in
  let next, choose = hooks order st in
  let root_n = Np.Nm.Granular ((fst root, fst root), snd root) in
  match
    PG.solve ?next ?choose ~vers:(Lookup.versions st) ~deps:(dependencies st)
      [ (root_n, PG.Ranges.of_list [ Np.Vs.Orig (snd root) ]) ]
  with
  | Error inc -> Error inc
  | Ok sol ->
      let r = decode st sol in
      Ok (if omit_dev then drop_dev ar root r else r)
