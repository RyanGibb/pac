open Encoding
module P = Npm_parse

type result = {
  installs : ((string * string) * string) list;
  tree : (((string * string) * string) * ((string * string) * string)) list;
  nodes : int;
  lookups : int;
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
let dependencies st cache n (u : Np.Vs.version) =
  Pac_common.Tbl.memo cache (n, u) (fun () ->
      List.map
        (fun ((m, vs) : T.Dependees.t) ->
          (m, runs (lazy (Lookup.versions st m)) (T.VSet.elements vs)))
        (Lookup.dependees st (n, u)))

let decode st ~lookups sol =
  let s = T.PkgSet.ofList sol in
  let read, dropped = Lookup.optional_verdicts st in
  {
    installs = List.sort compare (Np.PkgSet.elements (R.npmResolution s));
    tree = List.sort compare (Np.Conc.ParentRel.elements (R.npmParents s));
    nodes = List.length sol;
    lookups;
    optional_read = read;
    optional_dropped = dropped;
  }

(* npm resolves dev and optional dependencies whatever --omit says, and
   leaves out of what it installs only the packages that every path from
   the root reaches through an omitted edge (calc-dep-flags.js, and
   Node.shouldOmit), so they still shape the versions the rest gets.  A
   copy holds its dependencies, and its peer is what its holder shows: the
   holder's own copy, or where the holder peers on the name too, what the
   holder's own holders show.  A copy is a package under one holder. *)
let kept ~dev ~optional ar (root : string * string) r =
  let top = ((fst root, fst root), snd root) in
  let kids = Hashtbl.create 64 and up = Hashtbl.create 64 in
  List.iter
    (fun (c, p) ->
      Hashtbl.add kids p c;
      Hashtbl.add up c p)
    r.tree;
  let meta ((k, v) : (string * string) * string) = Archive.meta ar (snd k, v) in
  let child p a =
    List.filter_map
      (fun (((k, _) : (string * string) * string) as c) ->
        if fst k = a then Some (c, p) else None)
      (Hashtbl.find_all kids p)
  in
  let peers_on n a =
    match meta n with
    | Some m -> List.exists (fun (q : P.peer) -> q.P.p_name = a) m.P.v_peers
    | None -> false
  in
  let rec shows seen p a =
    if p <> top && peers_on p a && not (List.mem p seen) then
      match
        List.concat_map (fun q -> shows (p :: seen) q a) (Hashtbl.find_all up p)
      with
      | [] -> child p a
      | l -> l
    else child p a
  in
  let kept = Hashtbl.create 64 in
  let rec keep ((n, h) as copy) =
    if not (Hashtbl.mem kept copy) then begin
      Hashtbl.replace kept copy ();
      match meta n with
      | None -> ()
      | Some m ->
          List.iter
            (fun (d : P.dep) ->
              if
                (n = top || not d.P.d_dev)
                && (not (dev && d.P.d_dev))
                && not (optional && d.P.d_optional)
              then List.iter keep (child n d.P.d_dir))
            m.P.v_deps;
          List.iter
            (fun (q : P.peer) ->
              if not (optional && q.P.p_optional) then
                List.iter keep (shows [] h q.P.p_name))
            m.P.v_peers
    end
  in
  keep (top, top);
  kept

let drop ~dev ~optional ar root r =
  let kept = kept ~dev ~optional ar root r in
  let tree = List.filter (Hashtbl.mem kept) r.tree in
  let top = ((fst root, fst root), snd root) in
  {
    r with
    installs =
      List.filter (fun n -> n = top || List.mem_assoc n tree) r.installs;
    tree;
  }

let solve ?(debug = false) ?(order = `Tool) ?(omit_dev = false)
    ?(omit_optional = false) ar (root : string * string) :
    (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit) =
  Pubgrub.set_debug debug;
  let st = Lookup.create ar root in
  let h = Order.hooks order st in
  (* dependencies' memo, whose size is the lookup count the answer reports *)
  let asked = Hashtbl.create 65536 in
  let root_k = (fst root, fst root) in
  let root_n = Np.Nm.Granular (root_k, snd root) in
  (* Every name's versions are fixed once asked, bar the root's
     intermediates, which a root-installable peer loaded later can fill
     (peers_naming). Where the list is fixed, a depender's block of
     versions may run up to the next listed one, as [runs] does for a
     dependee's, so ranges stay few. *)
  let dense (n : Np.Nm.name) _ _ =
    match n with Np.Nm.Intermediate (k, _, _) -> k <> root_k | _ -> true
  in
  let r =
    PG.solve ?next:h.Pac_common.Order.next ?choose:h.Pac_common.Order.choose
      ~dense ~vers:(Lookup.versions st) ~deps:(dependencies st asked)
      [ (root_n, PG.Ranges.of_list [ Np.Vs.Orig (snd root) ]) ]
  in
  h.Pac_common.Order.finish ();
  let r =
    match r with
    | Error inc -> Error (fun ppf -> PG.explain_incompatibility ppf inc)
    | Ok sol ->
        let r = decode st ~lookups:(Hashtbl.length asked) sol in
        Ok
          (if omit_dev || omit_optional then
             drop ~dev:omit_dev ~optional:omit_optional ar root r
           else r)
  in
  (* a registry failing the walk says nothing of the answer, which is
     decoded already *)
  let core () =
    match
      Pac_common.Core.walk ~versions:(Lookup.versions st)
        ~dependees:(fun p ->
          List.map
            (fun ((m, vs) : T.Dependees.t) -> (m, T.VSet.elements vs))
            (Lookup.dependees st p))
        [ root_n ]
    with
    | c -> Pac_common.Core.print ~pp_name:PName.pp ~pp_version:PVersion.pp c
    | exception Archive.Fetch_failed e ->
        Printf.printf "core: incomplete, %s\n%!" e
  in
  (r, core)
