type result = {
  layout : (string list * (string * string)) list;
  nodes : int;
  lookups : int;
}

module Make () = struct
  module Place_encoding = Place_encoding.Make ()
  open Place_encoding
  module L = Place_lookup.Make (Place_encoding)
  module Place_order = Place_order.Make (Place_encoding) (L)

  (* A location's or a walk's versions fall into stretches, the versions of
     one registry package at one location, which a package's packument lists
     whole.  A key gains a package when a manifest aliasing one to it loads,
     and its versions sort between stretches, never inside one, so a range
     spanning adjacent versions of one stretch stays exact. *)
  let same_stretch (a : PVersion.t) (b : PVersion.t) =
    match (a, b) with
    | R.Version.Occ (Npl.Occupant.Reg (m, _)), R.Version.Occ (Npl.Occupant.Reg (m', _)) ->
        String.equal m m'
    | ( R.Version.Found (l, Npl.Occupant.Reg (m, _)),
        R.Version.Found (l', Npl.Occupant.Reg (m', _)) ) ->
        String.equal m m' && l = l'
    | _ -> false

  (* A dependee's versions as runs of the name's own sorted versions rather
     than as one point per version, as the npm reading's runs, found from
     each version's place in the name's list.  A run stays inside one
     stretch and is closed at its last version, since the next one in the
     list may be another stretch's. *)
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
        List.sort_uniq Int.compare
          (List.filter_map (Hashtbl.find_opt ix.pos) vs)
      in
      let rec go acc lo hi = function
        | [] -> close acc lo hi
        | p :: rest when p = hi + 1 && same_stretch ix.arr.(hi) ix.arr.(p) ->
            go acc lo p rest
        | p :: rest -> go (close acc lo hi) p p rest
      in
      match ps with
      | [] -> PG.Ranges.empty
      | p :: rest -> go PG.Ranges.empty p p rest
    end

  (* PubGrub widens each dependency's depender range by asking for the
     dependencies of the depender's neighbouring versions, and at a location
     every version of the key is a neighbour.  A location's dependees are
     therefore built from parts each converted once. *)
  let dependencies st cache =
    let part_cache = Hashtbl.create 65536 in
    let indices = Hashtbl.create 65536 in
    let conv hs =
      List.map
        (fun ((m, vs) : T.Dependee.t) ->
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
      Pac_common.Tbl.memo cache (n, u) (fun () ->
          match L.parts st n u with
          | Some ps ->
              List.concat_map
                (fun (k, f) ->
                  Pac_common.Tbl.memo part_cache k (fun () -> conv (f ())))
                ps
          | None -> conv (L.dependees st (n, u)))

  (* Each occupant's edges as the lookups read them, the ones the check read
     the answer against.  npm resolves dev and optional dependencies whatever
     --omit says, and leaves out of what it installs only the packages that
     every path from the root reaches through an omitted edge
     (calc-dep-flags.js, and Node.shouldOmit), so an omitted edge is not
     followed. *)
  let edges ~dev ~optional st (x : Npl.Occupant.t) : Npl.coq_Edge list =
    let omitted (e : Npl.coq_Edge) =
      if e.Npl.e_peer then optional && e.Npl.e_optional
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
    List.filter_map
      (fun (ed : L.edge) -> if omitted ed.L.e then None else Some ed.L.e)
      (L.edges st x)

  (* The occupants the root reaches: the decoded layout restricted so is a
     placement resolution, while the whole of it need not be. *)
  let decode ~dev ~optional ~lookups st root sol =
    {
      layout =
        List.sort
          (fun (l, _) (l', _) -> compare (lock_path l) (lock_path l'))
          (List.filter_map
             (fun (l, (a, x)) ->
               match x with
               | Npl.Occupant.Reg (m, v) -> Some (a :: l, (m, v.IVer.s))
               | Npl.Occupant.Proj -> None)
             (Pl.LayoutRel.elements
                (Npl.Reduction.reachableOf (edges ~dev ~optional st) root
                   (R.placementResolution (T.PackageSet.ofList sol)))));
      nodes = List.length sol;
      lookups;
    }

  let check_answer st sol =
    let versions m = T.VSet.ofList (L.versions st m) in
    let dependees p = T.DependeeSet.ofList (L.dependees st p) in
    let q = T.rootQuery (R.Name.Root, R.Version.Occ Npl.Occupant.Proj) in
    match T.check versions dependees q (T.PackageSet.ofList sol) with
    | None -> ()
    | Some f ->
        Pac_common.Check.fail ~pp_name:PName.pp
          ~pp_version:(fun _ -> PVersion.pp)
          ~elements:T.VSet.elements f

  let solve ?(debug = false) ?(check = false) ?(order = `Tool)
      ?(omit_dev = false) ?(omit_optional = false) ~depth ar
      (root : string * string) :
      (result, Pac_common.Report.explanation) Stdlib.result * (unit -> unit) =
    Pubgrub.set_debug debug;
    let st = L.create ~depth ar root in
    let h = Place_order.hooks order st in
    (* each node whose dependencies the solve looked up *)
    let asked = Hashtbl.create 65536 in
    let r =
      PG.solve ?next:h.Pac_common.Order.next ?choose:h.Pac_common.Order.choose
        ~dense:(fun _ -> same_stretch)
        ~vers:(L.versions st) ~deps:(dependencies st asked)
        [ (R.Name.Root, PG.Ranges.of_list [ R.Version.Occ Npl.Occupant.Proj ]) ]
    in
    h.Pac_common.Order.finish ();
    let r =
      match r with
      | Error inc ->
          Error
            (fun ppf ->
              Format.fprintf ppf "(within depth %d)@." depth;
              PG.explain_incompatibility ppf inc)
      | Ok sol ->
          if check then check_answer st sol;
          Ok
            (decode ~dev:omit_dev ~optional:omit_optional
               ~lookups:(Hashtbl.length asked) st (fst root) sol)
    in
    let core () =
      match
        Pac_common.Core.walk ~versions:(L.versions st)
          ~dependees:(fun p ->
            List.map
              (fun ((m, vs) : T.Dependee.t) -> (m, T.VSet.elements vs))
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
end
