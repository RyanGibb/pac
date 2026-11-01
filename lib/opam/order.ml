open Lookups

module NameSet = Set.Make (struct
  type t = PackageFormulaReduction.Name.t

  let compare = FormulaLookups.Name.compare
end)

(* The reduction hands a package's dependees back as a set, so the order
   its dependencies were written in is gone by the time the core graph holds
   them.  Read it back off the parsed formula: opam's CUDF depends list
   is the conjunctive spine in source order (opamSolver.ml,
   [preresolve_deps] then [ands_to_list]), and that is the order
   0install walks. *)
let spine_positions ar (n : string) (v : string) : (string, int) Hashtbl.t =
  let tbl = Hashtbl.create 16 in
  let rec spine acc : Opam_parse.off -> Opam_parse.off list = function
    | OAnd (a, b) -> spine (spine acc a) b
    | f -> f :: acc
  in
  (match (meta_of ar n v).Opam_parse.depends with
  | None -> ()
  | Some f ->
      List.iteri
        (fun i c ->
          List.iter
            (fun m -> if not (Hashtbl.mem tbl m) then Hashtbl.add tbl m i)
            (Opam_parse.off_names [] c))
        (List.rev (spine [] f)));
  tbl

let rec form_names acc (f : PackageFormula.coq_Formula) =
  match f with
  | PackageFormula.FAtom (Reduction.Name.Real m, _) -> m :: acc
  | PackageFormula.FAtom (_, _) -> acc
  | PackageFormula.FConj (a, b) | PackageFormula.FDisj (a, b) ->
      form_names (form_names acc a) b
  | PackageFormula.FNeg a -> form_names acc a

(* where a dependee sits on the depender's spine, or None for the
   dependees 0install's decider never reaches: a conflict is a
   `Restricts dependency it skips outright -- here an edge on a name the
   depends formula does not mention, so unranked -- and a conflict class
   is no role either: opam compiles it into CUDF conflicts
   (opamSwitchState.ml:835-878), which 0install skips as it does any
   other. *)
let spine_rank tbl (m : PackageFormulaReduction.Name.t) : int option =
  let best acc s =
    match (Hashtbl.find_opt tbl s, acc) with
    | Some i, Some j -> Some (min i j)
    | Some i, None -> Some i
    | None, a -> a
  in
  match m with
  | PackageFormulaReduction.Name.Orig (Reduction.Name.Real s) ->
      Hashtbl.find_opt tbl s
  | PackageFormulaReduction.Name.Disjunct fs ->
      List.fold_left
        (fun a f -> List.fold_left best a (form_names [] f))
        None fs
  | _ -> None

let walkable (m : PackageFormulaReduction.Name.t) =
  match m with
  | PackageFormulaReduction.Name.Orig (Reduction.Name.Class _) -> false
  | _ -> true

(* 0install's [decider] (solver_core.ml): walk the roles already selected
   depth-first from the root, each one's dependencies in the order they
   are written, and take the first role still undecided.  PubGrub's
   [Entailed] is that "undecided" -- forced into the solution but not yet
   decided -- and [Decided] is its "selected". *)
let zero_install ar query st ~touch =
  let order_cache = Hashtbl.create 4096 in
  (* opam's create_spec conses each atom onto the list 0install walks
     (opamBuiltin0install.ml:47-53, 65-67), so the query goes last first *)
  let query_positions =
    let tbl = Hashtbl.create 16 in
    List.iteri
      (fun i (n, _) -> if not (Hashtbl.mem tbl n) then Hashtbl.add tbl n i)
      (List.rev query);
    tbl
  in
  (* the dependees of a decided package, in source order and without the
     synthetic packages 0install has no role for *)
  let requirements (tn : PackageFormulaReduction.Name.t) (pv : PVersion.t) :
      PackageFormulaReduction.Name.t list =
    ignore (FormulaLookups.dependencies st ~touch tn pv);
    (* 0install's decider walks requirements, not restrictions: a
       conflict's edge admits ⊥ and opens no role *)
    let ds =
      List.filter_map
        (fun (m, vs) ->
          if Reduced.VSet.mem PackageFormulaReduction.Version.Bot vs then None
          else Some m)
        (FormulaLookups.dependees st (tn, pv.PVersion.v))
    in
    match (tn, pv.PVersion.v) with
    | ( PackageFormulaReduction.Name.Orig (Reduction.Name.Real n),
        PackageFormulaReduction.Version.Orig (Reduction.Version.RV v) ) ->
        let tbl =
          match Hashtbl.find_opt order_cache (n, v) with
          | Some t -> t
          | None ->
              let t = spine_positions ar n v in
              Hashtbl.add order_cache (n, v) t;
              t
        in
        List.filter_map
          (fun m -> Option.map (fun i -> (i, m)) (spine_rank tbl m))
          ds
        |> List.stable_sort (fun (i, _) (j, _) -> compare (i : int) j)
        |> List.map snd
    (* the root's dependencies are the query, in the order opam hands it
       on *)
    | PackageFormulaReduction.Name.Orig Reduction.Name.Root, _ ->
        let rank m =
          match spine_rank query_positions m with
          | Some i -> i
          | None -> max_int
        in
        List.filter walkable ds
        |> List.stable_sort (fun a b -> compare (rank a) (rank b))
    (* a disjunct package carries the alternative it was decided to, and
       there is no written order to restore *)
    | _ -> List.filter walkable ds
  in
  fun ~assigned (open_names : (PackageFormulaReduction.Name.t * int) list) ->
    let opens =
      List.fold_left (fun s (n, _) -> NameSet.add n s) NameSet.empty open_names
    in
    let exception Found of PackageFormulaReduction.Name.t in
    let rec visit seen n =
      if NameSet.mem n seen then seen
      else
        let seen = NameSet.add n seen in
        match assigned n with
        | Resolver.Unselected -> seen
        | Resolver.Entailed _ ->
            if NameSet.mem n opens then raise (Found n) else seen
        | Resolver.Decided v -> List.fold_left visit seen (requirements n v)
    in
    try
      ignore
        (visit NameSet.empty
           (PackageFormulaReduction.Name.Orig Reduction.Name.Root));
      (* nothing on the walk is open: leave the solver's own choice,
         absence last *)
      FormulaLookups.defer_bot ~assigned open_names
    with Found n -> n

(* Both orders take PubGrub's greatest candidate under the preference
   PVersion carries; [`Pubgrub] is PubGrub's fewest-candidates order with
   absence deferred, as for every reduction through the package
   formulas. *)
let hooks :
    ( archive
      * (string * Opam_parse.vc) list
      * FormulaLookups.t
      * (Reduced.Package.t -> unit),
      PackageFormulaReduction.Name.t,
      Resolver.selection,
      PVersion.t )
    Pac_common.Order.driver =
 fun order (ar, query, st, touch) ->
  match order with
  | `Tool -> Pac_common.Order.make ~next:(zero_install ar query st ~touch) ()
  | `Pubgrub ->
      Pac_common.Order.make ~next:(FormulaLookups.defer_bot ?last:None) ()
  | `Random seed -> Pac_common.Order.random seed
