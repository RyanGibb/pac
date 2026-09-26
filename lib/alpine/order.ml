module Make (Lk : Lookups.S) = struct
  open Lk

  let greatest = Pac_common.Order.greatest PVersion.compare

  (* only installIfForm's disjuncts open on FNeg: encDep negates whole
   formulas *)
  let is_install_if (tn : PFR.Name.t) =
    match tn with PFR.Name.Disjunct (PF.FNeg _ :: _) -> true | _ -> false

  (* A range that still admits ⊥ is what a negated requirement leaves a
   name, not a need for it: the name may yet be absent, so the solution
   does not hold it. *)
  let assigned_among ~assigned tn tvs =
    match assigned tn with
    | PG.Unselected -> false
    | PG.Decided u -> List.exists (fun v -> PVersion.compare u v = 0) tvs
    | PG.Entailed r ->
        (not (PG.Ranges.contains PVersion.bot r))
        && List.exists (fun v -> PG.Ranges.contains v r) tvs

  let rec leaves ar (f : PF.coq_Formula) : (PFR.Name.t * PVersion.t list) list =
    match f with
    | PF.FDep (m, vs) ->
        let tn = PFR.Name.Orig m in
        [
          ( tn,
            List.map
              (fun w -> tag ar tn (PFR.Version.Orig w))
              (PF.VSet.elements vs) );
        ]
    | PF.FDisj (a, b) | PF.FConj (a, b) -> leaves ar a @ leaves ar b
    | PF.FNeg _ -> []

  (* apk never asserts a condition false: it installs the augmented package
   when all the conditions hold and otherwise does nothing at all.
   PubGrub has to decide the disjunct either way, so the nearest thing is
   to discharge it on a condition the solution already falsifies -- a
   positive one whose atom it does not hold, or a negated one whose atom
   it does -- free, constraining nothing, and to take the augmented
   package only when it falsifies none.  A negated condition's
   alternative is doubly negated (encCond). *)
  let choose ar ~install_if ~assigned (tn : PFR.Name.t)
      (cands : PVersion.t list) =
    let held f =
      List.exists (fun (m, tvs) -> assigned_among ~assigned m tvs) (leaves ar f)
    in
    match tn with
    | PFR.Name.Disjunct fs when install_if && is_install_if tn -> (
        let alt (pv : PVersion.t) =
          match pv.PVersion.v with
          | PFR.Version.Idx i -> alt_at fs i
          | _ -> None
        in
        let free =
          List.filter
            (fun pv ->
              match alt pv with
              | Some (PF.FNeg (PF.FNeg f), _) -> held f
              | Some (PF.FNeg f, _) -> not (held f)
              | _ -> false)
            cands
        and pos =
          List.filter_map
            (fun pv ->
              match alt pv with
              | Some (PF.FNeg _, _) | None -> None
              | Some (f, last) -> Some (alt_rank ar last f, pv))
            cands
        in
        match (free, pos) with
        | _ :: _, _ -> greatest free
        | [], [] -> greatest cands
        | [], p :: ps ->
            snd
              (List.fold_left
                 (fun ((ra, a) as best) ((rb, b) as cand) ->
                   if rb > ra || (rb = ra && PVersion.compare b a > 0) then cand
                   else best)
                 p ps))
    (* apk never chooses among the providers of a name already taken:
     selecting a package assigns it every name it provides, so a later
     dependency on one of them is met by that package.  So a provider the
     solution already holds goes first, and the rank orders the rest. *)
    | PFR.Name.Disjunct (f0 :: _ as fs) when lone_provider f0 <> None -> (
        let taken =
          List.filter
            (fun (pv : PVersion.t) ->
              match pv.PVersion.v with
              | PFR.Version.Idx i -> (
                  match alt_at fs i with Some (f, _) -> held f | None -> false)
              | _ -> false)
            cands
        in
        match taken with [] -> greatest cands | _ -> greatest taken)
    | _ -> greatest cands

  (* PubGrub's own order, fewest candidates first, but for two deferrals: a
   name whose open range still admits ⊥, as for every package formula,
   and behind it an install-if disjunct.  Such a disjunct exists only once
   its designated condition has been selected, so the conditions it
   discharges on have largely settled by the time [choose] sees it.
   Deferring it behind every other open name settles the rest of them;
   decided early, it asserts a condition false or installs its package
   before either is known to be needed. *)
  let next = L.defer_bot_then ~last:is_install_if

  (* apk's solver, rerun on an installed set, swaps a provider for a
   higher-ranked one and drops a package nothing needs, so an answer that
   departs from apk's choices is valid but not minimal.  The rules that
   keep it minimal are kept in both orders: apk's provider ranking, which
   PVersion carries, a name already provided by a selected package kept
   for it, and install-if rules decided last.  On 2222 goals chosen to
   exercise providers and install-if rules, dropping the second leaves 175
   answers apk would change, the third 200, and PubGrub's own choose and
   next together 359; dropping the install-if rule of [choose], which is
   all [`Pubgrub] drops, changes none. *)
  let hooks :
      (archive, PFR.Name.t, PG.selection, PVersion.t) Pac_common.Order.driver =
   fun order ar ->
    match order with
    | `Tool ->
        Pac_common.Order.make ~next ~choose:(choose ar ~install_if:true) ()
    | `Pubgrub ->
        Pac_common.Order.make ~next ~choose:(choose ar ~install_if:false) ()
    | `Random seed -> Pac_common.Order.random seed
end
