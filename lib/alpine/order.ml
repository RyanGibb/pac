(* Which name PubGrub decides next and which candidate it tries, as apk
   would ([`Tool]), or as near PubGrub's own choices ([`Pubgrub]) as an
   answer apk accepts allows.  apk accepts an installed set only when its
   own solver, rerun on it, changes nothing, and that solver swaps a
   provider for a higher-ranked one and drops a package nothing needs.
   So an answer that departs from apk's choices is one apk rejects, and
   three of the rules below are kept in both orders: apk's provider
   ranking, which PVersion carries, a name already provided by a selected
   package kept for it, and install-if rules decided last.  On 2222 goals
   chosen to exercise providers and install-if rules, dropping the second
   leaves 175 answers apk rejects, the third 200, and PubGrub's
   own choose and next together 359; dropping the install-if rule of
   [choose], which is all [`Pubgrub] drops, changes none.  Trusted here
   (TCB): these policy choices. *)

open Lookups

type t = [ `Tool | `Pubgrub ]

let greatest = function
  | [] -> invalid_arg "greatest"
  | c :: cs ->
      List.fold_left (fun a b -> if PVersion.compare b a > 0 then b else a) c cs

(* only installIfForm's disjuncts open on FNeg: encDep negates whole
   formulas *)
let is_install_if (tn : PFR.Name.t) =
  match tn with PFR.Name.Disjunct (PF.FNeg _ :: _) -> true | _ -> false

(* A range that still admits ⊥ is what a negated requirement leaves a
   name, not a need for it: the name may yet be absent, so the solution
   does not carry it. *)
let carried_at ~assigned tn tvs =
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
   positive one whose atom it does not carry, or a negated one whose atom
   it does -- free, constraining nothing, and to take the augmented
   package only when it falsifies none.  A negated condition's
   alternative is doubly negated (encCond). *)
let choose ar ~install_if ~assigned (tn : PFR.Name.t)
    (cands : PVersion.t list) =
  let carried f =
    List.exists (fun (m, tvs) -> carried_at ~assigned m tvs) (leaves ar f)
  in
  match tn with
  | PFR.Name.Disjunct fs when install_if && is_install_if tn -> (
      let free = ref [] and pos = ref [] in
      List.iter
        (fun (pv : PVersion.t) ->
          match pv.PVersion.v with
          | PFR.Version.Idx i -> (
              match alt_at fs i with
              | Some (PF.FNeg (PF.FNeg f), _) ->
                  if carried f then free := pv :: !free
              | Some (PF.FNeg f, _) ->
                  if not (carried f) then free := pv :: !free
              | Some (f, last) -> pos := (alt_rank ar last f, pv) :: !pos
              | None -> ())
          | _ -> ())
        cands;
      match !free with
      | _ :: _ as free -> greatest free
      | [] -> (
          match !pos with
          | [] -> greatest cands
          | p :: ps ->
              snd
                (List.fold_left
                   (fun ((ra, a) as best) ((rb, b) as cand) ->
                     if rb > ra || (rb = ra && PVersion.compare b a > 0) then
                       cand
                     else best)
                   p ps)))
  (* apk never chooses among the providers of a name already taken:
     selecting a package assigns it every name it provides, so a later
     dependency on one of them is met by that package.  So a provider the
     solution already carries goes first, and the rank orders the rest. *)
  | PFR.Name.Disjunct (f0 :: _ as fs) when lone_provider f0 <> None -> (
      let taken =
        List.filter
          (fun (pv : PVersion.t) ->
            match pv.PVersion.v with
            | PFR.Version.Idx i -> (
                match alt_at fs i with Some (f, _) -> carried f | None -> false)
            | _ -> false)
          cands
      in
      match taken with [] -> greatest cands | _ -> greatest taken)
  | _ -> greatest cands

(* PubGrub's own order, fewest candidates first, but for two deferrals.
   An install-if disjunct exists only once its designated condition has
   been selected, so the conditions it discharges on have largely settled
   by the time [choose] sees it.  Deferring it behind every other open
   name settles the rest of them; decided early, it asserts a condition
   false or installs its package before either is known to be needed.  A
   name whose open range still admits ⊥ waits behind every name that must
   be present, as the shared [defer_bot] has it, and ahead only of the install-if
   disjuncts. *)
let next ~assigned (opens : (PFR.Name.t * int) list) =
  let rank (tn, _) =
    if is_install_if tn then 2 else if L.admits_bot ~assigned tn then 1 else 0
  in
  fst
    (List.fold_left
       (fun best c -> if rank c < rank best then c else best)
       (List.hd opens) (List.tl opens))

let hooks (order : t) ar =
  match order with
  | `Tool -> (Some next, Some (choose ar ~install_if:true))
  | `Pubgrub -> (Some next, Some (choose ar ~install_if:false))
