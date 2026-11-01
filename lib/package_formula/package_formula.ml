module Tbl = Pac_common.Tbl

module Make
    (N : Pac.UsualOrderedType)
    (V : Pac.UsualOrderedType)
    (PF :
      module type of Pac.PackageFormula (N) (V))
        (P : sig
          type t

          val v : t -> PF.Reduction.Version.t
          val bot : t
          val compare : t -> t -> int
          val pp : Format.formatter -> t -> unit
        end)
        (Pp : sig
          val pp_name : Format.formatter -> PF.Reduction.Name.t -> unit
        end) =
struct
  module PFR = PF.Reduction
  module T = PFR.Reduced

  let r2c = Pac_common.Ot.r2c

  module Name = struct
    type t = PFR.Name.t

    (* NameOT is a UsualOrderedType, so a name compares Eq to itself; the
       pointer test only skips the walk on interned names (see [intern]),
       and leaves the order PubGrub sees exactly as NameOT gives it *)
    let compare a b = if a == b then 0 else r2c (PFR.NameOT.compare a b)
    let pp = Pp.pp_name
  end

  module PG = Pubgrub.Make (Name) (P)

  module NameMap = Map.Make (struct
    type t = PFR.Name.t

    let compare a b = r2c (PFR.NameOT.compare a b)
  end)

  type t = {
    root : N.t * V.t;
    tag : PFR.Name.t -> PFR.Version.t -> P.t;
    oracle : N.t -> PF.VSet.t;
    volatile : N.t -> bool;
    edges : (T.Package.t, T.DependeeSet.t) Hashtbl.t;
    synthetic_vers : (PFR.Name.t, P.t list) Hashtbl.t;
    original_vers : (N.t, P.t list) Hashtbl.t;
    oracle_memo : (N.t, PF.VSet.t) Hashtbl.t;
    seen : (PF.Package.t, unit) Hashtbl.t;
    deps : (T.Package.t, (PFR.Name.t * PG.Ranges.t) list) Hashtbl.t;
    mutable canon : PFR.Name.t NameMap.t;
  }

  let create ~root ~tag ~oracle ?(volatile = fun _ -> false) () =
    {
      root;
      tag;
      oracle;
      volatile;
      edges = Hashtbl.create 65536;
      synthetic_vers = Hashtbl.create 65536;
      original_vers = Hashtbl.create 16384;
      oracle_memo = Hashtbl.create 16384;
      seen = Hashtbl.create 16384;
      deps = Hashtbl.create 65536;
      canon = NameMap.empty;
    }

  let lookups st = Hashtbl.length st.deps

  let unless_volatile st tbl (n : N.t) f =
    if st.volatile n then f () else Tbl.memo tbl n f

  let oracle st (n : N.t) : PF.VSet.t =
    unless_volatile st st.oracle_memo n (fun () -> st.oracle n)

  (* A Disjunct name carries its formulas, so comparing two equal names
     walks both in full, and PubGrub does that on every dependency-list scan
     and map hit.  Each version's reduction builds its own copy of a
     synthetic name shared across versions; one representative per name
     lets [Name.compare] answer equality by pointer.  The map is keyed by
     NameOT itself, so which names unify is exactly NameOT equality and the
     order PubGrub sees -- a next hook's pick included -- is unchanged. *)
  let intern st (m : PFR.Name.t) : PFR.Name.t =
    match NameMap.find_opt m st.canon with
    | Some c -> c
    | None ->
        st.canon <- NameMap.add m m st.canon;
        m

  (* A package can carry thousands of dependees -- one per install-if rule
     designating it, 1023 for Alpine's docs -- so inserting them one at a
     time into a sorted-list set is quadratic: group by source first and
     build each source's set in a single pass. *)
  let record_deprel st (d : T.DependencyRel.t) =
    let by_src = Hashtbl.create 64 in
    List.iter
      (fun ((s, h) : T.DependencyElt.t) -> Tbl.push by_src s h)
      (T.DependencyRel.elements d);
    Hashtbl.iter
      (fun s hs ->
        let fresh = T.DependeeSet.ofList hs in
        Hashtbl.replace st.edges s
          (match Hashtbl.find_opt st.edges s with
          | Some prev -> T.DependeeSet.union prev fresh
          | None -> fresh))
      by_src

  (* Only the synthetic names the reduction introduces are harvested; an
     original name's versions are its lookup's, [versions]. *)
  let record_synthetic st (r : T.PackageSet.t) =
    List.iter
      (fun ((tn, tv) : T.Package.t) ->
        match tn with
        | PFR.Name.Orig _ -> ()
        | _ ->
            let tv = st.tag tn tv in
            if not (List.mem tv (Tbl.find_list st.synthetic_vers tn)) then
              Tbl.push st.synthetic_vers tn tv)
      (T.PackageSet.elements r)

  let process st (q : PF.Package.t) (dependees : unit -> PF.coq_Formula list) =
    if not (Hashtbl.mem st.seen q) then begin
      Hashtbl.replace st.seen q ();
      let d_q =
        PF.DependencyRel.ofList (List.map (fun f -> (q, f)) (dependees ()))
      in
      record_deprel st (PFR.reduceDepsBy (oracle st) d_q);
      record_synthetic st (PFR.reduceReal (PF.PackageSet.singleton q) d_q)
    end

  let dependees st (p : T.Package.t) : T.Dependee.t list =
    match Hashtbl.find_opt st.edges p with
    | Some hs -> T.DependeeSet.elements hs
    | None -> []

  (* Every original name answers its versions and the absent one
     (PF.Reduction.Lookup.versions_lookupOrig), except the root, whose
     absent version the query rules out before the solve starts and whose
     presence in the list would only widen the ranges PubGrub prints for
     it.  A synthetic name answers what its owners' reductions harvested. *)
  let versions st (tn : PFR.Name.t) : P.t list =
    match tn with
    | PFR.Name.Orig n when N.eq_dec n (fst st.root) ->
        [ st.tag tn (PFR.Version.Orig (snd st.root)) ]
    | PFR.Name.Orig n ->
        unless_volatile st st.original_vers n (fun () ->
            List.map
              (fun w -> st.tag tn (PFR.Version.Orig w))
              (PF.VSet.elements (oracle st n))
            @ [ P.bot ])
    | PFR.Name.Disjunct _ -> Tbl.find_list st.synthetic_vers tn

  (* [touch] processes the package, where it is one whose dependees are
     read off an instance; a synthetic package's edges were harvested when
     its owner was.  Memoised because PubGrub asks, at each decision, for
     the dependencies of every version of the node. *)
  let dependencies st ~touch (tn : PFR.Name.t) (pv : P.t) =
    let p = (tn, P.v pv) in
    Tbl.memo st.deps p (fun () ->
        touch p;
        List.map
          (fun ((m, vs) : T.Dependee.t) ->
            let m = intern st m in
            (m, PG.Ranges.of_list (List.map (st.tag m) (T.VSet.elements vs))))
          (dependees st p))

  (* only an original name has the absent version; asking the partial
     solution about a disjunct would compare its formulas *)
  let admits_bot ~assigned (tn : PFR.Name.t) =
    match tn with
    | PFR.Name.Orig _ -> (
        match assigned tn with
        | PG.Entailed r -> PG.Ranges.contains P.bot r
        | _ -> false)
    | PFR.Name.Disjunct _ -> false

  (* Absence is the greatest version but the last decision: decided early,
     by PubGrub's fewest-candidates order, a name a negated atom reaches goes
     to ⊥ before the packages that need it, narrowing them.  So a name whose
     range admits ⊥ waits until every name that must be present is decided:
     then either something needs it and its range excludes ⊥, or ⊥ is
     right.  The names [last] holds wait behind those. *)
  let defer_bot ?(last = fun _ -> false) ~assigned
      (open_names : (PFR.Name.t * int) list) =
    let rank (n, _) =
      if last n then 2 else if admits_bot ~assigned n then 1 else 0
    in
    fst
      (List.fold_left
         (fun best c -> if rank c < rank best then c else best)
         (List.hd open_names) (List.tl open_names))

  (* [Pp.pp_name] stands a disjunct for its formulas, which the explanations
     print; the core block lists disjuncts side by side, so it spells each
     one out, its versions tagged as PubGrub sees them *)
  let rec pp_formula st fmt (f : PF.coq_Formula) =
    match f with
    | PF.FAtom (n, vs) ->
        let tn = PFR.Name.Orig n in
        Format.fprintf fmt "%a{%a}" Pp.pp_name tn
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
             P.pp)
          (List.map
             (fun w -> st.tag tn (PFR.Version.Orig w))
             (PF.VSet.elements vs))
    | PF.FConj (a, b) ->
        Format.fprintf fmt "(%a & %a)" (pp_formula st) a (pp_formula st) b
    | PF.FDisj (a, b) ->
        Format.fprintf fmt "(%a | %a)" (pp_formula st) a (pp_formula st) b
    | PF.FNeg a -> Format.fprintf fmt "!%a" (pp_formula st) a

  let pp_core_name st fmt (tn : PFR.Name.t) =
    match tn with
    | PFR.Name.Disjunct fs ->
        Format.fprintf fmt "<%a>"
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt " | ")
             (pp_formula st))
          fs
    | PFR.Name.Orig _ -> Pp.pp_name fmt tn

  let core st ~touch =
    Pac_common.Core.print ~pp_name:(pp_core_name st) ~pp_version:P.pp
      (Pac_common.Core.walk ~versions:(versions st)
         ~dependees:(fun (tn, pv) ->
           let p = (tn, P.v pv) in
           touch p;
           List.map
             (fun ((m, vs) : T.Dependee.t) ->
               (m, List.map (st.tag m) (T.VSet.elements vs)))
             (dependees st p))
         [ PFR.Name.Orig (fst st.root) ])

  let check st ~touch (core : T.PackageSet.t) =
    let versions tn = T.VSet.ofList (List.map P.v (versions st tn)) in
    let dependees p =
      touch p;
      T.DependeeSet.ofList (dependees st p)
    in
    let root =
      T.rootQuery (PFR.Name.Orig (fst st.root), PFR.Version.Orig (snd st.root))
    in
    match T.check versions dependees root core with
    | None -> ()
    | Some f ->
        Pac_common.Check.fail ~pp_name:Pp.pp_name
          ~pp_version:(fun tn fmt v -> P.pp fmt (st.tag tn v))
          ~elements:T.VSet.elements f

  let solve st ~check:checked ~touch
      (h : (Name.t, PG.selection, P.t) Pac_common.Order.hooks) :
      (PF.PackageSet.t * int, Pac_common.Report.explanation) result =
    let root = PFR.Name.Orig (fst st.root) in
    let r =
      PG.solve ?next:h.Pac_common.Order.next ?choose:h.Pac_common.Order.choose
        ~vers:(versions st) ~deps:(dependencies st ~touch)
        [ (root, PG.Ranges.of_list (versions st root)) ]
    in
    h.Pac_common.Order.finish ();
    match r with
    | Error inc -> Error (fun ppf -> PG.explain_incompatibility ppf inc)
    | Ok sol ->
        let core =
          T.PackageSet.ofList (List.map (fun (tn, pv) -> (tn, P.v pv)) sol)
        in
        if checked then check st ~touch core;
        Ok (PFR.packageFormulaResolution core, List.length sol)
end
