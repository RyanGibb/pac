module Tbl = Pac_common.Tbl

module Make
    (N : Pac.UsualOrderedType)
    (V : Pac.UsualOrderedType)
    (PF :
      module type of Pac.PackageFormula (N) (V))
        (P : sig
          type t

          val v : t -> PF.Reduction.Version.t

          (* the absent version, tagged: [tag] must give it at every name *)
          val bot : t
          val compare : t -> t -> int
          val pp : Format.formatter -> t -> unit
        end)
        (Pp : sig
          val pp_name : Format.formatter -> PF.Reduction.Name.t -> unit
        end) =
struct
  module PFR = PF.Reduction
  module T = PFR.T

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
    edges : (T.Pkg.t, T.DependeesSet.t) Hashtbl.t;
    synthetic_vers : (PFR.Name.t, P.t list) Hashtbl.t;
    original_vers : (N.t, P.t list) Hashtbl.t;
    oracle_memo : (N.t, PF.VSet.t) Hashtbl.t;
    seen : (PF.Pkg.t, unit) Hashtbl.t;
    deps : (T.Pkg.t, (PFR.Name.t * PG.Ranges.t) list) Hashtbl.t;
    mutable canon : PFR.Name.t NameMap.t;
  }

  (* [oracle] is the versions lookup at an original name, before tagging;
     the encoder reads it at the names a formula negates, so it must be
     complete when asked.  Its answer is memoised except at a [volatile]
     name, whose versions may grow as the run loads more of the archive. *)
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
  let record_deprel st (d : T.DepRel.t) =
    let by_src = Hashtbl.create 64 in
    List.iter
      (fun ((s, h) : T.DepElt.t) ->
        Tbl.push by_src s h)
      (T.DepRel.elements d);
    Hashtbl.iter
      (fun s hs ->
        let fresh = T.DependeesSet.ofList hs in
        Hashtbl.replace st.edges s
          (match Hashtbl.find_opt st.edges s with
          | Some prev -> T.DependeesSet.union prev fresh
          | None -> fresh))
      by_src

  (* Only the synthetic names the reduction introduces are harvested; an
     original name's versions are its lookup's, [versions]. *)
  let record_synthetic st (r : T.PkgSet.t) =
    List.iter
      (fun ((tn, tv) : T.Pkg.t) ->
        match tn with
        | PFR.Name.Orig _ -> ()
        | _ ->
            let tv = st.tag tn tv in
            if not (List.mem tv (Tbl.find_list st.synthetic_vers tn))
            then Tbl.push st.synthetic_vers tn tv)
      (T.PkgSet.elements r)

  (* [dependees] is PF.Reduction's dependees lookup at [q], read off the
     sub-instance the driver builds for it; a thunk, so a package asked
     about twice builds it once *)
  let process st (q : PF.Pkg.t) (dependees : unit -> PF.coq_Formula list) =
    if not (Hashtbl.mem st.seen q) then begin
      Hashtbl.replace st.seen q ();
      let d_q = PF.DepRel.ofList (List.map (fun f -> (q, f)) (dependees ())) in
      record_deprel st (PFR.reduceDepsBy (oracle st) d_q);
      record_synthetic st (PFR.reduceReal (PF.PkgSet.singleton q) d_q)
    end

  let dependees st (p : T.Pkg.t) : T.Dependees.t list =
    match Hashtbl.find_opt st.edges p with
    | Some hs -> T.DependeesSet.elements hs
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
          (fun ((m, vs) : T.Dependees.t) ->
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

  (* Absence is the greatest version but the last decision.  A name a
     negated atom reaches is entailed to a range admitting ⊥ the moment its
     declarer is decided, and PubGrub's own order -- fewest candidates
     first -- would then decide it, to ⊥, before the packages that need it
     are decided, narrowing their ranges to the versions that do not (opam's
     lwt 6.1.2 needs dune-configurator; dune's conflict on old
     dune-configurators had it decided absent first, and lwt fell to
     4.2.1).  So a name whose open range still admits ⊥ waits until every
     name that must be present is decided; by then either something needs
     it, and its range excludes ⊥, or nothing does, and ⊥ is right.  The
     names [last] holds wait behind even those. *)
  let defer_bot ?(last = fun _ -> false) ~assigned
      (open_names : (PFR.Name.t * int) list) =
    let rank (n, _) =
      if last n then 2 else if admits_bot ~assigned n then 1 else 0
    in
    fst
      (List.fold_left
         (fun best c -> if rank c < rank best then c else best)
         (List.hd open_names) (List.tl open_names))

  (* The core solution back through the proved decoder to the package
     formula's packages.  Reading the ecosystem's packages off the
     solution directly would be a further, unproved, decoder, and it is
     the decoded one the soundness theorem is stated about. *)
  let solve st ~touch (h : (Name.t, PG.selection, P.t) Pac_common.Order.hooks) :
      (PF.PkgSet.t * int, Pac_common.Report.explanation) result =
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
          T.PkgSet.ofList (List.map (fun (tn, pv) -> (tn, P.v pv)) sol)
        in
        Ok (PFR.packageFormulaResolution core, List.length sol)
end
