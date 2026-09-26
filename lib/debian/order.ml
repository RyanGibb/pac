module Make (S : Apt_reject.SEARCH) = struct
  open S
  open T
  include Apt_reject.Make (S)

  module Driver = struct
    type nonrec state = state
    type nonrec name = name
    type version = PVersion.t
    type atom = DMA.Deb.Atom.t
    type nonrec assigned = assigned
    type nonrec rejection = rejection

    let kind : name -> Work_heap.kind = function
      | DMA.Deb.Name.Orig _ -> Package
      | DMA.Deb.Name.Disjunct _ -> Hard
      | DMA.Deb.Name.Soft _ -> Soft
      | DMA.Deb.Name.Selector _ -> Alternative

    let clause_atoms = function
      | DMA.Deb.Name.Disjunct aset | DMA.Deb.Name.Soft aset ->
          (* as ordered_clauses counts them *)
          Some (DMA.Deb.AtomSet.elements (DMA.Deb.clauseAtoms aset))
      | DMA.Deb.Name.Selector a ->
          (* a one-alternative Depends has no disjunct package: the selector
             itself is the work item *)
          Some [ a ]
      | _ -> None

    let static_solutions st a = solutions st None a
    let solutions st ~assigned a = solutions st (Some assigned) a

    (* apt tests each solution's package, not the version the solution
       names; under Strict-Pinning the one is the other's only version *)
    let obsolete (a : atom) =
      let at (n, x) w =
        match x with
        | DMA.QAArch b -> (
            match stanza ((n, b), w) with
            | Some stz -> T.obsolete tables stz
            | None -> false)
        | _ -> false
      in
      match cands_of (DMA.Deb.Name.Selector a) with
      | [] ->
          List.exists
            (fun (_, w) -> sat (snd a) w && at (fst a) w)
            (orig_versions (DMA.Deb.Name.Orig (fst a)))
      | cs ->
          List.exists
            (fun (pv : PVersion.t) ->
              match pv.PVersion.v with
              | DMA.Deb.Version.RefReal w -> at (fst a) w
              | DMA.Deb.Version.Ref (m, w) -> at m w
              | _ -> false)
            cs

    let decided (assigned : assigned) n =
      match assigned n with PG.Decided pv -> Some pv | _ -> None

    let satisfied assigned n = free_of ~assigned n (cands_of n) <> []

    let at_pkg f n (pv : PVersion.t) =
      match (n, pv.PVersion.v) with
      | DMA.Deb.Name.Orig (m, DMA.QAArch b), DMA.Deb.Version.Orig v ->
          f ((m, b), v)
      | _ -> []

    let conflicts st ~assigned n pv = at_pkg (conflicts st ~assigned) n pv

    let conflicted_by st ~assigned n pv =
      at_pkg (conflicted_by st ~assigned) n pv

    let propagate = propagate
    let assign = assign

    let reset st =
      Hashtbl.reset st.vdead;
      Hashtbl.reset st.pdead

    let version_equal a b = PVersion.compare a b = 0

    let registered st n (pv : PVersion.t) =
      match (n, pv.PVersion.v) with
      | DMA.Deb.Name.Orig (m, DMA.QAArch b), DMA.Deb.Version.Orig v ->
          register st ((m, b), v)
      | _ -> ([], [])

    (* apt's Assume of the alternative's solution: a version var, or the
       package var of a deferred alternative *)
    let continuation n (pv : PVersion.t) =
      match (n, pv.PVersion.v) with
      | (DMA.Deb.Name.Disjunct _ | DMA.Deb.Name.Soft _), DMA.Deb.Version.Atom a
        ->
          [ alt_name a ]
      | _ -> []

    let forced_to st n (pv : PVersion.t) =
      match (n, pv.PVersion.v) with
      | DMA.Deb.Name.Disjunct _, DMA.Deb.Version.Atom a -> Some (alt_name a)
      | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal _
      | DMA.Deb.Name.Selector a, DMA.Deb.Version.Ref _ ->
          if deferred st a then
            Some
              (match pv.PVersion.v with
              | DMA.Deb.Version.Ref (m, _) -> DMA.Deb.Name.Orig m
              | _ -> DMA.Deb.Name.Orig (fst a))
          else None
      | _ -> None

    (* a selector decided to a provider or real version is apt's version var
       popping, unless the atom is deferred and the var was the package's
       all along *)
    let version_of st n (pv : PVersion.t) =
      match (n, pv.PVersion.v) with
      | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal w
        when not (deferred st a) ->
          let on = DMA.Deb.Name.Orig (fst a) in
          Some (on, tag on (DMA.Deb.Version.Orig w))
      | DMA.Deb.Name.Selector a, DMA.Deb.Version.Ref (m, w)
        when not (deferred st a) ->
          let on = DMA.Deb.Name.Orig m in
          Some (on, tag on (DMA.Deb.Version.Orig w))
      | _ -> None

    let head = head
    let same_name a b = PName.compare a b = 0
    let negation = negation
  end

  module Heap = Work_heap.Make (Driver)

  type t = Heap.t

  let create () = Heap.create (create_state ())

  (* The choice among a name's candidates apt would make.  An alternative
     nothing satisfies is not among apt's solutions (AllTargets skips it) or
     is one it has rejected (Solve takes the first undecided), and so is a
     rejected provider or version of a selector's name: trying either would
     burn a backtrack and permute the shadow heap where apt's never moves,
     so it is ranked out whenever a live alternative, or the escape,
     remains.  A decision apt kept across a Pop that PubGrub undid is made
     again, to the same version.  And a folded clause takes the first
     undecided solution of the intersection. *)
  let keep f cands = match List.filter f cands with [] -> cands | live -> live

  let live_filter st ~assigned n cands =
    let live_pkg m w =
      live_at st ~pkgvar:true m w && live_at st ~pkgvar:false m w
    in
    keep
      (fun (pv : PVersion.t) ->
        match (n, pv.PVersion.v) with
        | _, DMA.Deb.Version.Atom a -> solutions st (Some assigned) a > 0
        | DMA.Deb.Name.Selector a, DMA.Deb.Version.RefReal w ->
            live_pkg (fst a) w
        | _, DMA.Deb.Version.Ref (m, w) -> live_pkg m w
        | _ -> true)
      cands

  let kept_filter t n cands =
    match Heap.kept t n with
    | Some v when List.exists (fun c -> PVersion.compare c v = 0) cands -> [ v ]
    | _ -> cands

  let narrowed_filter st ~assigned n cands =
    match
      List.find_opt
        (fun (p, _) -> installed_at ~assigned p)
        (Hashtbl.find_all st.narrowed n)
    with
    | None -> cands
    | Some (_, na) ->
        keep
          (fun (pv : PVersion.t) ->
            match pv.PVersion.v with
            | DMA.Deb.Version.RefReal w -> sat (snd na) w
            (* an explicit :b has no real candidate: b's own package is a
               Ref, providing the name at its version *)
            | DMA.Deb.Version.Ref ((m, DMA.QAArch _), w)
              when String.equal m (fst (fst na))
                   &&
                   match snd (fst na) with
                   | DMA.QAExact _ -> true
                   | _ -> false ->
                sat (snd na) w
            | DMA.Deb.Version.Ref ((m, DMA.QAArch b), w) -> (
                match stanza ((m, b), w) with
                | Some stz ->
                    provides_matching stz (fst (fst na)) (snd na) <> []
                | None -> false)
            | _ -> true)
          cands

  let filter (t : t) ~assigned n cands =
    let st = t.Heap.d in
    live_filter st ~assigned n cands
    |> kept_filter t n
    |> narrowed_filter st ~assigned n

  (* A name only conflicts have reached admits absence, its greatest
     version, and is decided last: deciding it earlier would forbid a
     dependency that later comes to require it.  apt has no work item for
     such a name, so the shadow heap never sees it.  Only a real name has
     the absent version; asking the partial solution about a clause name
     would compare its atom set. *)
  let admits_bot ~assigned tn =
    match tn with
    | DMA.Deb.Name.Orig _ -> (
        match assigned tn with
        | PG.Entailed r -> PG.Ranges.contains (tag tn DMA.Deb.Version.Bot) r
        | _ -> false)
    | _ -> false

  (* apt never resolves a clause one of whose alternatives is already
     satisfied: it leaves the clause alone and installs nothing for it.
     PubGrub has to decide the disjunct either way, so the nearest thing is
     to decide it at no cost -- an alternative, or a provider of one, the
     solution already holds.  Where it holds none, and for every other
     name, PVersion.compare's answer stands unchanged; the tool order first
     narrows the candidates to those apt would consider. *)
  let hooks : (unit, name, PG.selection, PVersion.t) Pac_common.Order.driver =
   fun order () ->
    let next pick ~assigned open_names =
      match
        List.filter (fun (tn, _) -> not (admits_bot ~assigned tn)) open_names
      with
      | [] -> fst (List.hd open_names)
      | req -> pick ~assigned req
    in
    let choose filter ~assigned n cands =
      let cands = filter ~assigned n cands in
      match free_of ~assigned n cands with
      | [] -> greatest cands
      | free -> greatest free
    in
    match order with
    | `Tool ->
        let t = create () in
        Pac_common.Order.make
          ~next:(next (Heap.next t))
          ~choose:(choose (filter t))
          ~finish:(fun () -> Heap.report t)
          ()
    | `Pubgrub ->
        Pac_common.Order.make
          ~next:(next (fun ~assigned:_ req -> fst (List.hd req)))
          ~choose:(choose (fun ~assigned:_ _ cands -> cands))
          ()
    | `Random seed -> Pac_common.Order.random seed
end
