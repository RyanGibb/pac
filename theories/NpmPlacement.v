From Stdlib Require Import MSets List Bool.
From PackageCalculus Require Import Prelude Core Versions Semver Placement
  NpmCommon.

Create HintDb cmp_npl.
Create Rewrite HintDb cmp_npl.

Module NpmPlacement (N V : UsualOrderedType) (PM : SemverMatch V).
  Module VS := FSetUOT V.
  Include NpmCommon N V VS.
  Module NKey := PairUOT N N.
  Module KeySet := FSetUOT NKey.
  Module RPkgF := UOTCompareFacts RPkg.
  #[local] Hint Rewrite RPkgF.compare_eq_iff : cmp_npl.
  #[local] Hint Extern 1 => cmp_by RPkgF.compare_antisym : cmp_npl.
  #[local] Hint Extern 1 => cmp_by RPkgF.compare_lt_trans : cmp_npl.

  Module Sv := Semver V VS PM.
  Include Sv.

  Module Occ.
    Inductive occ : Type :=
    | Top
    | Reg (m : N.t) (v : V.t).
    Definition t := occ.

    Definition rank (x : t) : nat := match x with Top => 0 | Reg _ _ => 1 end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq => match x, y with
              | Reg m1 v1, Reg m2 v2 => RPkg.compare (m1, v1) (m2, v2)
              | _, _ => Eq
              end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_npl. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_npl. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_npl. Qed.
  End Occ.

  Module OccOT := UOTFromCompare Occ.
  Module Pl := Placement N OccOT.

  Record Dependency : Type := MkDep
    { d_dir : N.t
    ; d_name : N.t
    ; d_range : Range
    ; d_dev : bool
    ; d_optional : bool }.

  Record PeerDependency : Type := MkPeer
    { p_dir : N.t
    ; p_name : N.t
    ; p_range : Range
    ; p_optional : bool }.

  (* The relation fields are lists: sets would demand an order on Range
     used nowhere. *)
  Record Inst : Type := MkInst
    { inst_repo : RepoSet.t
    ; inst_deps : list (RPkg.t * Dependency)
    ; inst_peers : list (RPkg.t * PeerDependency)
    ; inst_ovr : list (N.t * Range)
    ; inst_root : N.t
    ; inst_rootDeps : list Dependency
    ; inst_rootPeers : list PeerDependency }.

  Definition ovrName (I : Inst) (a m : N.t) : N.t :=
    match lookupOvr (inst_ovr I) a with
    | Some _ => a
    | None => m
    end.

  Definition ovrRange (I : Inst) (a : N.t) (rg : Range) : Range :=
    match lookupOvr (inst_ovr I) a with
    | Some rg' => rg'
    | None => rg
    end.

  Definition cands (I : Inst) (m : N.t) (rg : Range) : VS.t :=
    rangeEval rg (realVersions (inst_repo I) m).

  Record Edge : Type := MkEdge
    { e_dir : N.t
    ; e_name : N.t
    ; e_range : Range
    ; e_peer : bool
    ; e_opt : bool }.

  Definition depEdge (I : Inst) (d : Dependency) : Edge :=
    let m := ovrName I (d_dir d) (d_name d) in
    let rg := ovrRange I (d_dir d) (d_range d) in
    MkEdge (d_dir d) m rg false
      (andb (d_optional d) (VS.is_empty (cands I m rg))).

  Definition peerEdge (I : Inst) (r : PeerDependency) : Edge :=
    MkEdge (p_dir r) (ovrName I (p_dir r) (p_name r))
      (ovrRange I (p_dir r) (p_range r)) true (p_optional r).

  Definition activeDeps (I : Inst) (x : Occ.t) : list Dependency :=
    match x with
    | Occ.Top => inst_rootDeps I
    | Occ.Reg m v =>
        List.filter (fun d => negb (d_dev d)) (ownedBy (m, v) (inst_deps I))
    end.

  Definition declPeers (I : Inst) (x : Occ.t) : list PeerDependency :=
    match x with
    | Occ.Top => inst_rootPeers I
    | Occ.Reg m v => ownedBy (m, v) (inst_peers I)
    end.

  Definition replaced (ds : list Dependency) (r : PeerDependency) : bool :=
    List.existsb (fun d => NEqb.eqb (d_dir d) (p_dir r)) ds.

  Definition edgesOf (I : Inst) (x : Occ.t) : list Edge :=
    List.map (depEdge I) (activeDeps I x) ++
    List.map (peerEdge I)
      (List.filter (fun r => negb (replaced (activeDeps I x) r))
         (declPeers I x)).

  Definition Sat (I : Inst) (e : Edge) (x : Occ.t) : Prop :=
    exists u, x = Occ.Reg (e_name e) u /\
      VS.In u (cands I (e_name e) (e_range e)).

  Definition EdgeOk (I : Inst) (L : Pl.Layout.t) (l : Pl.Path.t) (e : Edge)
      : Prop :=
    match Pl.walk L l (e_dir e) with
    | None => e_opt e = true
    | Some (l', x) => Pl.Suffix l' (Pl.land (e_peer e) l) /\ Sat I e x
    end.

  Module SOkk := SetOps NKey NKey KeySet KeySet.
  Definition keysOf (I : Inst) : KeySet.t :=
    SOkk.ofList
      (List.map (fun d => (d_dir d, e_name (depEdge I d)))
         (inst_rootDeps I ++ List.map snd (inst_deps I)) ++
       List.map (fun r => (p_dir r, e_name (peerEdge I r)))
         (inst_rootPeers I ++ List.map snd (inst_peers I))).

  Record IsResolution (I : Inst) (L : Pl.Layout.t) : Prop :=
    { res_avail :
        forall l a x, Pl.Layout.In (l, (a, x)) L ->
        exists m v, x = Occ.Reg m v /\ KeySet.In (a, m) (keysOf I) /\
          RepoSet.In (m, v) (inst_repo I)
    ; res_occupancy :
        forall l a x x', Pl.Layout.In (l, (a, x)) L ->
        Pl.Layout.In (l, (a, x')) L -> x = x'
    ; res_tree :
        forall b l p, Pl.Layout.In (b :: l, p) L ->
        exists x, Pl.Layout.In (l, (b, x)) L
    ; res_root : forall e, In e (edgesOf I Occ.Top) -> EdgeOk I L nil e
    ; res_edges :
        forall l a x, Pl.Layout.In (l, (a, x)) L ->
        forall e, In e (edgesOf I x) -> EdgeOk I L (a :: l) e }.

  Module SOkp := SetOps NKey Pl.Pkg KeySet Pl.PkgSet.
  Module SOvp := SetOps V Pl.Pkg VS Pl.PkgSet.
  Definition placeRepo (I : Inst) : Pl.PkgSet.t :=
    SOkp.unionMap (fun k =>
        SOvp.map (fun v => (fst k, Occ.Reg (snd k) v))
          (realVersions (inst_repo I) (snd k)))
      (keysOf I).

  Lemma mem_placeRepo : forall I a x,
      Pl.PkgSet.In (a, x) (placeRepo I) <->
      exists m v, x = Occ.Reg m v /\ KeySet.In (a, m) (keysOf I) /\
        RepoSet.In (m, v) (inst_repo I).
  Proof.
    intros I a x; unfold placeRepo; rewrite SOkp.mem_unionMap; split.
    - intros [[a' m] [Hk Hv]]; apply SOvp.mem_map in Hv.
      destruct Hv as [v [Hv E]]; injection E as -> ->.
      exists m, v; split; [reflexivity |].
      split; [exact Hk | apply mem_realVersions; exact Hv].
    - intros [m [v [-> [Hk Hv]]]]; exists (a, m); split; [exact Hk |].
      apply SOvp.mem_map; exists v; split; [| reflexivity].
      apply mem_realVersions; exact Hv.
  Qed.

  Definition rootOcc (I : Inst) : Pl.Pkg.t := (inst_root I, Occ.Top).

  Definition occs (I : Inst) : Pl.PkgSet.t :=
    Pl.PkgSet.add (rootOcc I) (placeRepo I).

  Module SOvo := SetOps V OccOT VS Pl.VSet.
  Definition acceptsIn (m : N.t) (rg : Range) (vs : VS.t) : Pl.VSet.t :=
    SOvo.map (Occ.Reg m) (rangeEval rg vs).

  Definition accepts (I : Inst) (e : Edge) : Pl.VSet.t :=
    acceptsIn (e_name e) (e_range e) (realVersions (inst_repo I) (e_name e)).

  Lemma mem_accepts : forall I e x,
      Pl.VSet.In x (accepts I e) <-> Sat I e x.
  Proof.
    intros I e x; unfold accepts, acceptsIn, Sat, cands; rewrite SOvo.mem_map.
    split; intros [u [H1 H2]]; exists u; split; assumption.
  Qed.

  Definition kindb (pe o : bool) (e : Edge) : bool :=
    andb (Bool.eqb (e_peer e) pe) (Bool.eqb (e_opt e) o).

  Module SOpd := SetOps Pl.Pkg Pl.C.DepElt Pl.PkgSet Pl.C.DepRel.
  Definition edgeRel (I : Inst) (pe o : bool) : Pl.C.DepRel.t :=
    SOpd.unionMap (fun p =>
        SOpd.ofList
          (List.map (fun e => (p, (e_dir e, accepts I e)))
             (List.filter (kindb pe o) (edgesOf I (snd p)))))
      (occs I).

  Lemma mem_edgeRel : forall I pe o p n vs,
      Pl.C.DepRel.In (p, (n, vs)) (edgeRel I pe o) <->
      Pl.PkgSet.In p (occs I) /\
      exists e, In e (edgesOf I (snd p)) /\ e_peer e = pe /\ e_opt e = o /\
        n = e_dir e /\ vs = accepts I e.
  Proof.
    intros I pe o p n vs; unfold edgeRel; rewrite SOpd.mem_unionMap; split.
    - intros [q [Hq H]]; apply SOpd.mem_ofList, in_map_iff in H.
      destruct H as [e [E He]]; injection E as <- <- <-.
      apply filter_In in He; destruct He as [He Hk].
      unfold kindb in Hk; apply andb_true_iff in Hk.
      rewrite !Bool.eqb_true_iff in Hk; destruct Hk as [Hp Ho].
      split; [exact Hq |]; exists e; auto.
    - intros [Hq [e [He [Hp [Ho [-> ->]]]]]]; exists p; split; [exact Hq |].
      apply SOpd.mem_ofList, in_map_iff; exists e; split; [reflexivity |].
      apply filter_In; split; [exact He |].
      unfold kindb; rewrite Hp, Ho, !Bool.eqb_reflx; reflexivity.
  Qed.

  Definition tr (I : Inst) : Pl.Inst :=
    {| Pl.inst_repo := placeRepo I
     ; Pl.inst_deps := edgeRel I false false
     ; Pl.inst_peers := edgeRel I true false
     ; Pl.inst_optDeps := edgeRel I false true
     ; Pl.inst_optPeers := edgeRel I true true
     ; Pl.inst_root := rootOcc I |}.

  Lemma rel_tr : forall I pe o, Pl.rel (tr I) pe o = edgeRel I pe o.
  Proof. intros I [|] [|]; reflexivity. Qed.

  Lemma edgeOk_meets : forall I L l e,
      EdgeOk I L l e <->
      Pl.Meets L l (Pl.land (e_peer e) l) (e_dir e) (accepts I e) (e_opt e).
  Proof.
    intros I L l e; unfold EdgeOk, Pl.Meets, Pl.Resolves.
    destruct (Pl.walk L l (e_dir e)) as [[l' x] |]; split.
    - intros [Hs Hx]; left; exists l', x; split; [reflexivity |].
      split; [exact Hs | apply mem_accepts; exact Hx].
    - intros [[l0 [u [E [Hs Hu]]]] | [_ E]]; [| discriminate E].
      injection E as <- <-; split; [exact Hs | apply mem_accepts; exact Hu].
    - intro Ho; right; split; [exact Ho | reflexivity].
    - intros [[l0 [u [E _]]] | [Ho _]]; [discriminate E | exact Ho].
  Qed.

  Theorem tr_resolution : forall I L,
      Pl.IsResolution (tr I) L <-> IsResolution I L.
  Proof.
    intros I L; split.
    - intros [Hsub Hocc Htree Hroot Hdeps].
      assert (Hholds : forall p l, Pl.Holds (tr I) L l p ->
                 Pl.PkgSet.In p (occs I) ->
                 forall e, In e (edgesOf I (snd p)) -> EdgeOk I L l e).
      { intros p l Hh Hp e He; apply edgeOk_meets, Hh.
        rewrite rel_tr, mem_edgeRel; split; [exact Hp |].
        exists e; auto. }
      constructor.
      + intros l a x H; apply mem_placeRepo, (Hsub l (a, x) H).
      + exact Hocc.
      + exact Htree.
      + exact (Hholds (rootOcc I) nil Hroot
                 (proj2 (Pl.PkgSet.add_spec _ _ _) (or_introl eq_refl))).
      + intros l a x H; apply (Hholds (a, x) (a :: l) (Hdeps l (a, x) H)).
        apply Pl.PkgSet.add_spec; right; exact (Hsub l (a, x) H).
    - intros [Havail Hocc Htree Hroot Hedges].
      assert (Hholds : forall p l,
                 (forall e, In e (edgesOf I (snd p)) -> EdgeOk I L l e) ->
                 Pl.Holds (tr I) L l p).
      { intros p l He pe o n vs HE; rewrite rel_tr, mem_edgeRel in HE.
        destruct HE as [_ [e [Hin [<- [<- [-> ->]]]]]].
        apply edgeOk_meets, He; exact Hin. }
      constructor.
      + intros l [a x] H; apply mem_placeRepo, (Havail l a x H).
      + exact Hocc.
      + exact Htree.
      + apply Hholds; exact Hroot.
      + intros l [a x] H; apply Hholds; exact (Hedges l a x H).
  Qed.

  (* Placement's Reduction is named in full: an alias of it inside this
     functor trips a kernel anomaly when the functor is applied. *)
  Definition reduceReal (I : Inst) (depth : nat) : Pl.Reduction.T.PkgSet.t :=
    Pl.Reduction.reduceReal (tr I) depth.

  Definition reduceDeps (I : Inst) (depth : nat) : Pl.Reduction.T.DepRel.t :=
    Pl.Reduction.reduceDeps (tr I) depth.

  Definition rootPkg (I : Inst) : Pl.Reduction.T.Pkg.t :=
    Pl.Reduction.rootPkg (tr I).

  Theorem npm_soundness : forall I depth S,
      Pl.Reduction.T.IsResolution (reduceReal I depth) (reduceDeps I depth)
        (rootPkg I) S ->
      IsResolution I (Pl.Reduction.placementResolution S) /\
      Pl.Depth depth (Pl.Reduction.placementResolution S).
  Proof.
    intros I depth S H.
    destruct (Pl.Reduction.placement_soundness _ _ _ H) as [H1 H2].
    split; [apply tr_resolution; exact H1 | exact H2].
  Qed.

  Theorem npm_completeness : forall I depth L,
      IsResolution I L -> Pl.Depth depth L ->
      Pl.Reduction.T.IsResolution (reduceReal I depth) (reduceDeps I depth)
        (rootPkg I) (Pl.Reduction.coreResolution (tr I) depth L).
  Proof.
    intros I depth L H Hd; apply Pl.Reduction.placement_completeness;
      [apply tr_resolution; exact H | exact Hd].
  Qed.

  Theorem npm_roundtrip : forall I depth L,
      IsResolution I L -> Pl.Depth depth L ->
      Pl.Reduction.placementResolution
        (Pl.Reduction.coreResolution (tr I) depth L) = L.
  Proof.
    intros I depth L H Hd;
      apply Pl.Reduction.placementResolution_coreResolution;
      [apply tr_resolution; exact H | exact Hd].
  Qed.

  Module Lookup.
    Definition AgreesAtKey (I' I : Inst) (a : N.t) : Prop :=
      forall m v,
        (KeySet.In (a, m) (keysOf I') /\ RepoSet.In (m, v) (inst_repo I')) <->
        (KeySet.In (a, m) (keysOf I) /\ RepoSet.In (m, v) (inst_repo I)).

    Lemma keyVersions_agree : forall I' I a, AgreesAtKey I' I a ->
        Pl.repoVersions (placeRepo I') a = Pl.repoVersions (placeRepo I) a.
    Proof.
      intros I' I a H; apply Pl.repoVersions_ext; intro x.
      rewrite !mem_placeRepo; split; intros [m [v [-> Hk]]];
        exists m, v; split; try reflexivity; apply H; exact Hk.
    Qed.

    Definition nameInst (I : Inst) : Pl.Inst :=
      {| Pl.inst_repo := placeRepo I
       ; Pl.inst_deps := Pl.C.DepRel.empty
       ; Pl.inst_peers := Pl.C.DepRel.empty
       ; Pl.inst_optDeps := Pl.C.DepRel.empty
       ; Pl.inst_optPeers := Pl.C.DepRel.empty
       ; Pl.inst_root := rootOcc I |}.

    Theorem versions_lookupLoc : forall I I' depth l a,
        Pl.Reduction.Lookup.Reached (tr I) depth (Pl.Reduction.Name.Loc l a) ->
        AgreesAtKey I' I a ->
        Pl.Reduction.T.versions (reduceReal I depth)
          (Pl.Reduction.Name.Loc l a) =
        Pl.Reduction.versions (nameInst I') depth (Pl.Reduction.Name.Loc l a).
    Proof.
      intros I I' depth l a H Ha; unfold reduceReal.
      rewrite (Pl.Reduction.Lookup.versions_lookupLoc _ _ _ _ H).
      unfold Pl.Reduction.versions, Pl.Reduction.Lookup.nameSubInst, nameInst,
        tr, rootOcc; cbn [Pl.inst_repo].
      rewrite Pl.Reduction.Lookup.versions_fibre, (keyVersions_agree _ _ _ Ha).
      reflexivity.
    Qed.

    Theorem versions_lookupWalk : forall I I' depth l a,
        Pl.Reduction.Lookup.Reached (tr I) depth (Pl.Reduction.Name.Walk l a) ->
        AgreesAtKey I' I a ->
        Pl.Reduction.T.versions (reduceReal I depth)
          (Pl.Reduction.Name.Walk l a) =
        Pl.Reduction.versions (nameInst I') depth (Pl.Reduction.Name.Walk l a).
    Proof.
      intros I I' depth l a H Ha; unfold reduceReal.
      rewrite (Pl.Reduction.Lookup.versions_lookupWalk _ _ _ _ H).
      unfold Pl.Reduction.versions, Pl.Reduction.Lookup.nameSubInst, nameInst,
        tr, rootOcc; cbn [Pl.inst_repo].
      rewrite Pl.Reduction.Lookup.versions_fibre, (keyVersions_agree _ _ _ Ha).
      reflexivity.
    Qed.

    Definition atomOf (lam : Pl.Path.t) (e : Edge) (xs : Pl.VSet.t)
        : Pl.Reduction.T.Dependees.t :=
      (Pl.Reduction.Name.Walk lam (e_dir e),
       Pl.Reduction.optAccept (e_opt e) (Pl.land (e_peer e) lam) xs).

    Definition edgeAtom (I : Inst) (lam : Pl.Path.t) (e : Edge)
        : Pl.Reduction.T.Dependees.t :=
      atomOf lam e (accepts I e).

    Module SOhh := SetOps Pl.Reduction.T.Dependees Pl.Reduction.T.Dependees
      Pl.Reduction.T.DependeesSet Pl.Reduction.T.DependeesSet.
    Definition occAtoms (I : Inst) (lam : Pl.Path.t) (x : Occ.t)
        : Pl.Reduction.T.DependeesSet.t :=
      SOhh.ofList (List.map (edgeAtom I lam) (edgesOf I x)).

    Lemma edgeAtoms_tr : forall I p lam, Pl.PkgSet.In p (occs I) ->
        Pl.Reduction.edgeAtoms (tr I) p lam = occAtoms I lam (snd p).
    Proof.
      intros I p lam Hp; apply Pl.Reduction.T.DependeesSet.ext; intro h.
      rewrite Pl.Reduction.mem_edgeAtoms; unfold occAtoms.
      rewrite SOhh.mem_ofList, in_map_iff; split.
      - intros [pe [o [n [vs [HE ->]]]]]; rewrite rel_tr, mem_edgeRel in HE.
        destruct HE as [_ [e [He [<- [<- [-> ->]]]]]].
        exists e; split; [reflexivity | exact He].
      - intros [e [<- He]].
        exists (e_peer e), (e_opt e), (e_dir e), (accepts I e).
        split; [| reflexivity].
        rewrite rel_tr, mem_edgeRel; split; [exact Hp |].
        exists e; auto.
    Qed.

    Theorem dependees_lookupRoot : forall I depth,
        Pl.Reduction.T.dependees (reduceDeps I depth) (rootPkg I) =
        occAtoms I nil Occ.Top.
    Proof.
      intros I depth; unfold reduceDeps, rootPkg.
      rewrite Pl.Reduction.dependees_reduceDeps.
      - cbn [Pl.Reduction.rootPkg Pl.Reduction.dependees tr Pl.inst_root
               rootOcc snd]; unfold Pl.Reduction.occDeps.
        rewrite (edgeAtoms_tr I (rootOcc I) nil)
          by (apply Pl.PkgSet.add_spec; left; reflexivity).
        apply Pl.Reduction.T.DependeesSet.ext; intro h.
        rewrite Pl.Reduction.T.DependeesSet.union_spec.
        cbn [Pl.par Pl.Reduction.treeAtom rootOcc snd]; split.
        + intros [H | H]; [| exact H].
          destruct (Pl.Reduction.T.DependeesSet.empty_spec H).
        + intro H; right; exact H.
      - apply Pl.Reduction.mem_reduceReal; split; [exact Logic.I |].
        apply Pl.Reduction.T.VSet.singleton_spec; reflexivity.
    Qed.

    Theorem dependees_lookupOcc : forall I depth l a x,
        Pl.Reduction.T.PkgSet.In
          (Pl.Reduction.Name.Loc l a, Pl.Reduction.Version.Occ x)
          (reduceReal I depth) ->
        Pl.Reduction.T.dependees (reduceDeps I depth)
          (Pl.Reduction.Name.Loc l a, Pl.Reduction.Version.Occ x) =
        Pl.Reduction.T.DependeesSet.union
          (Pl.Reduction.treeAtom (placeRepo I) l) (occAtoms I (a :: l) x).
    Proof.
      intros I depth l a x H; unfold reduceDeps.
      rewrite (Pl.Reduction.dependees_reduceDeps _ _ _ H).
      apply Pl.Reduction.mem_reduceReal in H; destruct H as [_ H].
      apply Pl.Reduction.mem_versions_loc in H.
      destruct H as [E | [v [_ [Hv E]]]]; [discriminate E |].
      injection E as ->; cbn [Pl.Reduction.dependees].
      unfold Pl.Reduction.occDeps.
      rewrite (edgeAtoms_tr I (a, v) (a :: l))
        by (apply Pl.PkgSet.add_spec; right; exact Hv).
      reflexivity.
    Qed.

    Theorem dependees_lookupWalk : forall I depth l a w,
        Pl.Reduction.T.PkgSet.In (Pl.Reduction.Name.Walk l a, w)
          (reduceReal I depth) ->
        Pl.Reduction.T.dependees (reduceDeps I depth)
          (Pl.Reduction.Name.Walk l a, w) =
        Pl.Reduction.walkDeps l a w.
    Proof.
      intros I depth l a w H.
      exact (Pl.Reduction.Lookup.dependees_lookupWalk _ _ _ _ _ H).
    Qed.

    Theorem dependees_lookupAbsent : forall I depth l a,
        Pl.Reduction.T.dependees (reduceDeps I depth)
          (Pl.Reduction.Name.Loc l a, Pl.Reduction.Version.Bot) =
        Pl.Reduction.T.DependeesSet.empty.
    Proof. intros; apply Pl.Reduction.Lookup.dependees_lookupAbsent. Qed.

    Definition AgreesAtName (I' I : Inst) (m : N.t) : Prop :=
      forall u, RepoSet.In (m, u) (inst_repo I') <->
                RepoSet.In (m, u) (inst_repo I).

    Definition AgreesAtOcc (I' I : Inst) (x : Occ.t) : Prop :=
      inst_ovr I' = inst_ovr I /\
      activeDeps I' x = activeDeps I x /\ declPeers I' x = declPeers I x /\
      forall d, In d (activeDeps I x) -> d_optional d = true ->
        AgreesAtName I' I (ovrName I (d_dir d) (d_name d)).

    Lemma cands_agree : forall I' I m rg, AgreesAtName I' I m ->
        cands I' m rg = cands I m rg.
    Proof.
      intros I' I m rg Hr; unfold cands; f_equal.
      apply VS.ext; intro u; rewrite !mem_realVersions; exact (Hr u).
    Qed.

    Lemma edgesOf_agree : forall I' I x, AgreesAtOcc I' I x ->
        edgesOf I' x = edgesOf I x.
    Proof.
      intros I' I x [Ho [Hd [Hp Hr]]].
      assert (Hn : forall a m, ovrName I' a m = ovrName I a m)
        by (intros a m; unfold ovrName; rewrite Ho; reflexivity).
      assert (Hg : forall a rg, ovrRange I' a rg = ovrRange I a rg)
        by (intros a rg; unfold ovrRange; rewrite Ho; reflexivity).
      unfold edgesOf; rewrite Hd, Hp; f_equal.
      - apply map_ext_in; intros d Hin; unfold depEdge; cbv zeta.
        rewrite Hn, Hg.
        destruct (d_optional d) eqn:Hopt; [| reflexivity]; cbn [andb].
        rewrite (cands_agree I' I _ _ (Hr d Hin Hopt)); reflexivity.
      - apply map_ext; intro r; unfold peerEdge; rewrite Hn, Hg; reflexivity.
    Qed.

    Lemma edgeAtom_agree : forall I' I lam e, AgreesAtName I' I (e_name e) ->
        edgeAtom I' lam e = edgeAtom I lam e.
    Proof.
      intros I' I lam e Hr; unfold edgeAtom, accepts.
      replace (realVersions (inst_repo I') (e_name e))
        with (realVersions (inst_repo I) (e_name e)); [reflexivity |].
      apply VS.ext; intro u; rewrite !mem_realVersions; symmetry; exact (Hr u).
    Qed.

    Theorem occAtoms_parts : forall I Ix (at_ : Edge -> Inst) lam x,
        AgreesAtOcc Ix I x ->
        (forall e, In e (edgesOf I x) -> AgreesAtName (at_ e) I (e_name e)) ->
        occAtoms I lam x =
        SOhh.ofList (List.map (fun e => edgeAtom (at_ e) lam e) (edgesOf Ix x)).
    Proof.
      intros I Ix at_ lam x Hx He; unfold occAtoms.
      rewrite (edgesOf_agree _ _ _ Hx); f_equal.
      apply map_ext_in; intros e Hin.
      exact (eq_sym (edgeAtom_agree _ _ _ _ (He e Hin))).
    Qed.

    Theorem treeAtom_agree : forall I' I b l, AgreesAtKey I' I b ->
        Pl.Reduction.treeAtom (placeRepo I') (b :: l) =
        Pl.Reduction.treeAtom (placeRepo I) (b :: l).
    Proof.
      intros I' I b l H; cbn [Pl.Reduction.treeAtom].
      rewrite (keyVersions_agree _ _ _ H); reflexivity.
    Qed.
  End Lookup.
End NpmPlacement.
