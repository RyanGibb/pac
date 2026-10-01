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

  Definition depEdge (Vq : N.t -> VS.t) (I : Inst) (d : Dependency) : Edge :=
    let m := ovrName I (d_dir d) (d_name d) in
    let rg := ovrRange I (d_dir d) (d_range d) in
    MkEdge (d_dir d) m rg false
      (andb (d_optional d) (VS.is_empty (rangeEval rg (Vq m)))).

  Definition peerEdge (I : Inst) (theta : PeerDependency) : Edge :=
    MkEdge (p_dir theta) (ovrName I (p_dir theta) (p_name theta))
      (ovrRange I (p_dir theta) (p_range theta)) true (p_optional theta).

  Definition activeDeps (I : Inst) (o : Occ.t) : list Dependency :=
    match o with
    | Occ.Top => inst_rootDeps I
    | Occ.Reg m v =>
        List.filter (fun d => negb (d_dev d)) (ownedBy (m, v) (inst_deps I))
    end.

  Definition declPeers (I : Inst) (o : Occ.t) : list PeerDependency :=
    match o with
    | Occ.Top => inst_rootPeers I
    | Occ.Reg m v => ownedBy (m, v) (inst_peers I)
    end.

  Definition replaced (ds : list Dependency) (theta : PeerDependency) : bool :=
    List.existsb (fun d => NEqb.eqb (d_dir d) (p_dir theta)) ds.

  Definition edgesOfBy (Vq : N.t -> VS.t) (I : Inst) (o : Occ.t)
      : list Edge :=
    List.map (depEdge Vq I) (activeDeps I o) ++
    List.map (peerEdge I)
      (List.filter (fun theta => negb (replaced (activeDeps I o) theta))
         (declPeers I o)).

  Definition edgesOf (I : Inst) (o : Occ.t) : list Edge :=
    edgesOfBy (realVersions (inst_repo I)) I o.

  Definition Sat (I : Inst) (e : Edge) (o : Occ.t) : Prop :=
    exists u, o = Occ.Reg (e_name e) u /\
      VS.In u (cands I (e_name e) (e_range e)).

  Definition EdgeOk (I : Inst) (L : Pl.Layout.t) (l : Pl.Path.t) (e : Edge)
      : Prop :=
    match Pl.walk L l (e_dir e) with
    | None => e_opt e = true
    | Some (l', o) => Pl.Suffix l' (Pl.land (e_peer e) l) /\ Sat I e o
    end.

  Module SOkk := SetOps NKey NKey KeySet KeySet.
  Definition keysOf (I : Inst) : KeySet.t :=
    SOkk.ofList
      (List.map
         (fun d => (d_dir d, e_name (depEdge (realVersions (inst_repo I)) I d)))
         (inst_rootDeps I ++ List.map snd (inst_deps I)) ++
       List.map (fun theta => (p_dir theta, e_name (peerEdge I theta)))
         (inst_rootPeers I ++ List.map snd (inst_peers I))).

  Record IsResolution (I : Inst) (L : Pl.Layout.t) : Prop :=
    { res_subset :
        forall l a o, Pl.Layout.In (l, (a, o)) L ->
        exists m v, o = Occ.Reg m v /\ KeySet.In (a, m) (keysOf I) /\
          RepoSet.In (m, v) (inst_repo I)
    ; res_location_unique :
        forall l a o o', Pl.Layout.In (l, (a, o)) L ->
        Pl.Layout.In (l, (a, o')) L -> o = o'
    ; res_tree :
        forall b l p, Pl.Layout.In (b :: l, p) L ->
        exists o, Pl.Layout.In (l, (b, o)) L
    ; res_root : forall e, In e (edgesOf I Occ.Top) -> EdgeOk I L nil e
    ; res_dep_resolution :
        forall l a o, Pl.Layout.In (l, (a, o)) L ->
        forall e, In e (edgesOf I o) -> EdgeOk I L (a :: l) e }.

  Module Reduction.
    Module SOkp := SetOps NKey Pl.Pkg KeySet Pl.PkgSet.
    Module SOvp := SetOps V Pl.Pkg VS Pl.PkgSet.
    Definition placeRepo (I : Inst) : Pl.PkgSet.t :=
      SOkp.unionMap (fun k =>
          SOvp.map (fun v => (fst k, Occ.Reg (snd k) v))
            (realVersions (inst_repo I) (snd k)))
        (keysOf I).

    Lemma mem_placeRepo : forall I a o,
        Pl.PkgSet.In (a, o) (placeRepo I) <->
        exists m v, o = Occ.Reg m v /\ KeySet.In (a, m) (keysOf I) /\
          RepoSet.In (m, v) (inst_repo I).
    Proof.
      intros I a o; unfold placeRepo; rewrite SOkp.mem_unionMap; split.
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

    Lemma mem_accepts : forall I e o,
        Pl.VSet.In o (accepts I e) <-> Sat I e o.
    Proof.
      intros I e o; unfold accepts, acceptsIn, Sat, cands; rewrite SOvo.mem_map.
      split; intros [u [H1 H2]]; exists u; split; assumption.
    Qed.

    Definition kindb (peer optional : bool) (e : Edge) : bool :=
      andb (Bool.eqb (e_peer e) peer) (Bool.eqb (e_opt e) optional).

    Module SOpd := SetOps Pl.Pkg Pl.C.DepElt Pl.PkgSet Pl.C.DepRel.
    Definition edgeRel (I : Inst) (peer optional : bool) : Pl.C.DepRel.t :=
      SOpd.unionMap (fun p =>
          SOpd.ofList
            (List.map (fun e => (p, (e_dir e, accepts I e)))
               (List.filter (kindb peer optional) (edgesOf I (snd p)))))
        (occs I).

    Lemma mem_edgeRel : forall I peer optional a' o n vs,
        Pl.C.DepRel.In ((a', o), (n, vs)) (edgeRel I peer optional) <->
        Pl.PkgSet.In (a', o) (occs I) /\
        exists e, In e (edgesOf I o) /\ e_peer e = peer /\
          e_opt e = optional /\
          n = e_dir e /\ vs = accepts I e.
    Proof.
      intros I peer optional a' o n vs; unfold edgeRel;
        rewrite SOpd.mem_unionMap; split.
      - intros [q [Hq H]]; apply SOpd.mem_ofList, in_map_iff in H.
        destruct H as [e [E He]]; injection E as -> <- <-.
        apply filter_In in He; destruct He as [He Hk].
        unfold kindb in Hk; apply andb_true_iff in Hk.
        rewrite !Bool.eqb_true_iff in Hk; destruct Hk as [Hp Ho].
        split; [exact Hq |]; exists e; auto.
      - intros [Hq [e [He [Hp [Ho [-> ->]]]]]]; exists (a', o);
          split; [exact Hq |].
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

    Lemma rel_tr : forall I peer optional,
        Pl.rel (tr I) peer optional = edgeRel I peer optional.
    Proof. intros I [|] [|]; reflexivity. Qed.

    Lemma edgeOk_meets : forall I L l e,
        EdgeOk I L l e <->
        Pl.Meets L l (Pl.land (e_peer e) l) (e_dir e) (accepts I e) (e_opt e).
    Proof.
      intros I L l e; unfold EdgeOk, Pl.Meets, Pl.Resolves.
      destruct (Pl.walk L l (e_dir e)) as [[l' o] |]; split.
      - intros [Hs Hx]; left; exists l', o; split; [reflexivity |].
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
        { intros [a' o] l Hh Hp e He; apply edgeOk_meets, Hh.
          rewrite rel_tr, mem_edgeRel; split; [exact Hp |].
          exists e; auto. }
        constructor.
        + intros l a o H; apply mem_placeRepo, (Hsub l (a, o) H).
        + exact Hocc.
        + exact Htree.
        + exact (Hholds (rootOcc I) nil Hroot
                   (proj2 (Pl.PkgSet.add_spec _ _ _) (or_introl eq_refl))).
        + intros l a o H; apply (Hholds (a, o) (a :: l) (Hdeps l a o H)).
          apply Pl.PkgSet.add_spec; right; exact (Hsub l (a, o) H).
      - intros [Havail Hocc Htree Hroot Hedges].
        assert (Hholds : forall p l,
                   (forall e, In e (edgesOf I (snd p)) -> EdgeOk I L l e) ->
                   Pl.Holds (tr I) L l p).
        { intros [a' o] l He peer optional n vs HE;
          rewrite rel_tr, mem_edgeRel in HE.
          destruct HE as [_ [e [Hin [<- [<- [-> ->]]]]]].
          apply edgeOk_meets, He; exact Hin. }
        constructor.
        + intros l [a o] H; apply mem_placeRepo, (Havail l a o H).
        + exact Hocc.
        + exact Htree.
        + apply Hholds; exact Hroot.
        + intros l a o H; apply Hholds; exact (Hedges l a o H).
    Qed.

    (* Placement's Reduction is named in full: an alias of it inside this
       functor trips a kernel anomaly when the functor is applied. *)
    Definition reduceReal (I : Inst) (depth : nat) : Pl.Reduction.T.PkgSet.t :=
      Pl.Reduction.reduceReal (tr I) depth.

    Definition reduceDeps (I : Inst) (depth : nat) : Pl.Reduction.T.DepRel.t :=
      Pl.Reduction.reduceDeps (tr I) depth.

    Definition rootPkg (I : Inst) : Pl.Reduction.T.Pkg.t :=
      Pl.Reduction.rootPkg (tr I).

    Theorem npm_placement_soundness : forall I depth S,
        Pl.Reduction.T.IsResolution (reduceReal I depth) (reduceDeps I depth)
          (rootPkg I) S ->
        IsResolution I
          (Pl.reachable (tr I) (Pl.Reduction.placementResolution S)) /\
        Pl.Depth depth
          (Pl.reachable (tr I) (Pl.Reduction.placementResolution S)).
    Proof.
      intros I depth S H.
      destruct (Pl.Reduction.placement_soundness _ _ _ H) as [H1 H2].
      split; [apply tr_resolution; exact H1 | exact H2].
    Qed.

    Theorem npm_placement_completeness : forall I depth L,
        IsResolution I L -> Pl.Depth depth L ->
        Pl.Reduction.T.IsResolution (reduceReal I depth) (reduceDeps I depth)
          (rootPkg I) (Pl.Reduction.coreResolution (tr I) depth L).
    Proof.
      intros I depth L H Hd; apply Pl.Reduction.placement_completeness;
        [apply tr_resolution; exact H | exact Hd].
    Qed.

    Theorem npm_placement_retraction : forall I depth L,
        IsResolution I L -> Pl.Depth depth L ->
        Pl.Reduction.placementResolution
          (Pl.Reduction.coreResolution (tr I) depth L) = L.
    Proof.
      intros I depth L H Hd;
        apply Pl.Reduction.placement_retraction;
        [apply tr_resolution; exact H | exact Hd].
    Qed.

    Module Lookup.
      Definition AgreesAtKey (I' I : Inst) (a : N.t) : Prop :=
        forall m v,
          (KeySet.In (a, m) (keysOf I') /\ RepoSet.In (m, v) (inst_repo I')) <->
          (KeySet.In (a, m) (keysOf I) /\ RepoSet.In (m, v) (inst_repo I)).

      Lemma keyVersions_agree : forall I' I a, AgreesAtKey I' I a ->
          Pl.C.versions (placeRepo I') a = Pl.C.versions (placeRepo I) a.
      Proof.
        intros I' I a H; apply Pl.C.versions_ext; intro o.
        rewrite !mem_placeRepo; split; intros [m [v [-> Hk]]];
          exists m, v; split; try reflexivity; apply H; exact Hk.
      Qed.

      Definition SubAtKey (I' I : Inst) (a : N.t) : Prop :=
        forall m v,
          KeySet.In (a, m) (keysOf I') /\ RepoSet.In (m, v) (inst_repo I') ->
          KeySet.In (a, m) (keysOf I) /\ RepoSet.In (m, v) (inst_repo I).

      Definition nameInst (I : Inst) : Pl.Inst :=
        {| Pl.inst_repo := placeRepo I
         ; Pl.inst_deps := Pl.C.DepRel.empty
         ; Pl.inst_peers := Pl.C.DepRel.empty
         ; Pl.inst_optDeps := Pl.C.DepRel.empty
         ; Pl.inst_optPeers := Pl.C.DepRel.empty
         ; Pl.inst_root := rootOcc I |}.

      Theorem versions_lookupLoc : forall I I' depth l a,
          Pl.Reduction.Lookup.Reached (tr I) depth
            (Pl.Reduction.Name.Loc l a) ->
          AgreesAtKey I' I a ->
          Pl.Reduction.T.versions (reduceReal I depth)
            (Pl.Reduction.Name.Loc l a) =
          Pl.Reduction.versions (nameInst I') depth (Pl.Reduction.Name.Loc l a).
      Proof.
        intros I I' depth l a H Ha; unfold reduceReal.
        rewrite (Pl.Reduction.Lookup.versions_lookupLoc _ _ _ _ H).
        unfold Pl.Reduction.versions, Pl.Reduction.Lookup.nameSubInst, nameInst,
          tr, rootOcc; cbn [Pl.inst_repo].
        rewrite Pl.Reduction.Lookup.versions_fibre,
          (keyVersions_agree _ _ _ Ha).
        reflexivity.
      Qed.

      Theorem versions_lookupWalk : forall I I' depth l a,
          Pl.Reduction.Lookup.Reached (tr I) depth
            (Pl.Reduction.Name.Walk l a) ->
          AgreesAtKey I' I a ->
          Pl.Reduction.T.versions (reduceReal I depth)
            (Pl.Reduction.Name.Walk l a) =
          Pl.Reduction.versions (nameInst I') depth
            (Pl.Reduction.Name.Walk l a).
      Proof.
        intros I I' depth l a H Ha; unfold reduceReal.
        rewrite (Pl.Reduction.Lookup.versions_lookupWalk _ _ _ _ H).
        unfold Pl.Reduction.versions, Pl.Reduction.Lookup.nameSubInst, nameInst,
          tr, rootOcc; cbn [Pl.inst_repo].
        rewrite Pl.Reduction.Lookup.versions_fibre,
          (keyVersions_agree _ _ _ Ha).
        reflexivity.
      Qed.

      Lemma keyRepo_sub : forall I' I a o, SubAtKey I' I a ->
          Pl.PkgSet.In (a, o) (placeRepo I') ->
            Pl.PkgSet.In (a, o) (placeRepo I).
      Proof.
        intros I' I a o H Hx; apply mem_placeRepo in Hx.
        destruct Hx as [m [v [-> Hk]]]; apply mem_placeRepo.
        exists m, v; split; [reflexivity | exact (H m v Hk)].
      Qed.

      Theorem versions_lookupLoc_sub : forall I I' depth l a,
          Pl.Reduction.Lookup.Reached (tr I) depth
            (Pl.Reduction.Name.Loc l a) ->
          SubAtKey I' I a ->
          Pl.Reduction.T.VSet.Subset
            (Pl.Reduction.versions (nameInst I') depth
               (Pl.Reduction.Name.Loc l a))
            (Pl.Reduction.T.versions (reduceReal I depth)
               (Pl.Reduction.Name.Loc l a)).
      Proof.
        intros I I' depth l a H Ha w.
        rewrite (versions_lookupLoc I I depth l a H (fun m v => iff_refl _)).
        rewrite !Pl.Reduction.mem_versions_loc.
        intros [-> | [o [Hl [Hx ->]]]]; [left; reflexivity |].
        right; exists o; split; [exact Hl |].
        split; [exact (keyRepo_sub I' I a o Ha Hx) | reflexivity].
      Qed.

      Theorem versions_lookupWalk_sub : forall I I' depth l a,
          Pl.Reduction.Lookup.Reached (tr I) depth
            (Pl.Reduction.Name.Walk l a) ->
          SubAtKey I' I a ->
          Pl.Reduction.T.VSet.Subset
            (Pl.Reduction.versions (nameInst I') depth
               (Pl.Reduction.Name.Walk l a))
            (Pl.Reduction.T.versions (reduceReal I depth)
               (Pl.Reduction.Name.Walk l a)).
      Proof.
        intros I I' depth l a H Ha w.
        rewrite (versions_lookupWalk I I depth l a H (fun m v => iff_refl _)).
        rewrite !Pl.Reduction.mem_versions_walk.
        intros [-> | [l' [o [Hs [Hl [Hx ->]]]]]]; [left; reflexivity |].
        right; exists l', o; split; [exact Hs |]; split; [exact Hl |].
        split; [exact (keyRepo_sub I' I a o Ha Hx) | reflexivity].
      Qed.

      Definition atomOf (l : Pl.Path.t) (e : Edge) (vs : Pl.VSet.t)
          : Pl.Reduction.T.Dependees.t :=
        (Pl.Reduction.Name.Walk l (e_dir e),
         Pl.Reduction.optAccept (e_opt e) (Pl.land (e_peer e) l) vs).

      Definition edgeAtom (I : Inst) (l : Pl.Path.t) (e : Edge)
          : Pl.Reduction.T.Dependees.t :=
        atomOf l e (accepts I e).

      Module SOhh := SetOps Pl.Reduction.T.Dependees Pl.Reduction.T.Dependees
        Pl.Reduction.T.DependeesSet Pl.Reduction.T.DependeesSet.
      Definition occAtoms (I : Inst) (l : Pl.Path.t) (o : Occ.t)
          : Pl.Reduction.T.DependeesSet.t :=
        SOhh.ofList (List.map (edgeAtom I l) (edgesOf I o)).

      Lemma edgeAtoms_tr : forall I a' o l, Pl.PkgSet.In (a', o) (occs I) ->
          Pl.Reduction.edgeAtoms (tr I) (a', o) l = occAtoms I l o.
      Proof.
        intros I a' o l Hp; apply Pl.Reduction.T.DependeesSet.ext; intro h.
        rewrite Pl.Reduction.mem_edgeAtoms; unfold occAtoms.
        rewrite SOhh.mem_ofList, in_map_iff; split.
        - intros [peer [optional [n [vs [HE ->]]]]];
            rewrite rel_tr, mem_edgeRel in HE.
          destruct HE as [_ [e [He [<- [<- [-> ->]]]]]].
          exists e; split; [reflexivity | exact He].
        - intros [e [<- He]].
          exists (e_peer e), (e_opt e), (e_dir e), (accepts I e).
          split; [| reflexivity].
          rewrite rel_tr, mem_edgeRel; split; [exact Hp |].
          exists e; auto.
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

      Definition AgreesAtOcc (Vq : N.t -> VS.t) (I' I : Inst) (o : Occ.t)
          : Prop :=
        inst_ovr I' = inst_ovr I /\
        activeDeps I' o = activeDeps I o /\ declPeers I' o = declPeers I o /\
        forall d m, In d (activeDeps I o) -> d_optional d = true ->
          m = ovrName I (d_dir d) (d_name d) ->
          Vq m = realVersions (inst_repo I) m.

      Lemma edgesOfBy_agree : forall Vq I' I o, AgreesAtOcc Vq I' I o ->
          edgesOfBy Vq I' o = edgesOf I o.
      Proof.
        intros Vq I' I o [Ho [Hd [Hp Hr]]].
        assert (Hn : forall a m, ovrName I' a m = ovrName I a m)
          by (intros a m; unfold ovrName; rewrite Ho; reflexivity).
        assert (Hg : forall a rg, ovrRange I' a rg = ovrRange I a rg)
          by (intros a rg; unfold ovrRange; rewrite Ho; reflexivity).
        unfold edgesOf, edgesOfBy; rewrite Hd, Hp; f_equal.
        - apply map_ext_in; intros d Hin; unfold depEdge; cbv zeta.
          rewrite Hn, Hg.
          destruct (d_optional d) eqn:Hopt; [| reflexivity]; cbn [andb].
          rewrite (Hr d _ Hin Hopt eq_refl); reflexivity.
        - apply map_ext; intro theta; unfold peerEdge; rewrite Hn, Hg;
            reflexivity.
      Qed.

      Lemma edgeAtom_agree : forall I' I l e, AgreesAtName I' I (e_name e) ->
          edgeAtom I' l e = edgeAtom I l e.
      Proof.
        intros I' I l e Hr; unfold edgeAtom, accepts.
        replace (realVersions (inst_repo I') (e_name e))
          with (realVersions (inst_repo I) (e_name e)); [reflexivity |].
        apply VS.ext; intro u; rewrite !mem_realVersions; symmetry;
          exact (Hr u).
      Qed.

      Theorem occAtoms_parts : forall I Ix Vq (at_ : Edge -> Inst) l o,
          AgreesAtOcc Vq Ix I o ->
          (forall e, In e (edgesOf I o) -> AgreesAtName (at_ e) I (e_name e)) ->
          occAtoms I l o =
          SOhh.ofList
            (List.map (fun e => edgeAtom (at_ e) l e) (edgesOfBy Vq Ix o)).
      Proof.
        intros I Ix Vq at_ l o Hx He; unfold occAtoms.
        rewrite (edgesOfBy_agree _ _ _ _ Hx); f_equal.
        apply map_ext_in; intros e Hin.
        exact (eq_sym (edgeAtom_agree _ _ _ _ (He e Hin))).
      Qed.

      Lemma dependees_occAtomsRoot : forall I depth,
          Pl.Reduction.T.dependees (reduceDeps I depth) (rootPkg I) =
          occAtoms I nil Occ.Top.
      Proof.
        intros I depth; unfold reduceDeps, rootPkg.
        rewrite Pl.Reduction.dependees_reduceDeps.
        - cbn [Pl.Reduction.rootPkg Pl.Reduction.dependees tr Pl.inst_root
                 rootOcc snd].
          exact (edgeAtoms_tr I (inst_root I) Occ.Top nil
                   (proj2 (Pl.PkgSet.add_spec _ _ _) (or_introl eq_refl))).
        - apply Pl.Reduction.mem_reduceReal; split; [exact Logic.I |].
          apply Pl.Reduction.T.VSet.singleton_spec; reflexivity.
      Qed.

      Lemma dependees_occAtomsOcc : forall I depth l a o,
          Pl.Reduction.T.PkgSet.In
            (Pl.Reduction.Name.Loc l a, Pl.Reduction.Version.Occ o)
            (reduceReal I depth) ->
          Pl.Reduction.T.dependees (reduceDeps I depth)
            (Pl.Reduction.Name.Loc l a, Pl.Reduction.Version.Occ o) =
          occAtoms I (a :: l) o.
      Proof.
        intros I depth l a o H; unfold reduceDeps.
        rewrite (Pl.Reduction.dependees_reduceDeps _ _ _ H).
        apply Pl.Reduction.mem_reduceReal in H; destruct H as [_ H].
        apply Pl.Reduction.mem_versions_loc in H.
        destruct H as [E | [v [_ [Hv E]]]]; [discriminate E |].
        injection E as ->; cbn [Pl.Reduction.dependees].
        exact (edgeAtoms_tr I a v (a :: l)
                 (proj2 (Pl.PkgSet.add_spec _ _ _) (or_intror Hv))).
      Qed.

      Lemma mem_repoPreimage : forall I ns n u,
          RepoSet.In (n, u)
            (RepoSet.filter (fun '(n', _) => List.existsb (NEqb.eqb n') ns)
               (inst_repo I)) <->
          RepoSet.In (n, u) (inst_repo I) /\ In n ns.
      Proof.
        intros I ns n u.
        rewrite RepoSet.filter_spec
          by (intros x y Heq; rewrite Heq; reflexivity).
        cbn beta iota; rewrite List.existsb_exists; split.
        - intros [H [n' [Hn E]]]; apply NEqb.eqb_true_iff in E; subst n'.
          split; [exact H | exact Hn].
        - intros [H Hn]; split; [exact H |].
          exists n; split; [exact Hn | apply NEqb.eqb_refl].
      Qed.

      Lemma occAtoms_sub : forall I' I ns l o,
          inst_repo I' =
            RepoSet.filter
              (fun '(n, _) => List.existsb (NEqb.eqb n) ns) (inst_repo I) ->
          inst_ovr I' = inst_ovr I ->
          activeDeps I' o = activeDeps I o -> declPeers I' o = declPeers I o ->
          incl (List.map e_name (edgesOf I o)) ns ->
          occAtoms I' l o = occAtoms I l o.
      Proof.
        intros I' I ns l o HR Ho Hd Hp Hns.
        assert (Ha : forall n, In n (List.map e_name (edgesOf I o)) ->
                   AgreesAtName I' I n)
          by (intros n Hn u; rewrite HR, mem_repoPreimage;
              pose proof (Hns n Hn); tauto).
        assert (Hx : AgreesAtOcc (realVersions (inst_repo I')) I' I o).
        { split; [exact Ho |]; split; [exact Hd |]; split; [exact Hp |].
          intros d m Hin _ ->.
          assert (Hm : In (ovrName I (d_dir d) (d_name d))
                         (List.map e_name (edgesOf I o))).
          { apply in_map_iff.
            exists (depEdge (realVersions (inst_repo I)) I d);
              split; [reflexivity |].
            unfold edgesOf, edgesOfBy; apply in_or_app; left.
            apply in_map; exact Hin. }
          apply VS.ext; intro u; rewrite !mem_realVersions; exact (Ha _ Hm u). }
        symmetry; exact (occAtoms_parts I I' (realVersions (inst_repo I'))
                           (fun _ => I') l o Hx
                           (fun e He => Ha _ (in_map e_name _ e He))).
      Qed.

      Lemma keysOf_sub : forall I' I k,
          inst_ovr I' = inst_ovr I ->
          (forall d, In d (inst_rootDeps I ++ List.map snd (inst_deps I)) ->
             (d_dir d, ovrName I (d_dir d) (d_name d)) = k ->
             In d (inst_rootDeps I' ++ List.map snd (inst_deps I'))) ->
          (forall theta,
             In theta (inst_rootPeers I ++ List.map snd (inst_peers I)) ->
             (p_dir theta, ovrName I (p_dir theta) (p_name theta)) = k ->
             In theta (inst_rootPeers I' ++ List.map snd (inst_peers I'))) ->
          KeySet.In k (keysOf I) -> KeySet.In k (keysOf I').
      Proof.
        intros I' I k Ho Hd Hp Hk.
        assert (Hn : forall a n, ovrName I' a n = ovrName I a n)
          by (intros a n; unfold ovrName; rewrite Ho; reflexivity).
        unfold keysOf in Hk |- *; rewrite SOkk.mem_ofList in Hk |- *.
        apply in_app_or in Hk; apply in_or_app.
        destruct Hk as [Hk | Hk]; apply in_map_iff in Hk;
          destruct Hk as [x [E Hx]].
        - left; apply in_map_iff; exists x.
          cbn [e_name depEdge] in E |- *; rewrite Hn.
          split; [exact E | exact (Hd x Hx E)].
        - right; apply in_map_iff; exists x.
          cbn [e_name peerEdge] in E |- *; rewrite Hn.
          split; [exact E | exact (Hp x Hx E)].
      Qed.

      Theorem dependees_lookupRoot : forall I depth,
          Pl.Reduction.T.dependees (reduceDeps I depth) (rootPkg I) =
          Pl.Reduction.dependees
            (tr (MkInst
                   (RepoSet.filter
                      (fun '(n, _) =>
                         List.existsb (NEqb.eqb n)
                           (List.map e_name (edgesOf I Occ.Top)))
                      (inst_repo I))
                   nil nil (inst_ovr I) (inst_root I) (inst_rootDeps I)
                   (inst_rootPeers I)))
            (rootPkg I).
      Proof.
        intros I depth; rewrite dependees_occAtomsRoot.
        match goal with
        | |- _ = Pl.Reduction.dependees (tr ?J) _ => set (I' := J)
        end.
        transitivity (occAtoms I' nil Occ.Top).
        - symmetry;
            apply (occAtoms_sub I' I (List.map e_name (edgesOf I Occ.Top)));
            [reflexivity | reflexivity | reflexivity | reflexivity
            | intros n Hn; exact Hn].
        - symmetry; exact (edgeAtoms_tr I' (inst_root I') Occ.Top nil
                             (proj2 (Pl.PkgSet.add_spec _ _ _)
                                (or_introl eq_refl))).
      Qed.

      (* An occupant's edges are in the translation only while it is in R_P,
         so its sub-instance keeps the entries putting (a, m) into keysOf. *)
      Theorem dependees_lookupOcc : forall I depth l a m v,
          Pl.Reduction.T.PkgSet.In
            (Pl.Reduction.Name.Loc l a,
             Pl.Reduction.Version.Occ (Occ.Reg m v))
            (reduceReal I depth) ->
          Pl.Reduction.T.dependees (reduceDeps I depth)
            (Pl.Reduction.Name.Loc l a,
             Pl.Reduction.Version.Occ (Occ.Reg m v)) =
          Pl.Reduction.dependees
            (tr (MkInst
                   (RepoSet.filter
                      (fun '(n, _) =>
                         List.existsb (NEqb.eqb n)
                           (m :: List.map e_name (edgesOf I (Occ.Reg m v))))
                      (inst_repo I))
                   (List.filter
                      (fun '(p, d) =>
                         orb (RPkgEqb.eqb p (m, v))
                           (andb (NEqb.eqb (d_dir d) a)
                              (NEqb.eqb (ovrName I (d_dir d) (d_name d)) m)))
                      (inst_deps I))
                   (List.filter
                      (fun '(p, theta) =>
                         orb (RPkgEqb.eqb p (m, v))
                           (andb (NEqb.eqb (p_dir theta) a)
                              (NEqb.eqb
                                 (ovrName I (p_dir theta) (p_name theta)) m)))
                      (inst_peers I))
                   (inst_ovr I) (inst_root I)
                   (List.filter
                      (fun d =>
                         andb (NEqb.eqb (d_dir d) a)
                           (NEqb.eqb (ovrName I (d_dir d) (d_name d)) m))
                      (inst_rootDeps I))
                   (List.filter
                      (fun theta =>
                         andb (NEqb.eqb (p_dir theta) a)
                           (NEqb.eqb
                              (ovrName I (p_dir theta) (p_name theta)) m))
                      (inst_rootPeers I))))
            (Pl.Reduction.Name.Loc l a,
             Pl.Reduction.Version.Occ (Occ.Reg m v)).
      Proof.
        intros I depth l a m v H.
        rewrite (dependees_occAtomsOcc I depth l a _ H).
        assert (Hk : KeySet.In (a, m) (keysOf I) /\
                     RepoSet.In (m, v) (inst_repo I)).
        { apply Pl.Reduction.mem_reduceReal in H; destruct H as [_ H].
          apply Pl.Reduction.mem_versions_loc in H.
          destruct H as [E | [o [_ [Ho E]]]]; [discriminate E |].
          injection E as <-; cbn [tr Pl.inst_repo] in Ho.
          apply mem_placeRepo in Ho; destruct Ho as [m' [v' [E Hk]]].
          injection E as <- <-; exact Hk. }
        destruct Hk as [Hk Hr].
        match goal with
        | |- _ = Pl.Reduction.dependees (tr ?J) _ => set (I' := J)
        end.
        assert (Hocc : Pl.PkgSet.In (a, Occ.Reg m v) (occs I')).
        { unfold occs; apply Pl.PkgSet.add_spec; right; apply mem_placeRepo.
          exists m, v; split; [reflexivity |]; split.
          - apply (keysOf_sub I' I); [reflexivity | | | exact Hk].
            + intros d Hd E; injection E as Ea Em.
              unfold I'; cbn [inst_rootDeps inst_deps].
              apply in_app_or in Hd; apply in_or_app; destruct Hd as [Hd | Hd].
              * left; apply filter_In; split; [exact Hd |].
                cbn beta iota; rewrite Em, Ea, !NEqb.eqb_refl; reflexivity.
              * right; apply in_map_iff in Hd; apply in_map_iff.
                destruct Hd as [[p d'] [E Hd]]; cbn [snd] in E; subst d'.
                exists (p, d); split; [reflexivity |].
                apply filter_In; split; [exact Hd |]; cbn beta iota.
                rewrite Em, Ea, !NEqb.eqb_refl; apply Bool.orb_true_r.
            + intros theta Hp E; injection E as Ea Em.
              unfold I'; cbn [inst_rootPeers inst_peers].
              apply in_app_or in Hp; apply in_or_app; destruct Hp as [Hp | Hp].
              * left; apply filter_In; split; [exact Hp |].
                cbn beta iota; rewrite Em, Ea, !NEqb.eqb_refl; reflexivity.
              * right; apply in_map_iff in Hp; apply in_map_iff.
                destruct Hp as [[p theta'] [E Hp]]; cbn [snd] in E;
                  subst theta'.
                exists (p, theta); split; [reflexivity |].
                apply filter_In; split; [exact Hp |]; cbn beta iota.
                rewrite Em, Ea, !NEqb.eqb_refl; apply Bool.orb_true_r.
          - unfold I'; cbn [inst_repo]; apply mem_repoPreimage.
            split; [exact Hr | left; reflexivity]. }
        transitivity (occAtoms I' (a :: l) (Occ.Reg m v));
          [| symmetry; exact (edgeAtoms_tr I' a (Occ.Reg m v) (a :: l) Hocc)].
        symmetry;
          apply (occAtoms_sub I' I
                   (m :: List.map e_name (edgesOf I (Occ.Reg m v))));
          [reflexivity | reflexivity | | | intros n Hn; right; exact Hn].
        - unfold I'; cbn [activeDeps inst_deps].
          rewrite ownedBy_filter; [reflexivity |].
          intros d _; cbn beta iota; rewrite RPkgEqb.eqb_refl; reflexivity.
        - unfold I'; cbn [declPeers inst_peers].
          rewrite ownedBy_filter; [reflexivity |].
          intros theta _; cbn beta iota; rewrite RPkgEqb.eqb_refl;
            reflexivity.
      Qed.
    End Lookup.
  End Reduction.
End NpmPlacement.
