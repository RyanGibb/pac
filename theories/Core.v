From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude.

(* Module application is generative: two instantiations of Core at equal
   parameters have incompatible types. Instantiate once and share. *)
Module Core (N V : UsualOrderedType).
  Module Pkg := PairUOT N V.
  Module PkgSet := FSetUOT Pkg.
  Module VSet := FSetUOT V.
  Module Dependees := PairUOT N VSet.AsUOT.
  Module DependeesSet := FSetUOT Dependees.
  Module DepElt := PairUOT Pkg Dependees.
  Module DepRel := FSetUOT DepElt.

  Definition dependees (D : DepRel.t) (p : Pkg.t) : DependeesSet.t :=
    DepRel.fold (fun '(q, h) acc =>
        if Pkg.eq_dec q p then DependeesSet.add h acc else acc)
      D DependeesSet.empty.

  Module SOdh := SetOps DepElt Dependees DepRel DependeesSet.
  Lemma mem_dependees : forall D (p : Pkg.t) (h : Dependees.t),
      DependeesSet.In h (dependees D p) <-> DepRel.In (p, h) D.
  Proof.
    intros D p h; unfold dependees.
    rewrite (SOdh.in_fold _
      (fun e => if Pkg.eq_dec (fst e) p
                then DependeesSet.singleton (snd e) else DependeesSet.empty)).
    2:{ intros [q d] a y; simpl; pose proof (SOdh.empty_in y).
        destruct (Pkg.eq_dec q p); rewrite ?SOdh.add_in, ?SOdh.singleton_in;
          tauto. }
    pose proof (SOdh.empty_in h) as E0; split.
    - intros [H | [[q d] [HeD He]]]; [tauto | simpl in He].
      destruct (Pkg.eq_dec q p) as [-> | _]; [| tauto].
      apply SOdh.singleton_in in He; subst d; exact HeD.
    - intro H; right; exists (p, h); simpl.
      rewrite dec_refl, SOdh.singleton_in; auto.
  Qed.

  Lemma dependees_ext : forall D D' (p : Pkg.t),
      (forall h, DepRel.In (p, h) D <-> DepRel.In (p, h) D') ->
      dependees D p = dependees D' p.
  Proof.
    intros D D' p H; apply DependeesSet.ext; intro h.
    rewrite !mem_dependees; exact (H h).
  Qed.

  Lemma dependees_empty_iff : forall D (p : Pkg.t),
      dependees D p = DependeesSet.empty <->
      forall h, ~ DepRel.In (p, h) D.
  Proof.
    intros D p; split.
    - intros He h Hin; rewrite <- mem_dependees, He in Hin.
      exact (DependeesSet.empty_spec Hin).
    - intro H; apply DependeesSet.ext; intro h.
      rewrite mem_dependees; split;
        [intro Hin; destruct (H h Hin) | intro Hin;
         destruct (DependeesSet.empty_spec Hin)].
  Qed.

  Module SOpv := SetOps Pkg V PkgSet VSet.
  Definition versions (R : PkgSet.t) (n : N.t) : VSet.t :=
    SOpv.filterMap (fun '(m, v) => if N.eq_dec m n then Some v else None) R.

  Lemma mem_versions : forall R (n : N.t) (v : V.t),
      VSet.In v (versions R n) <-> PkgSet.In (n, v) R.
  Proof.
    intros R n v; unfold versions; rewrite SOpv.mem_filterMap.
    split.
    - intros [[m u] [HR Hm]]; cbn beta iota in Hm.
      destruct (N.eq_dec m n) as [-> | NE]; [| discriminate].
      injection Hm as <-; exact HR.
    - intro H; exists (n, v); split; [exact H | cbn beta iota].
      rewrite dec_refl; reflexivity.
  Qed.

  Lemma versions_ext : forall R R' (n : N.t),
      (forall v, PkgSet.In (n, v) R <-> PkgSet.In (n, v) R') ->
      versions R n = versions R' n.
  Proof.
    intros R R' n H; apply VSet.ext; intro v.
    rewrite !mem_versions; exact (H v).
  Qed.

  Module NSet := FSetUOT N.

  Definition hasNameb (S : PkgSet.t) (n : N.t) : bool :=
    PkgSet.exists_ (fun p => if N.eq_dec (fst p) n then true else false) S.

  Lemma hasNameb_true : forall S n,
      hasNameb S n = true <-> exists v, PkgSet.In (n, v) S.
  Proof.
    intros S n; unfold hasNameb; rewrite PkgSet.exists_spec'.
    split.
    - intros [[m v] [Hm Ht]]; cbn [fst] in Ht.
      destruct (N.eq_dec m n) as [-> | ]; [| discriminate].
      exists v; exact Hm.
    - intros [v Hv]; exists (n, v); split; [exact Hv |].
      cbn [fst]; apply dec_refl.
  Qed.

  Lemma hasNameb_false : forall S n,
      hasNameb S n = false <-> forall v, ~ PkgSet.In (n, v) S.
  Proof.
    intros S n; split.
    - intros E v Hv.
      assert (Ht : hasNameb S n = true)
        by (apply hasNameb_true; exists v; exact Hv).
      congruence.
    - intro Hnone; destruct (hasNameb S n) eqn:E; [| reflexivity].
      apply hasNameb_true in E; destruct E as [v Hv]; destruct (Hnone v Hv).
  Qed.

  Definition absentIn (S : PkgSet.t) (ns : NSet.t) : NSet.t :=
    NSet.filter (fun n => negb (hasNameb S n)) ns.

  Lemma mem_absentIn : forall S ns n,
      NSet.In n (absentIn S ns) <->
      NSet.In n ns /\ forall v, ~ PkgSet.In (n, v) S.
  Proof.
    intros S ns n; unfold absentIn; rewrite NSet.filter_spec'.
    rewrite Bool.negb_true_iff, hasNameb_false; reflexivity.
  Qed.

  Module PkgPreimage := PreimageOfKeys N Pkg NSet PkgSet.
  Definition namePreimage (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
    PkgPreimage.ofKeys fst ns R.

  Lemma mem_namePreimage : forall R ns q,
      PkgSet.In q (namePreimage R ns) <-> PkgSet.In q R /\ NSet.In (fst q) ns.
  Proof. intros R ns q; apply PkgPreimage.mem_ofKeys. Qed.

  Lemma versions_namePreimage : forall R ns n,
      NSet.In n ns -> versions (namePreimage R ns) n = versions R n.
  Proof.
    intros R ns n Hn; apply versions_ext; intro v.
    rewrite mem_namePreimage; cbn [fst]; tauto.
  Qed.

  Definition VersionUnique (S : PkgSet.t) : Prop :=
    forall (n : N.t) (v v' : V.t),
      PkgSet.In (n, v) S -> PkgSet.In (n, v') S -> v = v'.

  Definition FunctionalInName (D : DepRel.t) : Prop :=
    forall (p : Pkg.t) (n : N.t) (vs1 vs2 : VSet.t),
      DepRel.In (p, (n, vs1)) D -> DepRel.In (p, (n, vs2)) D -> vs1 = vs2.

  Record IsResolution
      (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_dep_closure :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          DepRel.In (p, (n, vs)) D ->
          exists v, VSet.In v vs /\ PkgSet.In (n, v) S
    ; res_version_unique : VersionUnique S }.

  Module Merge.
    Definition mergedVS (D : DepRel.t) (p : Pkg.t) (n : N.t) : VSet.t :=
      VSet.filter
        (fun v => DepRel.for_all
            (fun '(q, (m, vs)) =>
                      if Pkg.eq_dec q p
                      then if N.eq_dec m n then VSet.mem v vs else true
                      else true)
            D)
        (DepRel.fold (fun '(q, (m, vs)) acc =>
             if Pkg.eq_dec q p
             then if N.eq_dec m n then VSet.union vs acc else acc
             else acc)
           D VSet.empty).

    Module SOdv := SetOps DepElt V DepRel VSet.
    Lemma mergedVS_union_spec : forall D p n v,
        VSet.In v
          (DepRel.fold (fun '(q, (m, vs)) acc =>
               if Pkg.eq_dec q p
               then if N.eq_dec m n then VSet.union vs acc else acc
               else acc)
             D VSet.empty) <->
        exists vs, DepRel.In (p, (n, vs)) D /\ VSet.In v vs.
    Proof.
      intros D p n v.
      rewrite (SOdv.in_fold _
        (fun e => if Pkg.eq_dec (fst e) p
                  then if N.eq_dec (fst (snd e)) n
                       then snd (snd e) else VSet.empty
                  else VSet.empty)).
      2:{ intros [q [m vs]] a y; simpl; pose proof (SOdv.empty_in y).
          destruct (Pkg.eq_dec q p); [destruct (N.eq_dec m n) |];
            rewrite ?VSet.union_spec; tauto. }
      pose proof (SOdv.empty_in v) as E0; split.
      - intros [H | [[q [m vs]] [HeD He]]]; [tauto | simpl in He].
        destruct (Pkg.eq_dec q p) as [-> | _];
          [destruct (N.eq_dec m n) as [-> | _] |]; [| tauto | tauto].
        exists vs; split; assumption.
      - intros [vs [HD Hv]].
        right; exists (p, (n, vs)); simpl; rewrite !dec_refl; auto.
    Qed.

    Lemma mem_mergedVS : forall D p n v,
        VSet.In v (mergedVS D p n) <->
        (exists vs, DepRel.In (p, (n, vs)) D) /\
        (forall vs, DepRel.In (p, (n, vs)) D -> VSet.In v vs).
    Proof.
      intros D p n v; unfold mergedVS.
      rewrite VSet.filter_spec'.
      rewrite mergedVS_union_spec.
      rewrite DepRel.for_all_spec'.
      split.
      - intros [[vs [HD Hv]] Hall].
        split; [exists vs; exact HD |].
        intros vs' HD'.
        specialize (Hall _ HD'); simpl in Hall; rewrite !dec_refl in Hall.
        apply VSet.mem_spec; exact Hall.
      - intros [[vs0 H0] Hall].
        split.
        + exists vs0; split; [exact H0 | apply Hall; exact H0].
        + intros [q [m vs]] He; simpl.
          destruct (Pkg.eq_dec q p) as [-> | NE]; [| reflexivity].
          destruct (N.eq_dec m n) as [-> | NE]; [| reflexivity].
          apply VSet.mem_spec; apply Hall; exact He.
    Qed.

    Definition merge (D : DepRel.t) : DepRel.t :=
      DepRel.fold (fun '(q, (n, _)) acc =>
          DepRel.add (q, (n, mergedVS D q n)) acc)
        D DepRel.empty.

    Module SOdd := SetOps DepElt DepElt DepRel DepRel.
    Lemma mem_merge : forall D p n vs,
        DepRel.In (p, (n, vs)) (merge D) <->
        (exists vs0, DepRel.In (p, (n, vs0)) D) /\ vs = mergedVS D p n.
    Proof.
      intros D p n vs; unfold merge.
      rewrite (SOdd.in_fold _
        (fun e => DepRel.singleton
                    (fst e, (fst (snd e), mergedVS D (fst e) (fst (snd e)))))).
      2:{ intros [q [m ws]] a y; simpl.
          rewrite SOdd.add_in, SOdd.singleton_in; tauto. }
      split.
      - intros [H | [e [HeD He]]].
        + exfalso; exact (SOdd.empty_in _ H).
        + destruct e as [q [m ws]]; rewrite SOdd.singleton_in in He;
            simpl in He.
          injection He as -> -> ->.
          split; [exists ws; exact HeD | reflexivity].
      - intros [[vs0 H0] ->].
        right; exists (p, (n, vs0)); split; [exact H0 | simpl].
        rewrite SOdd.singleton_in; reflexivity.
    Qed.

    Theorem merge_functionalInName : forall D, FunctionalInName (merge D).
    Proof.
      intros D p n vs1 vs2 H1 H2.
      apply mem_merge in H1; apply mem_merge in H2.
      destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity.
    Qed.

    Theorem merge_resolution_iff : forall R D r S,
        IsResolution R (merge D) r S <-> IsResolution R D r S.
    Proof.
      intros R D r S; split; intros [Hsub Hroot Hdep Huniq]; constructor;
        try assumption.
      - intros p Hp m vs HD.
        destruct (Hdep p Hp m (mergedVS D p m)) as [v [Hv HvS]].
        + apply mem_merge; split; [exists vs; exact HD | reflexivity].
        + apply mem_mergedVS in Hv; destruct Hv as [_ Hall].
          exists v; split; [apply Hall; exact HD | exact HvS].
      - intros p Hp m ws Hmem.
        apply mem_merge in Hmem; destruct Hmem as [[vs0 H0] ->].
        destruct (Hdep p Hp m vs0 H0) as [v [Hv HvS]].
        exists v; split; [| exact HvS].
        apply mem_mergedVS; split; [exists vs0; exact H0 |].
        intros vs' HD'.
        destruct (Hdep p Hp m vs' HD') as [v' [Hv' Hv'S]].
        assert (v = v') as -> by (apply (Huniq m); assumption).
        exact Hv'.
    Qed.
  End Merge.
End Core.
