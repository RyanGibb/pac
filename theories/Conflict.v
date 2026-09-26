From Stdlib Require Import Orders.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_conf.
Create Rewrite HintDb cmp_conf.

Module Conflict (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Module ConfElt := PairUOT Pkg C.Dependees.
  Module ConflictRel := FSetUOT ConfElt.

  Record IsResolution
      (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
      (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_core : C.IsResolution R D r S
    ; res_conflict_avoidance :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          ConflictRel.In (p, (n, vs)) G ->
          ~ (exists v, VSet.In v vs /\ PkgSet.In (n, v) S) }.

  Module Reduction.
    Module VF := UOTCompareFacts V.
    #[local] Hint Rewrite VF.compare_eq_iff : cmp_conf.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_conf.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_conf.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Bot.
      Definition t := version.

      Definition rank (x : t) : nat :=
        match x with Orig _ => 0 | Bot => 1 end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq => match x, y with
                | Orig v1, Orig v2 => V.compare v1 v2
                | _, _ => Eq
                end
        | c => c
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_conf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_conf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_conf. Qed.
    End Version.

    Module VersionOT := UOTFromCompare Version.
    Module T := Core N VersionOT.
    Module NSet := FSetUOT N.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t := (fst p, Version.Orig (snd p)).

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition embedSet (S : PkgSet.t) : T.PkgSet.t := SOpt.map embedPkg S.

    Module SOvt := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t := SOvt.map Version.Orig vs.

    Module SOpn := SetOps Pkg N PkgSet NSet.
    Module SOdn := SetOps C.DepElt N C.DepRel NSet.
    Module SOcn := SetOps ConfElt N ConflictRel NSet.
    Definition instNames (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
      : NSet.t :=
      NSet.union (SOpn.map fst R)
        (NSet.union (SOdn.map (fun '(_, (n, _)) => n) D)
           (SOcn.map (fun '(_, (n, _)) => n) G)).

    Module SOnt := SetOps N T.Pkg NSet T.PkgSet.
    Definition absentPkgs (ns : NSet.t) : T.PkgSet.t :=
      SOnt.map (fun n => (n, Version.Bot)) ns.

    Definition reduceReal (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
      : T.PkgSet.t :=
      T.PkgSet.union (embedSet R) (absentPkgs (instNames R D G)).

    Lemma mem_instNames : forall R D G (n : N.t),
        NSet.In n (instNames R D G) <->
        (exists v, PkgSet.In (n, v) R) \/
        (exists p vs, C.DepRel.In (p, (n, vs)) D) \/
        (exists p vs, ConflictRel.In (p, (n, vs)) G).
    Proof.
      intros R D G n; unfold instNames.
      rewrite !NSet.union_spec, SOpn.mem_map, SOdn.mem_map, SOcn.mem_map.
      split.
      - intros [[[m v] [HR Hm]] | [[[p [m vs]] [HD Hm]] | [[p [m vs]] [HG Hm]]]];
          simpl in Hm; subst.
        + left; exists v; exact HR.
        + right; left; exists p, vs; exact HD.
        + right; right; exists p, vs; exact HG.
      - intros [[v HR] | [[p [vs HD]] | [p [vs HG]]]].
        + left; exists (n, v); split; [exact HR | reflexivity].
        + right; left; exists (p, (n, vs)); split; [exact HD | reflexivity].
        + right; right; exists (p, (n, vs)); split; [exact HG | reflexivity].
    Qed.

    Lemma mem_absentPkgs : forall ns (y : T.Pkg.t),
        T.PkgSet.In y (absentPkgs ns) <->
        exists n, NSet.In n ns /\ y = (n, Version.Bot).
    Proof. intros ns y; unfold absentPkgs; apply SOnt.mem_map. Qed.

    Lemma mem_reduceReal :
      forall R D G (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal R D G) <->
        (exists p, PkgSet.In p R /\ y = embedPkg p) \/
        (exists n, NSet.In n (instNames R D G) /\ y = (n, Version.Bot)).
    Proof.
      intros; unfold reduceReal, embedSet.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, mem_absentPkgs; reflexivity.
    Qed.

    Module SOdtd := SetOps C.DepElt T.DepElt C.DepRel T.DepRel.
    Definition origEdges (D : C.DepRel.t) : T.DepRel.t :=
      SOdtd.map (fun '(p, (n, vs)) => (embedPkg p, (n, embedVS vs))) D.

    Definition complementVS (R : PkgSet.t) (n : N.t) (vs : VSet.t) : T.VSet.t :=
      T.VSet.add Version.Bot (embedVS (VSet.diff (C.versions R n) vs)).

    Module SOctd := SetOps ConfElt T.DepElt ConflictRel T.DepRel.
    Definition conflictEdges (R : PkgSet.t) (G : ConflictRel.t) : T.DepRel.t :=
      SOctd.map (fun '(p, (n, vs)) => (embedPkg p, (n, complementVS R n vs))) G.

    Definition reduceDeps (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
      : T.DepRel.t :=
      T.DepRel.union (origEdges D) (conflictEdges R G).

    Lemma mem_complementVS : forall R n vs (w : Version.t),
        T.VSet.In w (complementVS R n vs) <->
        w = Version.Bot \/
        exists u, PkgSet.In (n, u) R /\ ~ VSet.In u vs /\ w = Version.Orig u.
    Proof.
      intros R n vs w; unfold complementVS.
      rewrite SOvt.add_in; unfold embedVS; rewrite SOvt.mem_map.
      split.
      - intros [-> | [u [Hu ->]]]; [left; reflexivity | right].
        apply VSet.diff_spec in Hu; destruct Hu as [Hu Hnv].
        apply C.mem_versions in Hu.
        exists u; auto.
      - intros [-> | [u [HR [Hnv ->]]]]; [left; reflexivity | right].
        exists u; split; [| reflexivity].
        apply VSet.diff_spec; split; [apply C.mem_versions; exact HR | exact Hnv].
    Qed.

    Lemma mem_origEdges : forall (D : C.DepRel.t) (y : T.DepElt.t),
        T.DepRel.In y (origEdges D) <->
        exists p n vs, C.DepRel.In (p, (n, vs)) D /\
          y = (embedPkg p, (n, embedVS vs)).
    Proof.
      intros D y; unfold origEdges; rewrite SOdtd.mem_map.
      split.
      - intros [[q [n vs]] [HD Hy]]; cbn beta iota in Hy.
        exists q, n, vs; split; [exact HD | exact Hy].
      - intros [p [n [vs [HD ->]]]].
        exists (p, (n, vs)); split; [exact HD | reflexivity].
    Qed.

    Lemma mem_conflictEdges : forall R (G : ConflictRel.t) (y : T.DepElt.t),
        T.DepRel.In y (conflictEdges R G) <->
        exists p n vs, ConflictRel.In (p, (n, vs)) G /\
          y = (embedPkg p, (n, complementVS R n vs)).
    Proof.
      intros R G y; unfold conflictEdges; rewrite SOctd.mem_map.
      split.
      - intros [[q [n vs]] [HG Hy]]; cbn beta iota in Hy.
        exists q, n, vs; split; [exact HG | exact Hy].
      - intros [p [n [vs [HG ->]]]].
        exists (p, (n, vs)); split; [exact HG | reflexivity].
    Qed.

    Lemma mem_reduceDeps :
      forall R (D : C.DepRel.t) (G : ConflictRel.t) (y : T.DepElt.t),
        T.DepRel.In y (reduceDeps R D G) <->
        (exists p n vs, C.DepRel.In (p, (n, vs)) D /\
           y = (embedPkg p, (n, embedVS vs))) \/
        (exists p n vs, ConflictRel.In (p, (n, vs)) G /\
           y = (embedPkg p, (n, complementVS R n vs))).
    Proof.
      intros R D G y; unfold reduceDeps.
      rewrite T.DepRel.union_spec, mem_origEdges, mem_conflictEdges.
      tauto.
    Qed.

    Definition tryInvPkg (p : T.Pkg.t) : option Pkg.t :=
      match p with
      | (n, Version.Orig v) => Some (n, v)
      | (_, Version.Bot) => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : T.Pkg.t) (p : Pkg.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [n [v | ]] p H; simpl in H; try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
    Lemma embedPkg_injective :
      forall p q : Pkg.t, embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOtp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

    Definition conflictResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_conflictResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (conflictResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold conflictResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma embedPkg_mem_real :
      forall (p : Pkg.t) R D (G : ConflictRel.t),
        T.PkgSet.In (embedPkg p) (reduceReal R D G) -> PkgSet.In p R.
    Proof.
      intros p R D G H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [n [_ Hy]]].
      - apply embedPkg_injective in Hq; subst q; exact HqR.
      - destruct p; unfold embedPkg in Hy; simpl in Hy; congruence.
    Qed.

    Theorem conflict_soundness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
             (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D G) (reduceDeps R D G) (embedPkg r) S ->
        IsResolution R D G r (conflictResolution S).
    Proof.
      intros R D G r S [Hsub Hroot Hdep Huniq].
      constructor.
      - constructor.
        + intros p Hp; apply mem_conflictResolution in Hp.
          exact (embedPkg_mem_real p R D G (Hsub _ Hp)).
        + apply mem_conflictResolution; exact Hroot.
        + intros p Hp m vs HD; apply mem_conflictResolution in Hp.
          assert (Hd : T.DepRel.In (embedPkg p, (m, embedVS vs))
                         (reduceDeps R D G))
            by (apply mem_reduceDeps; left; exists p, m, vs;
                split; [exact HD | reflexivity]).
          destruct (Hdep _ Hp _ _ Hd) as [v' [Hv' Hv'S]].
          unfold embedVS in Hv'; apply SOvt.mem_map in Hv';
            destruct Hv' as [v [Hv ->]].
          exists v; split;
            [exact Hv | apply mem_conflictResolution; exact Hv'S].
        + intros n v v' Hv Hv'; apply mem_conflictResolution in Hv, Hv'.
          assert (E : Version.Orig v = Version.Orig v')
            by (apply (Huniq n); assumption).
          injection E as E; exact E.
      - intros p Hp n vs Hg [u [Hu HuS]].
        apply mem_conflictResolution in Hp, HuS.
        assert (Hd : T.DepRel.In (embedPkg p, (n, complementVS R n vs))
                       (reduceDeps R D G))
          by (apply mem_reduceDeps; right; exists p, n, vs;
              split; [exact Hg | reflexivity]).
        destruct (Hdep _ Hp _ _ Hd) as [w [Hw HwS]].
        assert (E : w = Version.Orig u) by (apply (Huniq n); assumption).
        subst w; apply mem_complementVS in Hw.
        destruct Hw as [Hw | [u' [_ [Hnv E]]]]; [discriminate Hw |].
        injection E as <-; exact (Hnv Hu).
    Qed.

    Definition absentIn (S : PkgSet.t) (ns : NSet.t) : NSet.t :=
      NSet.filter
        (fun n => negb (PkgSet.exists_
                          (fun p => if N.eq_dec (fst p) n then true else false)
                          S))
        ns.

    Lemma exists_name_iff : forall S n,
        PkgSet.exists_ (fun p => if N.eq_dec (fst p) n then true else false) S
          = true <-> exists v, PkgSet.In (n, v) S.
    Proof.
      intros S n; rewrite PkgSet.exists_spec'; split.
      - intros [[m v] [Hm Ht]]; cbn [fst] in Ht.
        destruct (N.eq_dec m n) as [-> | ]; [eauto | discriminate].
      - intros [v Hv]; exists (n, v); cbn [fst]; rewrite dec_refl; auto.
    Qed.

    Lemma mem_absentIn : forall S ns n,
        NSet.In n (absentIn S ns) <->
        NSet.In n ns /\ forall v, ~ PkgSet.In (n, v) S.
    Proof.
      intros S ns n; unfold absentIn.
      rewrite NSet.filter_spec', Bool.negb_true_iff,
        <- Bool.not_true_iff_false, exists_name_iff.
      firstorder.
    Qed.

    Definition coreResolution (S : PkgSet.t) R D (G : ConflictRel.t) :
        T.PkgSet.t :=
      T.PkgSet.union (embedSet S) (absentPkgs (absentIn S (instNames R D G))).

    Lemma mem_coreResolution :
      forall S R D G (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution S R D G) <->
        (exists p, PkgSet.In p S /\ y = embedPkg p) \/
        (exists n, NSet.In n (instNames R D G) /\
           (forall v, ~ PkgSet.In (n, v) S) /\ y = (n, Version.Bot)).
    Proof.
      intros S R D G y; unfold coreResolution, embedSet.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, mem_absentPkgs.
      split.
      - intros [H | [n [Hn ->]]]; [left; exact H | right].
        apply mem_absentIn in Hn; destruct Hn as [Hn Hnone].
        exists n; auto.
      - intros [H | [n [Hn [Hnone ->]]]]; [left; exact H | right].
        exists n; split; [| reflexivity].
        apply mem_absentIn; auto.
    Qed.

    Lemma embed_mem_coreResolution_inv :
      forall S R D G (p : Pkg.t),
        T.PkgSet.In (embedPkg p) (coreResolution S R D G) -> PkgSet.In p S.
    Proof.
      intros S R D G p H; apply mem_coreResolution in H.
      destruct H as [[q [HqS Hq]] | [n [_ [_ Hq]]]].
      - apply embedPkg_injective in Hq; subst q; exact HqS.
      - destruct p; unfold embedPkg in Hq; simpl in Hq; congruence.
    Qed.

    Theorem conflict_completeness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (G : ConflictRel.t)
             (r : Pkg.t) (S : PkgSet.t),
        IsResolution R D G r S ->
        T.IsResolution (reduceReal R D G) (reduceDeps R D G) (embedPkg r)
          (coreResolution S R D G).
    Proof.
      intros R D G r S [[Hsub Hroot Hdep Huniq] Havoid].
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy; apply mem_reduceReal.
        destruct Hy as [[p [HpS ->]] | [n [Hn [_ ->]]]].
        + left; exists p; split; [apply Hsub; exact HpS | reflexivity].
        + right; exists n; auto.
      - apply mem_coreResolution; left; exists r; auto.
      - intros q Hq m ws Hd; apply mem_reduceDeps in Hd.
        destruct Hd as [[p [m0 [vs [HD Hy]]]] | [p [n [vs [HG Hy]]]]];
          injection Hy as -> -> ->.
        + assert (HpS : PkgSet.In p S)
            by (apply (embed_mem_coreResolution_inv S R D G p); exact Hq).
          destruct (Hdep p HpS m0 vs HD) as [v [Hv HvS]].
          exists (Version.Orig v); split.
          * unfold embedVS; apply SOvt.mem_map; exists v; auto.
          * apply mem_coreResolution; left; exists (m0, v); auto.
        + assert (HpS : PkgSet.In p S)
            by (apply (embed_mem_coreResolution_inv S R D G p); exact Hq).
          destruct (PkgSet.exists_
                      (fun q => if N.eq_dec (fst q) n then true else false) S)
            eqn:E.
          * apply exists_name_iff in E; destruct E as [u Hu].
            exists (Version.Orig u); split.
            -- apply mem_complementVS; right; exists u.
               split; [apply Hsub; exact Hu | split; [| reflexivity]].
               intro Huv; apply (Havoid p HpS n vs HG); exists u; auto.
            -- apply mem_coreResolution; left; exists (n, u); auto.
          * rewrite <- Bool.not_true_iff_false, exists_name_iff in E.
            exists Version.Bot;
              split; [apply mem_complementVS; left; reflexivity |].
            apply mem_coreResolution; right; exists n.
            split; [| split; [| reflexivity]].
            -- apply mem_instNames; right; right; exists p, vs; exact HG.
            -- intros v Hv; apply E; exists v; exact Hv.
      - intros n w w' Hw Hw'.
        apply mem_coreResolution in Hw, Hw'.
        destruct Hw as [[[pn pv] [HpS Hp]] | [m [_ [Hnone Hp]]]];
          destruct Hw' as [[[pn' pv'] [Hp'S Hp']] | [m' [_ [Hnone' Hp']]]];
          unfold embedPkg in *; cbn [fst snd] in *.
        + injection Hp as -> ->; injection Hp' as -> ->.
          f_equal; exact (Huniq _ _ _ HpS Hp'S).
        + injection Hp as -> ->; injection Hp' as -> ->.
          exfalso; exact (Hnone' _ HpS).
        + injection Hp as -> ->; injection Hp' as -> ->.
          exfalso; exact (Hnone _ Hp'S).
        + congruence.
    Qed.

    Module Lookup.
      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Module DepRelFibred := FibredRel Pkg C.Dependees C.DepElt C.DepRel.
      Module ConflictRelFibred :=
        FibredLabelledRel Pkg N VSet.AsUOT ConfElt ConflictRel.
      Module RKeys := PreimageOfKeys N Pkg NSet PkgSet.

      Definition realPreimage (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
        RKeys.ofKeys fst ns R.

      Definition conflictNames (G : ConflictRel.t) : NSet.t :=
        SOcn.map (fun '(_, (n, _)) => n) G.

      Lemma mem_conflictNames : forall G n,
          NSet.In n (conflictNames G) <->
          exists p vs, ConflictRel.In (p, (n, vs)) G.
      Proof.
        intros G n; unfold conflictNames; rewrite SOcn.mem_map; split.
        - intros [[p [m vs]] [HG Hm]]; cbn beta iota in Hm; subst m.
          exists p, vs; exact HG.
        - intros [p [vs HG]]; exists (p, (n, vs)); split;
            [exact HG | reflexivity].
      Qed.

      Lemma versions_realPreimage : forall R ns n,
          NSet.In n ns -> C.versions (realPreimage R ns) n = C.versions R n.
      Proof.
        intros R ns n Hn; apply C.versions_ext; intro v.
        unfold realPreimage; rewrite RKeys.mem_ofKeys; cbn [fst]; tauto.
      Qed.

      Lemma reachable_instNames : forall R D G (n : N.t),
          (exists p h, T.DepRel.In (p, (n, h)) (reduceDeps R D G)) ->
          NSet.In n (instNames R D G).
      Proof.
        intros R D G n [p [h Hd]]; apply mem_reduceDeps in Hd.
        apply mem_instNames.
        destruct Hd as [[q [m [vs [HD Hy]]]] | [q [m [vs [HG Hy]]]]];
          injection Hy as _ <- _.
        - right; left; exists q, vs; exact HD.
        - right; right; exists q, vs; exact HG.
      Qed.

      Theorem versions_lookupOrig : forall R D G (r : Pkg.t) (n : N.t),
          PkgSet.In r R ->
          (exists p h, T.DepRel.In (p, (n, h)) (reduceDeps R D G)) \/
          n = fst r ->
          T.versions (reduceReal R D G) n =
          T.VSet.add Version.Bot
            (embedVS (C.versions (PkgFibred.tailFibre R n) n)).
      Proof.
        intros R D G r n Hr Hreach.
        assert (Hn : NSet.In n (instNames R D G)).
        { destruct Hreach as [Hreach | ->];
            [exact (reachable_instNames R D G n Hreach) |].
          apply mem_instNames; left; destruct r as [rn rv]; exists rv;
            exact Hr. }
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal, SOvt.add_in.
        unfold embedVS; rewrite SOvt.mem_map.
        split.
        - intros [[[qn qv] [HR Hq]] | [m [_ Hy]]].
          + unfold embedPkg in Hq; cbn [fst snd] in Hq.
            injection Hq as -> ->.
            right; exists qv; split; [| reflexivity].
            apply C.mem_versions, PkgFibred.mem_tailFibre; auto.
          + injection Hy as -> ->; left; reflexivity.
        - intros [-> | [v [Hv ->]]].
          + right; exists n; auto.
          + apply C.mem_versions, PkgFibred.mem_tailFibre in Hv.
            destruct Hv as [Hv _].
            left; exists (n, v); split; [exact Hv | reflexivity].
      Qed.

      Theorem dependees_lookupOrig : forall R D G (n : N.t) (v : V.t),
          T.dependees (reduceDeps R D G) (embedPkg (n, v)) =
          T.dependees
            (reduceDeps
               (realPreimage R
                  (conflictNames (ConflictRelFibred.tailFibre G (n, v))))
               (DepRelFibred.tailFibre D (n, v))
               (ConflictRelFibred.tailFibre G (n, v)))
            (embedPkg (n, v)).
      Proof.
        intros R D G n v; apply T.dependees_ext; intros [m ws].
        assert (Hc : forall n' vs, ConflictRel.In ((n, v), (n', vs)) G ->
                  complementVS (realPreimage R (conflictNames
                    (ConflictRelFibred.tailFibre G (n, v)))) n' vs =
                  complementVS R n' vs).
        { intros n' vs HG; unfold complementVS.
          rewrite versions_realPreimage; [reflexivity |].
          apply mem_conflictNames; exists (n, v), vs.
          apply ConflictRelFibred.mem_tailFibre; auto. }
        rewrite !mem_reduceDeps.
        split; intros [[q [n' [vs [HD Hy]]]] | [q [n' [vs [HG Hy]]]]];
          destruct q as [qn qv]; unfold embedPkg in Hy; simpl in Hy;
          injection Hy as <- <- -> ->; [left | right | left | right];
          exists (n, v), n', vs.
        - split; [apply DepRelFibred.mem_tailFibre; auto | reflexivity].
        - split; [apply ConflictRelFibred.mem_tailFibre; auto |].
          rewrite Hc; [reflexivity | exact HG].
        - apply DepRelFibred.mem_tailFibre in HD; destruct HD as [HD _]; auto.
        - apply ConflictRelFibred.mem_tailFibre in HG; destruct HG as [HG _].
          rewrite Hc by exact HG; auto.
      Qed.

      Theorem dependees_lookupAbsent : forall R D G (n : N.t),
          T.dependees (reduceDeps R D G) (n, Version.Bot) =
          T.DependeesSet.empty.
      Proof.
        intros R D G n; apply T.dependees_empty_iff; intros [m ws] H.
        apply mem_reduceDeps in H.
        destruct H as [[q [n' [vs [_ Hy]]]] | [q [n' [vs [_ Hy]]]]];
          destruct q; unfold embedPkg in Hy; simpl in Hy; congruence.
      Qed.
    End Lookup.
  End Reduction.
End Conflict.
