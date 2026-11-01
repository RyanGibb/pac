From Stdlib Require Import Orders.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_conf.
Create Rewrite HintDb cmp_conf.

Module Conflict (N V : UsualOrderedType).
  Module Source := Core N V.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.

  Module ConflictElt := PairUOT Package Source.Dependee.
  Module ConflictRel := FSetUOT ConflictElt.

  Record IsResolution
      (R : PackageSet.t) (D : Source.DependencyRel.t) (G : ConflictRel.t)
      (r : Package.t) (S : PackageSet.t) : Prop :=
    { res_core : Source.IsResolution R D r S
    ; res_conflict_avoidance :
        forall p, PackageSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          ConflictRel.In (p, (n, vs)) G ->
          ~ (exists v, VSet.In v vs /\ PackageSet.In (n, v) S) }.

  Module Reduction.
    Module VFacts := UOTCompareFacts V.
    #[local] Hint Rewrite VFacts.compare_eq_iff : cmp_conf.
    #[local] Hint Extern 1 => cmp_by VFacts.compare_antisym : cmp_conf.
    #[local] Hint Extern 1 => cmp_by VFacts.compare_lt_trans : cmp_conf.

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
    Module Reduced := Core N VersionOT.
    Module NSet := Source.NSet.

    Definition embedPkg (p : Package.t) : Reduced.Package.t := (fst p, Version.Orig (snd p)).

    Module SOpt := SetOps Package Reduced.Package PackageSet Reduced.PackageSet.
    Definition embedSet (S : PackageSet.t) : Reduced.PackageSet.t := SOpt.map embedPkg S.

    Module SOvt := SetOps V VersionOT VSet Reduced.VSet.
    Definition embedVS (vs : VSet.t) : Reduced.VSet.t := SOvt.map Version.Orig vs.

    Module SOpn := SetOps Package N PackageSet NSet.
    Module SOdn := SetOps Source.DependencyElt N Source.DependencyRel NSet.
    Module SOcn := SetOps ConflictElt N ConflictRel NSet.
    Definition instNames (R : PackageSet.t) (D : Source.DependencyRel.t) (G : ConflictRel.t)
      : NSet.t :=
      NSet.union (SOpn.map fst R)
        (NSet.union (SOdn.map (fun '(_, (n, _)) => n) D)
           (SOcn.map (fun '(_, (n, _)) => n) G)).

    Module SOnt := SetOps N Reduced.Package NSet Reduced.PackageSet.
    Definition absentPkgs (ns : NSet.t) : Reduced.PackageSet.t :=
      SOnt.map (fun n => (n, Version.Bot)) ns.

    Definition reduceReal (R : PackageSet.t) (D : Source.DependencyRel.t) (G : ConflictRel.t)
      : Reduced.PackageSet.t :=
      Reduced.PackageSet.union (embedSet R) (absentPkgs (instNames R D G)).

    Lemma mem_instNames : forall R D G (n : N.t),
        NSet.In n (instNames R D G) <->
        (exists u, PackageSet.In (n, u) R) \/
        (exists p vs, Source.DependencyRel.In (p, (n, vs)) D) \/
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

    Lemma mem_absentPkgs : forall ns (p : Reduced.Package.t),
        Reduced.PackageSet.In p (absentPkgs ns) <->
        exists n, NSet.In n ns /\ p = (n, Version.Bot).
    Proof. intros ns p; unfold absentPkgs; apply SOnt.mem_map. Qed.

    Lemma mem_reduceReal :
      forall R D G (q : Reduced.Package.t),
        Reduced.PackageSet.In q (reduceReal R D G) <->
        (exists p, PackageSet.In p R /\ q = embedPkg p) \/
        (exists n, NSet.In n (instNames R D G) /\ q = (n, Version.Bot)).
    Proof.
      intros; unfold reduceReal, embedSet.
      rewrite Reduced.PackageSet.union_spec, SOpt.mem_map, mem_absentPkgs; reflexivity.
    Qed.

    Module SOdtd := SetOps Source.DependencyElt Reduced.DependencyElt Source.DependencyRel Reduced.DependencyRel.
    Definition origEdges (D : Source.DependencyRel.t) : Reduced.DependencyRel.t :=
      SOdtd.map (fun '(p, (n, vs)) => (embedPkg p, (n, embedVS vs))) D.

    Definition complementVS (R : PackageSet.t) (n : N.t) (vs : VSet.t) : Reduced.VSet.t :=
      Reduced.VSet.add Version.Bot (embedVS (VSet.diff (Source.versions R n) vs)).

    Module SOctd := SetOps ConflictElt Reduced.DependencyElt ConflictRel Reduced.DependencyRel.
    Definition conflictEdges (R : PackageSet.t) (G : ConflictRel.t) : Reduced.DependencyRel.t :=
      SOctd.map (fun '(p, (n, vs)) => (embedPkg p, (n, complementVS R n vs))) G.

    Definition reduceDeps (R : PackageSet.t) (D : Source.DependencyRel.t) (G : ConflictRel.t)
      : Reduced.DependencyRel.t :=
      Reduced.DependencyRel.union (origEdges D) (conflictEdges R G).

    Lemma mem_complementVS : forall R n vs (v : Version.t),
        Reduced.VSet.In v (complementVS R n vs) <->
        v = Version.Bot \/
        exists u, PackageSet.In (n, u) R /\ ~ VSet.In u vs /\ v = Version.Orig u.
    Proof.
      intros R n vs v; unfold complementVS.
      rewrite SOvt.add_in; unfold embedVS; rewrite SOvt.mem_map.
      split.
      - intros [-> | [u [Hu ->]]]; [left; reflexivity | right].
        apply VSet.diff_spec in Hu; destruct Hu as [Hu Hnv].
        apply Source.mem_versions in Hu.
        exists u; auto.
      - intros [-> | [u [HR [Hnv ->]]]]; [left; reflexivity | right].
        exists u; split; [| reflexivity].
        apply VSet.diff_spec; split; [apply Source.mem_versions; exact HR | exact Hnv].
    Qed.

    Lemma mem_origEdges : forall (D : Source.DependencyRel.t) (y : Reduced.DependencyElt.t),
        Reduced.DependencyRel.In y (origEdges D) <->
        exists p n vs, Source.DependencyRel.In (p, (n, vs)) D /\
          y = (embedPkg p, (n, embedVS vs)).
    Proof.
      intros D y; unfold origEdges; rewrite SOdtd.mem_map.
      split.
      - intros [[q [n vs]] [HD Hy]]; cbn beta iota in Hy.
        exists q, n, vs; split; [exact HD | exact Hy].
      - intros [p [n [vs [HD ->]]]].
        exists (p, (n, vs)); split; [exact HD | reflexivity].
    Qed.

    Lemma mem_conflictEdges : forall R (G : ConflictRel.t) (y : Reduced.DependencyElt.t),
        Reduced.DependencyRel.In y (conflictEdges R G) <->
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
      forall R (D : Source.DependencyRel.t) (G : ConflictRel.t) (y : Reduced.DependencyElt.t),
        Reduced.DependencyRel.In y (reduceDeps R D G) <->
        (exists p n vs, Source.DependencyRel.In (p, (n, vs)) D /\
           y = (embedPkg p, (n, embedVS vs))) \/
        (exists p n vs, ConflictRel.In (p, (n, vs)) G /\
           y = (embedPkg p, (n, complementVS R n vs))).
    Proof.
      intros R D G y; unfold reduceDeps.
      rewrite Reduced.DependencyRel.union_spec, mem_origEdges, mem_conflictEdges.
      tauto.
    Qed.

    Definition tryInvPkg (p : Reduced.Package.t) : option Package.t :=
      match p with
      | (n, Version.Orig v) => Some (n, v)
      | (_, Version.Bot) => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : Reduced.Package.t) (p : Package.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [n [v | ]] p H; simpl in H; try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps Reduced.Package Package Reduced.PackageSet PackageSet.
    Lemma embedPkg_injective :
      forall p q : Package.t, embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOtp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

    Definition conflictResolution (S : Reduced.PackageSet.t) : PackageSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_conflictResolution : forall (S : Reduced.PackageSet.t) (p : Package.t),
        PackageSet.In p (conflictResolution S) <-> Reduced.PackageSet.In (embedPkg p) S.
    Proof.
      unfold conflictResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma embedPkg_mem_real :
      forall (p : Package.t) R D (G : ConflictRel.t),
        Reduced.PackageSet.In (embedPkg p) (reduceReal R D G) -> PackageSet.In p R.
    Proof.
      intros p R D G H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [n [_ Hy]]].
      - apply embedPkg_injective in Hq; subst q; exact HqR.
      - destruct p; unfold embedPkg in Hy; simpl in Hy; congruence.
    Qed.

    Theorem conflict_soundness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (G : ConflictRel.t)
             (r : Package.t) (S : Reduced.PackageSet.t),
        Reduced.IsResolution (reduceReal R D G) (reduceDeps R D G) (embedPkg r) S ->
        IsResolution R D G r (conflictResolution S).
    Proof.
      intros R D G r S [Hsub Hroot Hdep Huniq].
      constructor.
      - constructor.
        + intros p Hp; apply mem_conflictResolution in Hp.
          exact (embedPkg_mem_real p R D G (Hsub _ Hp)).
        + apply mem_conflictResolution; exact Hroot.
        + intros p Hp m vs HD; apply mem_conflictResolution in Hp.
          assert (Hd : Reduced.DependencyRel.In (embedPkg p, (m, embedVS vs))
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
        assert (Hd : Reduced.DependencyRel.In (embedPkg p, (n, complementVS R n vs))
                       (reduceDeps R D G))
          by (apply mem_reduceDeps; right; exists p, n, vs;
              split; [exact Hg | reflexivity]).
        destruct (Hdep _ Hp _ _ Hd) as [w [Hw HwS]].
        assert (E : w = Version.Orig u) by (apply (Huniq n); assumption).
        subst w; apply mem_complementVS in Hw.
        destruct Hw as [Hw | [u' [_ [Hnv E]]]]; [discriminate Hw |].
        injection E as <-; exact (Hnv Hu).
    Qed.

    Definition coreResolution R D (G : ConflictRel.t) (S : PackageSet.t) :
        Reduced.PackageSet.t :=
      Reduced.PackageSet.union (embedSet S)
        (absentPkgs (Source.absentIn S (instNames R D G))).

    Lemma mem_coreResolution :
      forall S R D G (q : Reduced.Package.t),
        Reduced.PackageSet.In q (coreResolution R D G S) <->
        (exists p, PackageSet.In p S /\ q = embedPkg p) \/
        (exists n, NSet.In n (instNames R D G) /\
           (forall u, ~ PackageSet.In (n, u) S) /\ q = (n, Version.Bot)).
    Proof.
      intros S R D G q; unfold coreResolution, embedSet.
      rewrite Reduced.PackageSet.union_spec, SOpt.mem_map, mem_absentPkgs.
      split.
      - intros [H | [n [Hn ->]]]; [left; exact H | right].
        apply Source.mem_absentIn in Hn; destruct Hn as [Hn Hnone].
        exists n; auto.
      - intros [H | [n [Hn [Hnone ->]]]]; [left; exact H | right].
        exists n; split; [| reflexivity].
        apply Source.mem_absentIn; auto.
    Qed.

    Lemma embed_mem_coreResolution_inv :
      forall S R D G (p : Package.t),
        Reduced.PackageSet.In (embedPkg p) (coreResolution R D G S) -> PackageSet.In p S.
    Proof.
      intros S R D G p H; apply mem_coreResolution in H.
      destruct H as [[q [HqS Hq]] | [n [_ [_ Hq]]]].
      - apply embedPkg_injective in Hq; subst q; exact HqS.
      - destruct p; unfold embedPkg in Hq; simpl in Hq; congruence.
    Qed.

    Theorem conflict_completeness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (G : ConflictRel.t)
             (r : Package.t) (S : PackageSet.t),
        IsResolution R D G r S ->
        Reduced.IsResolution (reduceReal R D G) (reduceDeps R D G) (embedPkg r)
          (coreResolution R D G S).
    Proof.
      intros R D G r S [[Hsub Hroot Hdep Huniq] Havoid].
      constructor.
      - intros p' Hy; apply mem_coreResolution in Hy; apply mem_reduceReal.
        destruct Hy as [[p [HpS ->]] | [n [Hn [_ ->]]]].
        + left; exists p; split; [apply Hsub; exact HpS | reflexivity].
        + right; exists n; auto.
      - apply mem_coreResolution; left; exists r; auto.
      - intros q Hq m ws Hd; apply mem_reduceDeps in Hd.
        destruct Hd as [[p [m0 [vs [HD Hy]]]] | [p [n [vs [HG Hy]]]]];
          injection Hy as -> -> ->.
        + assert (HpS : PackageSet.In p S)
            by (apply (embed_mem_coreResolution_inv S R D G p); exact Hq).
          destruct (Hdep p HpS m0 vs HD) as [v [Hv HvS]].
          exists (Version.Orig v); split.
          * unfold embedVS; apply SOvt.mem_map; exists v; auto.
          * apply mem_coreResolution; left; exists (m0, v); auto.
        + assert (HpS : PackageSet.In p S)
            by (apply (embed_mem_coreResolution_inv S R D G p); exact Hq).
          destruct (Source.hasNameb S n) eqn:E.
          * apply Source.hasNameb_true in E; destruct E as [u Hu].
            exists (Version.Orig u); split.
            -- apply mem_complementVS; right; exists u.
               split; [apply Hsub; exact Hu | split; [| reflexivity]].
               intro Huv; apply (Havoid p HpS n vs HG); exists u; auto.
            -- apply mem_coreResolution; left; exists (n, u); auto.
          * rewrite <- Bool.not_true_iff_false, Source.hasNameb_true in E.
            exists Version.Bot;
              split; [apply mem_complementVS; left; reflexivity |].
            apply mem_coreResolution; right; exists n.
            split; [| split; [| reflexivity]].
            -- apply mem_instNames; right; right; exists p, vs; exact HG.
            -- intros v Hv; apply E; exists v; exact Hv.
      - intros n v v' Hv Hv'.
        apply mem_coreResolution in Hv, Hv'.
        destruct Hv as [[[pn pv] [HpS Hp]] | [m [_ [Hnone Hp]]]];
          destruct Hv' as [[[pn' pv'] [Hp'S Hp']] | [m' [_ [Hnone' Hp']]]];
          unfold embedPkg in *; cbn [fst snd] in *.
        + injection Hp as -> ->; injection Hp' as -> ->.
          f_equal; exact (Huniq _ _ _ HpS Hp'S).
        + injection Hp as -> ->; injection Hp' as -> ->.
          exfalso; exact (Hnone' _ HpS).
        + injection Hp as -> ->; injection Hp' as -> ->.
          exfalso; exact (Hnone _ Hp'S).
        + congruence.
    Qed.

    Theorem conflict_retraction : forall S R D G,
        conflictResolution (coreResolution R D G S) = S.
    Proof.
      intros S R D G; apply PackageSet.ext; intro p.
      rewrite mem_conflictResolution.
      split; [exact (embed_mem_coreResolution_inv S R D G p) |].
      intro H; apply mem_coreResolution; left; exists p; split;
        [exact H | reflexivity].
    Qed.

    Module Lookup.
      Module PackageSetFibred := FibredRel N V Package PackageSet.
      Module DependencyRelFibred := FibredRel Package Source.Dependee Source.DependencyElt Source.DependencyRel.
      Module ConflictRelFibred :=
        FibredLabelledRel Package N VSet.AsUOT ConflictElt ConflictRel.

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

      Lemma reachable_instNames : forall R D G (n : N.t),
          (exists p h, Reduced.DependencyRel.In (p, (n, h)) (reduceDeps R D G)) ->
          NSet.In n (instNames R D G).
      Proof.
        intros R D G n [p [h Hd]]; apply mem_reduceDeps in Hd.
        apply mem_instNames.
        destruct Hd as [[q [m [vs [HD Hy]]]] | [q [m [vs [HG Hy]]]]];
          injection Hy as _ <- _.
        - right; left; exists q, vs; exact HD.
        - right; right; exists q, vs; exact HG.
      Qed.

      Lemma versions_reduceReal_bot : forall R D G (n : N.t),
          Reduced.VSet.add Version.Bot (Reduced.versions (reduceReal R D G) n) =
          Reduced.VSet.add Version.Bot (embedVS (Source.versions R n)).
      Proof.
        intros R D G n; apply Reduced.VSet.ext; intro w.
        rewrite !SOvt.add_in, Reduced.mem_versions, mem_reduceReal.
        unfold embedVS; rewrite SOvt.mem_map.
        split.
        - intros [-> | [[[qn qv] [HR Hq]] | [m [_ Hy]]]];
            [left; reflexivity | |].
          + unfold embedPkg in Hq; cbn [fst snd] in Hq.
            injection Hq as -> ->.
            right; exists qv; split; [apply Source.mem_versions; exact HR |].
            reflexivity.
          + injection Hy as -> ->; left; reflexivity.
        - intros [-> | [v [Hv ->]]]; [left; reflexivity |].
          right; left; exists (n, v); split; [| reflexivity].
          apply Source.mem_versions; exact Hv.
      Qed.

      Theorem versions_lookupOrig :
        forall R D G (m : N.t) (u : V.t) (n : N.t),
          PackageSet.In (m, u) R ->
          (exists p h, Reduced.DependencyRel.In (p, (n, h)) (reduceDeps R D G)) \/
          n = m ->
          Reduced.versions (reduceReal R D G) n =
          Reduced.VSet.add Version.Bot
            (Reduced.versions
               (reduceReal (PackageSetFibred.tailFibre R n) Source.DependencyRel.empty
                  ConflictRel.empty) n).
      Proof.
        intros R D G m u n Hr Hreach.
        rewrite versions_reduceReal_bot.
        assert (Hn : NSet.In n (instNames R D G)).
        { destruct Hreach as [Hreach | ->];
            [exact (reachable_instNames R D G n Hreach) |].
          apply mem_instNames; left; exists u; exact Hr. }
        apply Reduced.VSet.ext; intro w.
        rewrite Reduced.mem_versions, mem_reduceReal, SOvt.add_in.
        unfold embedVS; rewrite SOvt.mem_map.
        split.
        - intros [[[qn qv] [HR Hq]] | [m' [_ Hy]]].
          + unfold embedPkg in Hq; cbn [fst snd] in Hq.
            injection Hq as -> ->.
            right; exists qv; split; [| reflexivity].
            apply Source.mem_versions, PackageSetFibred.mem_tailFibre; auto.
          + injection Hy as -> ->; left; reflexivity.
        - intros [-> | [v [Hv ->]]].
          + right; exists n; auto.
          + apply Source.mem_versions, PackageSetFibred.mem_tailFibre in Hv.
            destruct Hv as [Hv _].
            left; exists (n, v); split; [exact Hv | reflexivity].
      Qed.

      Theorem dependees_lookupOrig : forall R D G (n : N.t) (v : V.t),
          Reduced.dependees (reduceDeps R D G) (embedPkg (n, v)) =
          Reduced.dependees
            (reduceDeps
               (Source.namePreimage R
                  (conflictNames (ConflictRelFibred.tailFibre G (n, v))))
               (DependencyRelFibred.tailFibre D (n, v))
               (ConflictRelFibred.tailFibre G (n, v)))
            (embedPkg (n, v)).
      Proof.
        intros R D G n v; apply Reduced.dependees_ext; intros [m ws].
        assert (Hc : forall n' vs, ConflictRel.In ((n, v), (n', vs)) G ->
                  complementVS (Source.namePreimage R (conflictNames
                    (ConflictRelFibred.tailFibre G (n, v)))) n' vs =
                  complementVS R n' vs).
        { intros n' vs HG; unfold complementVS.
          rewrite Source.versions_namePreimage; [reflexivity |].
          apply mem_conflictNames; exists (n, v), vs.
          apply ConflictRelFibred.mem_tailFibre; auto. }
        rewrite !mem_reduceDeps.
        split; intros [[q [n' [vs [HD Hy]]]] | [q [n' [vs [HG Hy]]]]];
          destruct q as [qn qv]; unfold embedPkg in Hy; simpl in Hy;
          injection Hy as <- <- -> ->; [left | right | left | right];
          exists (n, v), n', vs.
        - split; [apply DependencyRelFibred.mem_tailFibre; auto | reflexivity].
        - split; [apply ConflictRelFibred.mem_tailFibre; auto |].
          rewrite Hc; [reflexivity | exact HG].
        - apply DependencyRelFibred.mem_tailFibre in HD; destruct HD as [HD _]; auto.
        - apply ConflictRelFibred.mem_tailFibre in HG; destruct HG as [HG _].
          rewrite Hc by exact HG; auto.
      Qed.

      Theorem dependees_lookupAbsent : forall R D G (n : N.t),
          Reduced.dependees (reduceDeps R D G) (n, Version.Bot) =
          Reduced.DependeeSet.empty.
      Proof.
        intros R D G n; apply Reduced.dependees_empty_iff; intros [m ws] H.
        apply mem_reduceDeps in H.
        destruct H as [[q [n' [vs [_ Hy]]]] | [q [n' [vs [_ Hy]]]]];
          destruct q; unfold embedPkg in Hy; simpl in Hy; congruence.
      Qed.
    End Lookup.
  End Reduction.
End Conflict.
