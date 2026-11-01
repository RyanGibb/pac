From Stdlib Require Import Orders.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_cls.
Create Rewrite HintDb cmp_cls.

Module ConflictClass (N V : UsualOrderedType).
  Module Source := Core N V.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.

  Module ConflictClassElt := PairUOT Package N.
  Module ConflictClassRel := FSetUOT ConflictClassElt.

  Definition ClassExclusion (Om : ConflictClassRel.t) (S : PackageSet.t) : Prop :=
    forall (k : N.t) (p q : Package.t), PackageSet.In p S -> PackageSet.In q S ->
      ConflictClassRel.In (p, k) Om -> ConflictClassRel.In (q, k) Om -> p = q.

  Record IsResolution
      (R : PackageSet.t) (D : Source.DependencyRel.t) (Om : ConflictClassRel.t) (r : Package.t)
      (S : PackageSet.t) : Prop :=
    { res_core : Source.IsResolution R D r S
    ; res_class_exclusion : ClassExclusion Om S }.

  Module Reduction.
    Module NF := UOTCompareFacts N.
    Module VF := UOTCompareFacts V.
    #[local] Hint Rewrite NF.compare_eq_iff VF.compare_eq_iff : cmp_cls.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_cls.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_cls.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_cls.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_cls.

    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Cls (k : N.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, Cls _ => Lt
        | Cls _, Orig _ => Gt
        | Cls k1, Cls k2 => N.compare k1 k2
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_cls. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_cls. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_cls. Qed.
    End Name.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Name (n : N.t).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, Name _ => Lt
        | Name _, Orig _ => Gt
        | Name n1, Name n2 => N.compare n1 n2
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_cls. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_cls. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_cls. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module Reduced := Core NameOT VersionOT.

    Definition embedPkg (p : Package.t) : Reduced.Package.t :=
      (Name.Orig (fst p), Version.Orig (snd p)).

    Module SOpt := SetOps Package Reduced.Package PackageSet Reduced.PackageSet.
    Definition embedSet (S : PackageSet.t) : Reduced.PackageSet.t := SOpt.map embedPkg S.

    Module SOvt := SetOps V VersionOT VSet Reduced.VSet.
    Definition embedVS (vs : VSet.t) : Reduced.VSet.t := SOvt.map Version.Orig vs.

    Module SOit := SetOps ConflictClassElt Reduced.Package ConflictClassRel Reduced.PackageSet.
    Definition classPkgs (ps : PackageSet.t) (Om : ConflictClassRel.t) : Reduced.PackageSet.t :=
      SOit.filterMap (fun '(q, k) =>
          if PackageSet.mem q ps
          then Some (Name.Cls k, Version.Name (fst q))
          else None)
        Om.

    Lemma mem_classPkgs : forall ps Om (p : Reduced.Package.t),
        Reduced.PackageSet.In p (classPkgs ps Om) <->
        exists n v k, ConflictClassRel.In ((n, v), k) Om /\ PackageSet.In (n, v) ps /\
          p = (Name.Cls k, Version.Name n).
    Proof.
      intros ps Om p; unfold classPkgs; rewrite SOit.mem_filterMap.
      split.
      - intros [[[n v] k] [Hc Hy]]; cbn beta iota in Hy.
        destruct (PackageSet.mem (n, v) ps) eqn:Hm; [| discriminate].
        injection Hy as <-.
        exists n, v, k; split; [exact Hc |].
        split; [apply PackageSet.mem_spec; exact Hm | reflexivity].
      - intros [n [v [k [Hc [Hq ->]]]]].
        exists ((n, v), k); split; [exact Hc | cbn beta iota].
        rewrite (proj2 (PackageSet.mem_spec _ _) Hq); reflexivity.
    Qed.

    Definition reduceReal (R : PackageSet.t) (Om : ConflictClassRel.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.union (embedSet R) (classPkgs R Om).

    Lemma mem_reduceReal : forall R Om (p' : Reduced.Package.t),
        Reduced.PackageSet.In p' (reduceReal R Om) <->
        (exists p, PackageSet.In p R /\ p' = embedPkg p) \/
        (exists n v k, ConflictClassRel.In ((n, v), k) Om /\ PackageSet.In (n, v) R /\
           p' = (Name.Cls k, Version.Name n)).
    Proof.
      intros; unfold reduceReal, embedSet.
      rewrite Reduced.PackageSet.union_spec, SOpt.mem_map, mem_classPkgs; reflexivity.
    Qed.

    Module SOdtd := SetOps Source.DependencyElt Reduced.DependencyElt Source.DependencyRel Reduced.DependencyRel.
    Definition origEdges (D : Source.DependencyRel.t) : Reduced.DependencyRel.t :=
      SOdtd.map (fun '(p, (n, vs)) => (embedPkg p, (Name.Orig n, embedVS vs)))
        D.

    Module SOitd := SetOps ConflictClassElt Reduced.DependencyElt ConflictClassRel Reduced.DependencyRel.
    Definition classEdges (Om : ConflictClassRel.t) : Reduced.DependencyRel.t :=
      SOitd.map (fun '(q, k) =>
          (embedPkg q,
           (Name.Cls k, Reduced.VSet.singleton (Version.Name (fst q)))))
        Om.

    Definition reduceDeps (D : Source.DependencyRel.t) (Om : ConflictClassRel.t) : Reduced.DependencyRel.t :=
      Reduced.DependencyRel.union (origEdges D) (classEdges Om).

    Lemma mem_origEdges : forall (D : Source.DependencyRel.t) (y : Reduced.DependencyElt.t),
        Reduced.DependencyRel.In y (origEdges D) <->
        exists p n vs, Source.DependencyRel.In (p, (n, vs)) D /\
          y = (embedPkg p, (Name.Orig n, embedVS vs)).
    Proof.
      intros D y; unfold origEdges; rewrite SOdtd.mem_map.
      split.
      - intros [[q [n vs]] [HD Hy]]; cbn beta iota in Hy.
        exists q, n, vs; split; [exact HD | exact Hy].
      - intros [p [n [vs [HD ->]]]].
        exists (p, (n, vs)); split; [exact HD | reflexivity].
    Qed.

    Lemma mem_classEdges : forall Om (y : Reduced.DependencyElt.t),
        Reduced.DependencyRel.In y (classEdges Om) <->
        exists n v k, ConflictClassRel.In ((n, v), k) Om /\
          y = (embedPkg (n, v),
               (Name.Cls k, Reduced.VSet.singleton (Version.Name n))).
    Proof.
      intros Om y; unfold classEdges; rewrite SOitd.mem_map.
      split.
      - intros [[[n v] k] [Hc Hy]]; cbn beta iota in Hy.
        exists n, v, k; split; [exact Hc | exact Hy].
      - intros [n [v [k [Hc ->]]]].
        exists ((n, v), k); split; [exact Hc | reflexivity].
    Qed.

    Lemma mem_reduceDeps : forall D Om (y : Reduced.DependencyElt.t),
        Reduced.DependencyRel.In y (reduceDeps D Om) <->
        (exists p n vs, Source.DependencyRel.In (p, (n, vs)) D /\
           y = (embedPkg p, (Name.Orig n, embedVS vs))) \/
        (exists n v k, ConflictClassRel.In ((n, v), k) Om /\
           y = (embedPkg (n, v),
                (Name.Cls k, Reduced.VSet.singleton (Version.Name n)))).
    Proof.
      intros; unfold reduceDeps.
      rewrite Reduced.DependencyRel.union_spec, mem_origEdges, mem_classEdges;
        reflexivity.
    Qed.

    Definition tryInvPkg (p : Reduced.Package.t) : option Package.t :=
      match p with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : Reduced.Package.t) (p : Package.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [[n | k] [v | q]] p H; simpl in H; try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps Reduced.Package Package Reduced.PackageSet PackageSet.
    Lemma embedPkg_injective :
      forall p q : Package.t, embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOtp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

    Definition conflictClassResolution (S : Reduced.PackageSet.t) : PackageSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_conflictClassResolution : forall (S : Reduced.PackageSet.t) (p : Package.t),
        PackageSet.In p (conflictClassResolution S) <-> Reduced.PackageSet.In (embedPkg p) S.
    Proof.
      unfold conflictClassResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma embedPkg_mem_real : forall (p : Package.t) R Om,
        Reduced.PackageSet.In (embedPkg p) (reduceReal R Om) -> PackageSet.In p R.
    Proof.
      intros p R Om H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [n [v [k [_ [_ Hy]]]]]].
      - apply embedPkg_injective in Hq; subst q; exact HqR.
      - discriminate Hy.
    Qed.

    Theorem conflict_class_soundness :
      forall R D Om (r : Package.t) (S : Reduced.PackageSet.t),
        Reduced.IsResolution (reduceReal R Om) (reduceDeps D Om) (embedPkg r) S ->
        IsResolution R D Om r (conflictClassResolution S).
    Proof.
      intros R D Om r S [Hsub Hroot Hdep Huniq].
      assert (Hcls : forall q k,
                 PackageSet.In q (conflictClassResolution S) ->
                 ConflictClassRel.In (q, k) Om ->
                 Reduced.PackageSet.In (Name.Cls k, Version.Name (fst q)) S).
      { intros [n v] k Hq Hc; apply mem_conflictClassResolution in Hq.
        assert (Hd : Reduced.DependencyRel.In
                       (embedPkg (n, v),
                        (Name.Cls k, Reduced.VSet.singleton (Version.Name n)))
                       (reduceDeps D Om))
          by (apply mem_reduceDeps; right; exists n, v, k;
              split; [exact Hc | reflexivity]).
        destruct (Hdep _ Hq _ _ Hd) as [w [Hw HwS]].
        rewrite SOvt.singleton_in in Hw; subst w; exact HwS. }
      assert (Hvu : Source.VersionUnique (conflictClassResolution S)).
      { intros n v v' Hv Hv'; apply mem_conflictClassResolution in Hv, Hv'.
        assert (E : Version.Orig v = Version.Orig v')
          by (apply (Huniq (Name.Orig n)); assumption).
        injection E as E; exact E. }
      constructor.
      - constructor.
        + intros p Hp; apply mem_conflictClassResolution in Hp.
          exact (embedPkg_mem_real p R Om (Hsub _ Hp)).
        + apply mem_conflictClassResolution; exact Hroot.
        + intros p Hp m vs HD; apply mem_conflictClassResolution in Hp.
          assert (Hd : Reduced.DependencyRel.In (embedPkg p, (Name.Orig m, embedVS vs))
                         (reduceDeps D Om))
            by (apply mem_reduceDeps; left; exists p, m, vs;
                split; [exact HD | reflexivity]).
          destruct (Hdep _ Hp _ _ Hd) as [w [Hw HwS]].
          unfold embedVS in Hw; apply SOvt.mem_map in Hw;
            destruct Hw as [v [Hv ->]].
          exists v; split;
            [exact Hv | apply mem_conflictClassResolution; exact HwS].
        + exact Hvu.
      - intros k [pn pv] [qn qv] Hp Hq Hpk Hqk.
        assert (E : Version.Name pn = Version.Name qn)
          by exact (Huniq (Name.Cls k) _ _ (Hcls _ k Hp Hpk) (Hcls _ k Hq Hqk)).
        injection E as <-.
        rewrite (Hvu pn pv qv Hp Hq); reflexivity.
    Qed.

    Definition coreResolution (Om : ConflictClassRel.t) (S : PackageSet.t) :
        Reduced.PackageSet.t :=
      reduceReal S Om.

    Theorem conflict_class_completeness :
      forall R D Om (r : Package.t) (S : PackageSet.t),
        IsResolution R D Om r S ->
        Reduced.IsResolution (reduceReal R Om) (reduceDeps D Om) (embedPkg r)
          (coreResolution Om S).
    Proof.
      intros R D Om r S [[Hsub Hroot Hdep Huniq] Hexcl].
      unfold coreResolution; constructor.
      - intros p' Hy; apply mem_reduceReal in Hy; apply mem_reduceReal.
        destruct Hy as [[p [Hp ->]] | [n [v [k [Hc [Hq ->]]]]]].
        + left; exists p; split; [exact (Hsub _ Hp) | reflexivity].
        + right; exists n, v, k; split; [exact Hc |].
          split; [exact (Hsub _ Hq) | reflexivity].
      - apply mem_reduceReal; left; exists r; split;
          [exact Hroot | reflexivity].
      - intros p' Hy m ws Hd; apply mem_reduceDeps in Hd.
        destruct Hd as [[p [n [vs [HD Hyd]]]] | [qn [qv [k [Hc Hyd]]]]];
          injection Hyd as -> -> ->.
        + apply embedPkg_mem_real in Hy.
          destruct (Hdep p Hy n vs HD) as [v [Hv HvS]].
          exists (Version.Orig v); split.
          * unfold embedVS; apply SOvt.mem_map; exists v; auto.
          * apply mem_reduceReal; left; exists (n, v);
              split; [exact HvS | reflexivity].
        + apply embedPkg_mem_real in Hy.
          exists (Version.Name qn); split.
          * apply SOvt.singleton_in; reflexivity.
          * apply mem_reduceReal; right; exists qn, qv, k;
              split; [exact Hc | split; [exact Hy | reflexivity]].
      - intros n w w' Hw Hw'; apply mem_reduceReal in Hw, Hw'.
        destruct Hw as [[p [Hp E]] | [qn [qv [k [Hc [Hq E]]]]]];
          destruct Hw' as [[p' [Hp' E']] | [qn' [qv' [k' [Hc' [Hq' E']]]]]];
          unfold embedPkg in *; try congruence.
        + destruct p as [pn pv], p' as [pn' pv']; cbn [fst snd] in E, E'.
          assert (pn' = pn) as -> by congruence.
          rewrite (Huniq pn pv pv' Hp Hp') in E; congruence.
        + assert (k' = k) as -> by congruence.
          injection (Hexcl k _ _ Hq Hq' Hc Hc') as -> _; congruence.
    Qed.

    Theorem conflict_class_retraction : forall (S : PackageSet.t) Om,
        conflictClassResolution (coreResolution Om S) = S.
    Proof.
      intros S Om; apply PackageSet.ext; intro p.
      rewrite mem_conflictClassResolution; unfold coreResolution.
      split; [exact (embedPkg_mem_real p S Om) |].
      intro H; apply mem_reduceReal; left; exists p; split;
        [exact H | reflexivity].
    Qed.

    Module Lookup.
      Module DependencyRelFibred := FibredRel Package Source.Dependee Source.DependencyElt Source.DependencyRel.
      Module ConflictClassRelFibred := FibredRel Package N ConflictClassElt ConflictClassRel.
      Module PackageSetFibred := FibredRel N V Package PackageSet.

      Module ConflictClassRelKeyPreimage := PreimageOfKeys ConflictClassElt Package ConflictClassRel PackageSet.
      Definition inClass (R : PackageSet.t) (Om : ConflictClassRel.t) (k : N.t) :
          PackageSet.t :=
        ConflictClassRelKeyPreimage.ofKeys (fun q => (q, k)) Om R.

      Lemma mem_inClass : forall R Om (k : N.t) (q : Package.t),
          PackageSet.In q (inClass R Om k) <->
          PackageSet.In q R /\ ConflictClassRel.In (q, k) Om.
      Proof. intros; unfold inClass; apply ConflictClassRelKeyPreimage.mem_ofKeys. Qed.

      Module NEqb := UOTEqb N.
      Module ConflictClassRelPreimage := Preimage ConflictClassElt ConflictClassRel.
      Definition classRelAt (Om : ConflictClassRel.t) (k : N.t) : ConflictClassRel.t :=
        ConflictClassRelPreimage.preimage snd (fun k' => NEqb.eqb k' k) Om.

      Lemma mem_classRelAt : forall Om (k k' : N.t) (q : Package.t),
          ConflictClassRel.In (q, k') (classRelAt Om k) <->
          ConflictClassRel.In (q, k') Om /\ k' = k.
      Proof.
        intros; unfold classRelAt; rewrite ConflictClassRelPreimage.mem_preimage;
          cbn [snd].
        rewrite NEqb.eqb_true_iff; reflexivity.
      Qed.

      Module SOpv := SetOps Package VersionOT PackageSet Reduced.VSet.
      Lemma versions_cls : forall R Om (k : N.t),
          Reduced.versions (reduceReal R Om) (Name.Cls k) =
          SOpv.map (fun q => Version.Name (fst q)) (inClass R Om k).
      Proof.
        intros R Om k; apply Reduced.VSet.ext; intro w.
        rewrite Reduced.mem_versions, mem_reduceReal, SOpv.mem_map.
        split.
        - intros [[p [_ Hp]] | [n [v [k' [Hc [Hq Hy]]]]]]; [discriminate Hp |].
          injection Hy as -> ->.
          exists (n, v); split; [apply mem_inClass; auto | reflexivity].
        - intros [[n v] [Hq ->]]; apply mem_inClass in Hq.
          right; exists n, v, k; tauto.
      Qed.

      Theorem versions_lookupOrig : forall R Om (n : N.t),
          Reduced.versions (reduceReal R Om) (Name.Orig n) =
          Reduced.versions (reduceReal (PackageSetFibred.tailFibre R n) ConflictClassRel.empty)
            (Name.Orig n).
      Proof.
        intros R Om n; apply Reduced.versions_ext; intro w.
        rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [HR Hq]] | [m [u [k [_ [_ Hy]]]]]];
            [| discriminate Hy].
          unfold embedPkg in Hq; cbn [fst snd] in Hq.
          injection Hq as -> ->.
          left; exists (qn, qv); split;
            [apply PackageSetFibred.mem_tailFibre; split; [exact HR | reflexivity]
            | reflexivity].
        - intros [[p [HR Hp]] | [m [u [k [Hc _]]]]].
          + apply PackageSetFibred.tailFibre_subset in HR.
            left; exists p; split; [exact HR | exact Hp].
          + destruct (ConflictClassRel.empty_spec Hc).
      Qed.

      Theorem dependees_lookupOrig : forall D Om (p : Package.t),
          Reduced.dependees (reduceDeps D Om) (embedPkg p) =
          Reduced.dependees
            (reduceDeps (DependencyRelFibred.tailFibre D p)
               (ConflictClassRelFibred.tailFibre Om p))
            (embedPkg p).
      Proof.
        intros D Om p; apply Reduced.dependees_ext; intros [m ws].
        rewrite !mem_reduceDeps.
        split.
        - intros [[q [n [vs [HD Hy]]]] | [qn [qv [k [Hc Hy]]]]].
          + assert (q = p) as -> by (apply embedPkg_injective; congruence).
            left; exists p, n, vs; split; [| exact Hy].
            apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
          + assert ((qn, qv) = p) as <-
              by (apply embedPkg_injective; congruence).
            right; exists qn, qv, k; split; [| exact Hy].
            apply ConflictClassRelFibred.mem_tailFibre; split; [exact Hc | reflexivity].
        - intros [[q [n [vs [HD Hy]]]] | [qn [qv [k [Hc Hy]]]]].
          + apply DependencyRelFibred.tailFibre_subset in HD.
            left; exists q, n, vs; split; [exact HD | exact Hy].
          + apply ConflictClassRelFibred.tailFibre_subset in Hc.
            right; exists qn, qv, k; split; [exact Hc | exact Hy].
      Qed.

      Theorem versions_lookupClass : forall R Om (k : N.t),
          Reduced.versions (reduceReal R Om) (Name.Cls k) =
          Reduced.versions (reduceReal (inClass R Om k) (classRelAt Om k))
            (Name.Cls k).
      Proof.
        intros R Om k; rewrite !versions_cls; f_equal.
        apply PackageSet.ext; intro q.
        rewrite !mem_inClass, mem_classRelAt; intuition.
      Qed.

      Theorem dependees_lookupClass :
        forall D Om (k : N.t) (n : Version.t),
          Reduced.dependees (reduceDeps D Om) (Name.Cls k, n) =
          Reduced.DependeeSet.empty.
      Proof.
        intros D Om k n; apply Reduced.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[q [m [vs [_ Hy]]]] | [m [u [k' [_ Hy]]]]];
          unfold embedPkg in Hy; congruence.
      Qed.
    End Lookup.
  End Reduction.
End ConflictClass.
