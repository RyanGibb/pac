From Stdlib Require Import Orders.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_cls.
Create Rewrite HintDb cmp_cls.

Module ConflictClass (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Module InClassElt := PairUOT Pkg N.
  Module InClassRel := FSetUOT InClassElt.

  (* Apart from the record so that a frontend's resolution can carry it as
     one field.  Cargo's links is this as it stands; opam's rule, stated
     over names, exempts two versions of one package, an exemption version
     uniqueness never lets apply. *)
  Definition ClassExclusion (Om : InClassRel.t) (S : PkgSet.t) : Prop :=
    forall (k : N.t) (p q : Pkg.t), PkgSet.In p S -> PkgSet.In q S ->
      InClassRel.In (p, k) Om -> InClassRel.In (q, k) Om -> p = q.

  Record IsResolution
      (R : PkgSet.t) (D : C.DepRel.t) (Om : InClassRel.t) (r : Pkg.t)
      (S : PkgSet.t) : Prop :=
    { res_core : C.IsResolution R D r S
    ; res_class_exclusion : ClassExclusion Om S }.

  Module Reduction.
    Module NF := UOTCompareFacts N.
    Module VF := UOTCompareFacts V.
    Module PF := UOTCompareFacts Pkg.
    #[local] Hint Rewrite NF.compare_eq_iff VF.compare_eq_iff
      PF.compare_eq_iff : cmp_cls.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_cls.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_cls.
    #[local] Hint Extern 1 => cmp_by PF.compare_antisym : cmp_cls.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_cls.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_cls.
    #[local] Hint Extern 1 => cmp_by PF.compare_lt_trans : cmp_cls.

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
      | Pkg (p : Pkg.t).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, Pkg _ => Lt
        | Pkg _, Orig _ => Gt
        | Pkg p1, Pkg p2 => Pkg.compare p1 p2
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
    Module T := Core NameOT VersionOT.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      (Name.Orig (fst p), Version.Orig (snd p)).

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition embedSet (S : PkgSet.t) : T.PkgSet.t := SOpt.map embedPkg S.

    Module SOvt := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t := SOvt.map Version.Orig vs.

    (* One for each class each package of X is in: at R these are the class
       packages, at a class resolution the ones it selects. *)
    Module SOit := SetOps InClassElt T.Pkg InClassRel T.PkgSet.
    Definition classPkgs (X : PkgSet.t) (Om : InClassRel.t) : T.PkgSet.t :=
      SOit.filterMap (fun '(q, k) =>
          if PkgSet.mem q X
          then Some (Name.Cls k, Version.Pkg q)
          else None)
        Om.

    Lemma mem_classPkgs : forall X Om (y : T.Pkg.t),
        T.PkgSet.In y (classPkgs X Om) <->
        exists q k, InClassRel.In (q, k) Om /\ PkgSet.In q X /\
          y = (Name.Cls k, Version.Pkg q).
    Proof.
      intros X Om y; unfold classPkgs; rewrite SOit.mem_filterMap.
      split.
      - intros [[q k] [Hc Hy]]; cbn beta iota in Hy.
        destruct (PkgSet.mem q X) eqn:Hm; [| discriminate].
        injection Hy as <-.
        exists q, k; split; [exact Hc |].
        split; [apply PkgSet.mem_spec; exact Hm | reflexivity].
      - intros [q [k [Hc [Hq ->]]]].
        exists (q, k); split; [exact Hc | cbn beta iota].
        rewrite (proj2 (PkgSet.mem_spec _ _) Hq); reflexivity.
    Qed.

    Definition reduceReal (R : PkgSet.t) (Om : InClassRel.t) : T.PkgSet.t :=
      T.PkgSet.union (embedSet R) (classPkgs R Om).

    Lemma mem_reduceReal : forall R Om (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal R Om) <->
        (exists p, PkgSet.In p R /\ y = embedPkg p) \/
        (exists q k, InClassRel.In (q, k) Om /\ PkgSet.In q R /\
           y = (Name.Cls k, Version.Pkg q)).
    Proof.
      intros; unfold reduceReal, embedSet.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, mem_classPkgs; reflexivity.
    Qed.

    Module SOdtd := SetOps C.DepElt T.DepElt C.DepRel T.DepRel.
    Definition origEdges (D : C.DepRel.t) : T.DepRel.t :=
      SOdtd.map (fun '(p, (n, vs)) => (embedPkg p, (Name.Orig n, embedVS vs)))
        D.

    (* Each package in a class depends on itself at that class, and version
       uniqueness there does the excluding: one edge per package and class it
       is in, where pairwise conflicts would need one per pair of packages in
       the class. *)
    Module SOitd := SetOps InClassElt T.DepElt InClassRel T.DepRel.
    Definition classEdges (Om : InClassRel.t) : T.DepRel.t :=
      SOitd.map (fun '(q, k) =>
          (embedPkg q, (Name.Cls k, T.VSet.singleton (Version.Pkg q))))
        Om.

    Definition reduceDeps (D : C.DepRel.t) (Om : InClassRel.t) : T.DepRel.t :=
      T.DepRel.union (origEdges D) (classEdges Om).

    Lemma mem_origEdges : forall (D : C.DepRel.t) (y : T.DepElt.t),
        T.DepRel.In y (origEdges D) <->
        exists p n vs, C.DepRel.In (p, (n, vs)) D /\
          y = (embedPkg p, (Name.Orig n, embedVS vs)).
    Proof.
      intros D y; unfold origEdges; rewrite SOdtd.mem_map.
      split.
      - intros [[q [n vs]] [HD Hy]]; cbn beta iota in Hy.
        exists q, n, vs; split; [exact HD | exact Hy].
      - intros [p [n [vs [HD ->]]]].
        exists (p, (n, vs)); split; [exact HD | reflexivity].
    Qed.

    Lemma mem_classEdges : forall Om (y : T.DepElt.t),
        T.DepRel.In y (classEdges Om) <->
        exists q k, InClassRel.In (q, k) Om /\
          y = (embedPkg q, (Name.Cls k, T.VSet.singleton (Version.Pkg q))).
    Proof.
      intros Om y; unfold classEdges; rewrite SOitd.mem_map.
      split.
      - intros [[q k] [Hc Hy]]; cbn beta iota in Hy.
        exists q, k; split; [exact Hc | exact Hy].
      - intros [q [k [Hc ->]]].
        exists (q, k); split; [exact Hc | reflexivity].
    Qed.

    Lemma mem_reduceDeps : forall D Om (y : T.DepElt.t),
        T.DepRel.In y (reduceDeps D Om) <->
        (exists p n vs, C.DepRel.In (p, (n, vs)) D /\
           y = (embedPkg p, (Name.Orig n, embedVS vs))) \/
        (exists q k, InClassRel.In (q, k) Om /\
           y = (embedPkg q,
                (Name.Cls k, T.VSet.singleton (Version.Pkg q)))).
    Proof.
      intros; unfold reduceDeps.
      rewrite T.DepRel.union_spec, mem_origEdges, mem_classEdges;
        reflexivity.
    Qed.

    Definition reduce (R : PkgSet.t) (D : C.DepRel.t) (Om : InClassRel.t) :
        T.PkgSet.t * T.DepRel.t :=
      (reduceReal R Om, reduceDeps D Om).

    Definition tryInvPkg (p : T.Pkg.t) : option Pkg.t :=
      match p with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : T.Pkg.t) (p : Pkg.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [[n | k] [v | q]] p H; simpl in H; try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
    Lemma embedPkg_injective :
      forall p q : Pkg.t, embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOtp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

    Definition classResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_classResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (classResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold classResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma embedPkg_mem_real : forall (p : Pkg.t) R Om,
        T.PkgSet.In (embedPkg p) (reduceReal R Om) -> PkgSet.In p R.
    Proof.
      intros p R Om H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [q [k [_ [_ Hy]]]]].
      - apply embedPkg_injective in Hq; subst q; exact HqR.
      - discriminate Hy.
    Qed.

    Theorem reduceDeps_functionalInName : forall D Om,
        C.FunctionalInName D -> T.FunctionalInName (reduceDeps D Om).
    Proof.
      intros D Om Hfn p' n' ws1 ws2 H1 H2.
      apply mem_reduceDeps in H1, H2.
      destruct H1 as [[p [n [vs [HD E]]]] | [q [k [Hc E]]]];
        destruct H2 as [[p2 [n2 [vs2 [HD2 E2]]]] | [q2 [k2 [Hc2 E2]]]];
        try congruence.
      - assert (p2 = p) as -> by (apply embedPkg_injective; congruence).
        assert (n2 = n) as -> by congruence.
        rewrite (Hfn _ _ _ _ HD HD2) in E; congruence.
      - assert (q2 = q) as -> by (apply embedPkg_injective; congruence).
        congruence.
    Qed.

    Theorem conflict_class_soundness :
      forall R D Om (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R Om) (reduceDeps D Om) (embedPkg r) S ->
        IsResolution R D Om r (classResolution S).
    Proof.
      intros R D Om r S [Hsub Hroot Hdep Huniq].
      assert (Hcls : forall q k,
                 PkgSet.In q (classResolution S) -> InClassRel.In (q, k) Om ->
                 T.PkgSet.In (Name.Cls k, Version.Pkg q) S).
      { intros q k Hq Hc; apply mem_classResolution in Hq.
        assert (Hd : T.DepRel.In
                       (embedPkg q,
                        (Name.Cls k, T.VSet.singleton (Version.Pkg q)))
                       (reduceDeps D Om))
          by (apply mem_reduceDeps; right; exists q, k;
              split; [exact Hc | reflexivity]).
        destruct (Hdep _ Hq _ _ Hd) as [w [Hw HwS]].
        rewrite SOvt.singleton_in in Hw; subst w; exact HwS. }
      constructor.
      - constructor.
        + intros p Hp; apply mem_classResolution in Hp.
          exact (embedPkg_mem_real p R Om (Hsub _ Hp)).
        + apply mem_classResolution; exact Hroot.
        + intros p Hp m vs HD; apply mem_classResolution in Hp.
          assert (Hd : T.DepRel.In (embedPkg p, (Name.Orig m, embedVS vs))
                         (reduceDeps D Om))
            by (apply mem_reduceDeps; left; exists p, m, vs;
                split; [exact HD | reflexivity]).
          destruct (Hdep _ Hp _ _ Hd) as [w [Hw HwS]].
          unfold embedVS in Hw; apply SOvt.mem_map in Hw;
            destruct Hw as [v [Hv ->]].
          exists v; split;
            [exact Hv | apply mem_classResolution; exact HwS].
        + intros n v v' Hv Hv'; apply mem_classResolution in Hv, Hv'.
          assert (E : Version.Orig v = Version.Orig v')
            by (apply (Huniq (Name.Orig n)); assumption).
          injection E as E; exact E.
      - intros k p q Hp Hq Hpk Hqk.
        assert (E : Version.Pkg p = Version.Pkg q)
          by exact (Huniq (Name.Cls k) _ _ (Hcls p k Hp Hpk) (Hcls q k Hq Hqk)).
        injection E as E; exact E.
    Qed.

    (* The reduction's own package set, taken at the class resolution: <k>
       is selected at p exactly when p is. *)
    Definition coreResolution (S : PkgSet.t) (Om : InClassRel.t) :
        T.PkgSet.t :=
      reduceReal S Om.

    Theorem conflict_class_completeness :
      forall R D Om (r : Pkg.t) (S : PkgSet.t),
        IsResolution R D Om r S ->
        T.IsResolution (reduceReal R Om) (reduceDeps D Om) (embedPkg r)
          (coreResolution S Om).
    Proof.
      intros R D Om r S [[Hsub Hroot Hdep Huniq] Hexcl].
      unfold coreResolution; constructor.
      - intros y Hy; apply mem_reduceReal in Hy; apply mem_reduceReal.
        destruct Hy as [[p [Hp ->]] | [q [k [Hc [Hq ->]]]]].
        + left; exists p; split; [exact (Hsub _ Hp) | reflexivity].
        + right; exists q, k; split; [exact Hc |].
          split; [exact (Hsub _ Hq) | reflexivity].
      - apply mem_reduceReal; left; exists r; split;
          [exact Hroot | reflexivity].
      - intros y Hy m ws Hd; apply mem_reduceDeps in Hd.
        destruct Hd as [[p [n [vs [HD Hyd]]]] | [q [k [Hc Hyd]]]];
          injection Hyd as -> -> ->.
        + apply embedPkg_mem_real in Hy.
          destruct (Hdep p Hy n vs HD) as [v [Hv HvS]].
          exists (Version.Orig v); split.
          * unfold embedVS; apply SOvt.mem_map; exists v; auto.
          * apply mem_reduceReal; left; exists (n, v);
              split; [exact HvS | reflexivity].
        + apply embedPkg_mem_real in Hy.
          exists (Version.Pkg q); split.
          * apply SOvt.singleton_in; reflexivity.
          * apply mem_reduceReal; right; exists q, k;
              split; [exact Hc | split; [exact Hy | reflexivity]].
      - intros n w w' Hw Hw'; apply mem_reduceReal in Hw, Hw'.
        destruct Hw as [[p [Hp E]] | [q [k [Hc [Hq E]]]]];
          destruct Hw' as [[p' [Hp' E']] | [q' [k' [Hc' [Hq' E']]]]];
          unfold embedPkg in *; try congruence.
        + destruct p as [pn pv], p' as [pn' pv']; cbn [fst snd] in E, E'.
          assert (pn' = pn) as -> by congruence.
          rewrite (Huniq pn pv pv' Hp Hp') in E; congruence.
        + assert (k' = k) as -> by congruence.
          rewrite (Hexcl k q q' Hq Hq' Hc Hc') in E; congruence.
    Qed.

    Theorem classResolution_coreResolution : forall (S : PkgSet.t) Om,
        classResolution (coreResolution S Om) = S.
    Proof.
      intros S Om; apply PkgSet.ext; intro p.
      rewrite mem_classResolution; unfold coreResolution.
      split; [exact (embedPkg_mem_real p S Om) |].
      intro H; apply mem_reduceReal; left; exists p; split;
        [exact H | reflexivity].
    Qed.

    Module Lookup.
      Module DepRelFibred := FibredRel Pkg C.Dependees C.DepElt C.DepRel.
      Module InClassFibred := FibredRel Pkg N InClassElt InClassRel.
      Module PkgFibred := FibredRel N V Pkg PkgSet.

      Module InClassPre := PreimageOfKeys InClassElt Pkg InClassRel PkgSet.
      Definition inClass (R : PkgSet.t) (Om : InClassRel.t) (k : N.t) :
          PkgSet.t :=
        InClassPre.ofKeys (fun q => (q, k)) Om R.

      Lemma mem_inClass : forall R Om (k : N.t) (q : Pkg.t),
          PkgSet.In q (inClass R Om k) <->
          PkgSet.In q R /\ InClassRel.In (q, k) Om.
      Proof. intros; unfold inClass; apply InClassPre.mem_ofKeys. Qed.

      Module NEqb := UOTEqb N.
      Module ClassRelPre := Preimage InClassElt InClassRel.
      Definition classRelAt (Om : InClassRel.t) (k : N.t) : InClassRel.t :=
        ClassRelPre.preimage snd (fun k' => NEqb.eqb k' k) Om.

      Lemma mem_classRelAt : forall Om (k k' : N.t) (q : Pkg.t),
          InClassRel.In (q, k') (classRelAt Om k) <->
          InClassRel.In (q, k') Om /\ k' = k.
      Proof.
        intros; unfold classRelAt; rewrite ClassRelPre.mem_preimage;
          cbn [snd].
        rewrite NEqb.eqb_true_iff; reflexivity.
      Qed.

      Module SOpv := SetOps Pkg VersionOT PkgSet T.VSet.
      Lemma versions_cls : forall R Om (k : N.t),
          T.versions (reduceReal R Om) (Name.Cls k) =
          SOpv.map Version.Pkg (inClass R Om k).
      Proof.
        intros R Om k; apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal, SOpv.mem_map.
        split.
        - intros [[p [_ Hp]] | [q [k' [Hc [Hq Hy]]]]]; [discriminate Hp |].
          injection Hy as -> ->.
          exists q; split; [apply mem_inClass; auto | reflexivity].
        - intros [q [Hq ->]]; apply mem_inClass in Hq.
          right; exists q, k; tauto.
      Qed.

      Theorem versions_lookupOrig : forall R Om (n : N.t),
          T.versions (reduceReal R Om) (Name.Orig n) =
          T.versions (reduceReal (PkgFibred.tailFibre R n) InClassRel.empty)
            (Name.Orig n).
      Proof.
        intros R Om n; apply T.versions_ext; intro w.
        rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [HR Hq]] | [q [k [_ [_ Hy]]]]]; [| discriminate Hy].
          unfold embedPkg in Hq; cbn [fst snd] in Hq.
          injection Hq as -> ->.
          left; exists (qn, qv); split;
            [apply PkgFibred.mem_tailFibre; split; [exact HR | reflexivity]
            | reflexivity].
        - intros [[p [HR Hp]] | [q [k [Hc _]]]].
          + apply PkgFibred.tailFibre_subset in HR.
            left; exists p; split; [exact HR | exact Hp].
          + destruct (InClassRel.empty_spec Hc).
      Qed.

      Theorem dependees_lookupOrig : forall D Om (p : Pkg.t),
          T.dependees (reduceDeps D Om) (embedPkg p) =
          T.dependees
            (reduceDeps (DepRelFibred.tailFibre D p)
               (InClassFibred.tailFibre Om p))
            (embedPkg p).
      Proof.
        intros D Om p; apply T.dependees_ext; intros [m ws].
        rewrite !mem_reduceDeps.
        split.
        - intros [[q [n [vs [HD Hy]]]] | [q [k [Hc Hy]]]];
            assert (q = p) as -> by (apply embedPkg_injective; congruence).
          + left; exists p, n, vs; split; [| exact Hy].
            apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
          + right; exists p, k; split; [| exact Hy].
            apply InClassFibred.mem_tailFibre; split; [exact Hc | reflexivity].
        - intros [[q [n [vs [HD Hy]]]] | [q [k [Hc Hy]]]].
          + apply DepRelFibred.tailFibre_subset in HD.
            left; exists q, n, vs; split; [exact HD | exact Hy].
          + apply InClassFibred.tailFibre_subset in Hc.
            right; exists q, k; split; [exact Hc | exact Hy].
      Qed.

      (* A preimage: the declarations of a package in k name no other.  It
         is on the versions side, which a solver re-asks at every decision,
         so a lazy driver can recompute it per ask; on the dependees side,
         read once, it could not be. *)
      Theorem versions_lookupClass : forall R Om (k : N.t),
          T.versions (reduceReal R Om) (Name.Cls k) =
          T.versions (reduceReal (inClass R Om k) (classRelAt Om k))
            (Name.Cls k).
      Proof.
        intros R Om k; rewrite !versions_cls; f_equal.
        apply PkgSet.ext; intro q.
        rewrite !mem_inClass, mem_classRelAt; intuition.
      Qed.

      Theorem dependees_lookupClass :
        forall D Om (k : N.t) (w : Version.t),
          T.dependees (reduceDeps D Om) (Name.Cls k, w) =
          T.DependeesSet.empty.
      Proof.
        intros D Om k w; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[q [n [vs [_ Hy]]]] | [q [k' [_ Hy]]]];
          unfold embedPkg in Hy; congruence.
      Qed.
    End Lookup.
  End Reduction.
End ConflictClass.
