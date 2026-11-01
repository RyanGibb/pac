From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_vers.
Create Rewrite HintDb cmp_vers.

Inductive CmpOp : Type := OpGe | OpGt | OpLe | OpLt | OpEq | OpNe.

Module ComparisonOperatorComp <: ComparableType.
  Definition t := CmpOp.
  Definition rank (o : CmpOp) : nat :=
    match o with
    | OpGe => 0 | OpGt => 1 | OpLe => 2 | OpLt => 3 | OpEq => 4 | OpNe => 5
    end.

  Definition compare (o1 o2 : CmpOp) : comparison :=
    Nat.compare (rank o1) (rank o2).

  Lemma compare_eq_iff : forall o1 o2, compare o1 o2 = Eq <-> o1 = o2.
  Proof. cmp_eq_iff cmp_vers. Qed.

  Lemma compare_antisym : forall o1 o2,
      compare o2 o1 = CompOpp (compare o1 o2).
  Proof. cmp_antisym cmp_vers. Qed.

  Lemma compare_lt_trans : forall o1 o2 o3,
      compare o1 o2 = Lt -> compare o2 o3 = Lt -> compare o1 o3 = Lt.
  Proof. cmp_lt_trans cmp_vers. Qed.
End ComparisonOperatorComp.
Module ComparisonOperatorOT := UOTFromCompare ComparisonOperatorComp.

Definition cmpOpEvalBy {A} (cmp : A -> A -> comparison)
    (op : CmpOp) (x c : A) : bool :=
  match op with
  | OpGe => match cmp x c with Lt => false | _ => true end
  | OpGt => match cmp x c with Gt => true | _ => false end
  | OpLe => match cmp x c with Gt => false | _ => true end
  | OpLt => match cmp x c with Lt => true | _ => false end
  | OpEq => match cmp x c with Eq => true | _ => false end
  | OpNe => match cmp x c with Eq => false | _ => true end
  end.

Module Versions (N V : UsualOrderedType).
  Module Source := Core N V.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.

  Inductive Formula : Type :=
  | FTop
  | FBot
  | FConj (phi1 phi2 : Formula)
  | FDisj (phi1 phi2 : Formula)
  | FCmp (op : CmpOp) (c : V.t).

  Definition cmpOpEval (op : CmpOp) (v c : V.t) : bool :=
    cmpOpEvalBy V.compare op v c.

  Module VFacts := UOTCompareFacts V.
  Lemma cmpOpEval_ne_iff : forall v c, cmpOpEval OpNe v c = true <-> v <> c.
  Proof.
    intros v c; unfold cmpOpEval, cmpOpEvalBy.
    destruct (V.compare v c) eqn:Hc; split; intro H.
    - discriminate.
    - apply VFacts.compare_eq_iff in Hc; contradiction.
    - intro He; subst c;
        rewrite (proj2 (VFacts.compare_eq_iff v v) eq_refl) in Hc;
        discriminate.
    - reflexivity.
    - intro He; subst c;
        rewrite (proj2 (VFacts.compare_eq_iff v v) eq_refl) in Hc;
        discriminate.
    - reflexivity.
  Qed.

  Fixpoint Satisfies (v : V.t) (phi : Formula) : Prop :=
    match phi with
    | FTop => True
    | FBot => False
    | FConj phi1 phi2 => Satisfies v phi1 /\ Satisfies v phi2
    | FDisj phi1 phi2 => Satisfies v phi1 \/ Satisfies v phi2
    | FCmp op c => cmpOpEval op v c = true
    end.

  Fixpoint satisfiesb (v : V.t) (phi : Formula) : bool :=
    match phi with
    | FTop => true
    | FBot => false
    | FConj phi1 phi2 => andb (satisfiesb v phi1) (satisfiesb v phi2)
    | FDisj phi1 phi2 => orb (satisfiesb v phi1) (satisfiesb v phi2)
    | FCmp op c => cmpOpEval op v c
    end.

  Lemma satisfiesb_iff : forall v phi,
      satisfiesb v phi = true <-> Satisfies v phi.
  Proof.
    intros v phi;
      induction phi as [ | | phi1 IH1 phi2 IH2 | phi1 IH1 phi2 IH2 | op c ];
      simpl.
    - split; intros _; reflexivity + exact I.
    - split; intro H; [discriminate H | destruct H].
    - rewrite Bool.andb_true_iff, IH1, IH2; reflexivity.
    - rewrite Bool.orb_true_iff, IH1, IH2; reflexivity.
    - reflexivity.
  Qed.

  Definition eval (phi : Formula) (Vn : VSet.t) : VSet.t :=
    VSet.filter (fun v => satisfiesb v phi) Vn.

  Lemma mem_eval : forall phi Vn v,
      VSet.In v (eval phi Vn) <-> VSet.In v Vn /\ Satisfies v phi.
  Proof.
    intros phi Vn v; unfold eval; rewrite VSet.filter_spec', satisfiesb_iff.
    reflexivity.
  Qed.

  Module VersionFormulaComp <: ComparableType.
    Definition t := Formula.
    Definition rank (phi : Formula) : nat :=
      match phi with
      | FTop => 0 | FBot => 1 | FConj _ _ => 2 | FDisj _ _ => 3 | FCmp _ _ => 4
      end.

    Fixpoint compare (x y : Formula) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | FConj a1 b1, FConj a2 b2 => lex (compare a1 a2) (compare b1 b2)
          | FDisj a1 b1, FDisj a2 b2 => lex (compare a1 a2) (compare b1 b2)
          | FCmp o1 c1, FCmp o2 c2 =>
              lex (ComparisonOperatorComp.compare o1 o2) (V.compare c1 c2)
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof.
      intros x; induction x as [ | | a IHa b IHb | a IHa b IHb | o c ];
        intros y; destruct y; simpl; try (split; intro H; congruence).
      1,2: rewrite lex_eq_iff, IHa, IHb.
      3: rewrite lex_eq_iff, ComparisonOperatorComp.compare_eq_iff, VFacts.compare_eq_iff.
      all: split;
        [intros [-> ->]; reflexivity | intro H; injection H as -> ->; auto].
    Qed.

    Lemma compare_antisym : forall x y,
        compare y x = CompOpp (compare x y).
    Proof.
      intros x; induction x as [ | | a IHa b IHb | a IHa b IHb | o c ];
        intros y; destruct y; simpl; try reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - rewrite lex_opp, ComparisonOperatorComp.compare_antisym, VFacts.compare_antisym;
          reflexivity.
    Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof.
      intros x; induction x as [ | | a1 IHa b1 IHb | a1 IHa b1 IHb | o1 c1 ];
        intros y z; destruct y as [ | | a2 b2 | a2 b2 | o2 c2 ],
          z as [ | | a3 b3 | a3 b3 | o3 c3 ]; simpl; intros H1 H2;
        try congruence.
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (lex_lt_trans ComparisonOperatorComp.compare_eq_iff
                 (ComparisonOperatorComp.compare_lt_trans _ _ _) (VFacts.compare_lt_trans _ _ _)
                 H1 H2).
    Qed.
  End VersionFormulaComp.
  Module VersionFormulaOT := UOTFromCompare VersionFormulaComp.

  Module Dependee := PairUOT N VersionFormulaOT.
  Module DependencyElt := PairUOT Package Dependee.
  Module DependencyRel := FSetUOT DependencyElt.

  Record IsResolution
      (R : PackageSet.t) (D : DependencyRel.t) (r : Package.t) (S : PackageSet.t) : Prop :=
    { res_subset : PackageSet.Subset S R
    ; res_root_mem : PackageSet.In r S
    ; res_dep_closure :
        forall p, PackageSet.In p S ->
        forall (n : N.t) (phi : Formula),
          DependencyRel.In (p, (n, phi)) D ->
          exists v, Satisfies v phi /\ PackageSet.In (n, v) S
    ; res_version_unique : Source.VersionUnique S }.

  Module Reduction.
    Module SOvd := SetOps DependencyElt Source.DependencyElt DependencyRel Source.DependencyRel.
    Definition reduce (R : PackageSet.t) (D : DependencyRel.t) : Source.DependencyRel.t :=
      SOvd.map (fun '(p, (m, phi)) => (p, (m, eval phi (Source.versions R m)))) D.

    Lemma mem_reduce : forall R D (p : Package.t) (n : N.t) (vs : VSet.t),
        Source.DependencyRel.In (p, (n, vs)) (reduce R D) <->
        exists phi, DependencyRel.In (p, (n, phi)) D /\ vs = eval phi (Source.versions R n).
    Proof.
      intros R D p n vs; unfold reduce; rewrite SOvd.mem_map.
      split.
      - intros [[q [m phi]] [HeD He]]; cbn beta iota in He.
        injection He as -> -> ->.
        exists phi; split; [exact HeD | reflexivity].
      - intros [phi [HD ->]].
        exists (p, (n, phi)); split; [exact HD | reflexivity].
    Qed.

    Theorem version_formula_correct : forall R D r S,
        Source.IsResolution R (reduce R D) r S <-> IsResolution R D r S.
    Proof.
      intros R D r S; split; intros [Hsub Hroot Hdep Huniq]; constructor;
        try assumption.
      - intros p Hp m phi HD.
        destruct (Hdep p Hp m (eval phi (Source.versions R m))) as [v [Hv HvS]].
        + apply mem_reduce; exists phi; split; [exact HD | reflexivity].
        + apply mem_eval in Hv; exists v; split; [apply Hv | exact HvS].
      - intros p Hp m ws Hmem.
        apply mem_reduce in Hmem; destruct Hmem as [phi [HD ->]].
        destruct (Hdep p Hp m phi HD) as [v [Hv HvS]].
        exists v; split; [| exact HvS].
        apply mem_eval; split; [| exact Hv].
        apply Source.mem_versions, Hsub; exact HvS.
    Qed.

    Module Lookup.
      Module DependencyRelFibred := FibredLabelledRel Package N VersionFormulaOT DependencyElt DependencyRel.
      Module DependencyRelKeys := RelKeys N DependencyElt DependencyRel.
      Module PackageSetPreimage := Preimage Package PackageSet.

      Definition realPreimage (R : PackageSet.t) (Dp : DependencyRel.t) : PackageSet.t :=
        PackageSetPreimage.preimage fst (DependencyRelKeys.hasKey DependencyRelFibred.node Dp) R.

      Lemma versions_realPreimage : forall R Dp n,
          (exists q phi, DependencyRel.In (q, (n, phi)) Dp) ->
          Source.versions (realPreimage R Dp) n = Source.versions R n.
      Proof.
        intros R Dp m [q [phi He]].
        apply VSet.ext; intro v.
        rewrite !Source.mem_versions; unfold realPreimage.
        rewrite PackageSetPreimage.mem_preimage.
        split.
        - intros [H _]; exact H.
        - intro H; split; [exact H |].
          apply DependencyRelKeys.hasKey_iff.
          exists (q, (m, phi)); split; [exact He | reflexivity].
      Qed.

      Lemma dependees_fibre : forall R D (p : Package.t),
          Source.dependees (reduce R D) p =
          Source.dependees (reduce R (DependencyRelFibred.tailFibre D p)) p.
      Proof.
        intros R D p; apply Source.dependees_ext; intros [n vs]; rewrite !mem_reduce.
        split; intros [phi [HD ->]]; exists phi; split; try reflexivity.
        - apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
        - exact (DependencyRelFibred.tailFibre_subset _ _ _ HD).
      Qed.

      Lemma reduce_realPreimage : forall R Dp,
          reduce (realPreimage R Dp) Dp = reduce R Dp.
      Proof.
        intros R Dp; apply Source.DependencyRel.ext; intros [q [n vs]].
        rewrite !mem_reduce.
        split; intros [phi [HD ->]]; exists phi; split;
          [exact HD | | exact HD |];
          rewrite (versions_realPreimage R Dp n);
          solve [reflexivity
                | exists q, phi; exact HD].
      Qed.

      Module PackageSetFibred := FibredRel N V Package PackageSet.
      Theorem versions_lookup : forall R (n : N.t),
          Source.versions R n = Source.versions (PackageSetFibred.tailFibre R n) n.
      Proof.
        intros R n; apply Source.versions_ext; intro v.
        rewrite PackageSetFibred.mem_tailFibre; tauto.
      Qed.

      Theorem dependees_lookup : forall R D (p : Package.t),
        let Dp := DependencyRelFibred.tailFibre D p in
        Source.dependees (reduce R D) p =
        Source.dependees (reduce (realPreimage R Dp) Dp) p.
      Proof.
        intros R D p; cbv zeta;
          rewrite reduce_realPreimage; apply dependees_fibre.
      Qed.

      Module SOdp := SetOps DependencyElt Package DependencyRel PackageSet.
      Definition tails (D : DependencyRel.t) : PackageSet.t :=
        SOdp.map (fun '(q, _) => q) D.

      Lemma mem_tails : forall D (q : Package.t),
          PackageSet.In q (tails D) <-> exists d, DependencyRel.In (q, d) D.
      Proof.
        intros D q; unfold tails; rewrite SOdp.mem_map.
        split.
        - intros [[q0 d] [HeD He]]; cbn beta iota in He; subst q0; eauto.
        - intros [d HD]; exists (q, d); split; [exact HD | reflexivity].
      Qed.

      Module SOpcd := SetOps Package Source.DependencyElt PackageSet Source.DependencyRel.
      Corollary reduce_glue : forall R D,
          reduce R D =
          SOpcd.unionMap
            (fun p => reduce (realPreimage R (DependencyRelFibred.tailFibre D p))
                             (DependencyRelFibred.tailFibre D p))
            (tails D).
      Proof.
        intros R D; apply Source.DependencyRel.ext; intros [q [n ws]].
        rewrite SOpcd.mem_unionMap, mem_reduce.
        split.
        - intros [phi [HD ->]].
          exists q; split; [apply mem_tails; eauto |].
          rewrite reduce_realPreimage, mem_reduce.
          exists phi; split; [| reflexivity].
          apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
        - intros [p [_ Hy]].
          rewrite reduce_realPreimage, mem_reduce in Hy.
          destruct Hy as [phi [Hf ->]].
          apply DependencyRelFibred.mem_tailFibre in Hf; destruct Hf as [HD _].
          exists phi; split; [exact HD | reflexivity].
      Qed.

    End Lookup.
  End Reduction.
End Versions.
