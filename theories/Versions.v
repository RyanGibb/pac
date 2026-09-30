From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_vers.
Create Rewrite HintDb cmp_vers.

Inductive CmpOp : Type := OpGe | OpGt | OpLe | OpLt | OpEq | OpNe.

Module OpComp <: ComparableType.
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
End OpComp.
Module OpOT := UOTFromCompare OpComp.

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
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive Formula : Type :=
  | FTop
  | FBot
  | FConj (phi1 phi2 : Formula)
  | FDisj (phi1 phi2 : Formula)
  | FCmp (op : CmpOp) (c : V.t).

  Definition cmpOpEval (op : CmpOp) (v c : V.t) : bool :=
    cmpOpEvalBy V.compare op v c.

  Module VF := UOTCompareFacts V.
  Lemma cmpOpEval_ne_iff : forall v c, cmpOpEval OpNe v c = true <-> v <> c.
  Proof.
    intros v c; unfold cmpOpEval, cmpOpEvalBy.
    destruct (V.compare v c) eqn:Hc; split; intro H.
    - discriminate.
    - apply VF.compare_eq_iff in Hc; contradiction.
    - intro He; subst c;
        rewrite (proj2 (VF.compare_eq_iff v v) eq_refl) in Hc;
        discriminate.
    - reflexivity.
    - intro He; subst c;
        rewrite (proj2 (VF.compare_eq_iff v v) eq_refl) in Hc;
        discriminate.
    - reflexivity.
  Qed.

  Fixpoint eval (phi : Formula) (Vn : VSet.t) : VSet.t :=
    match phi with
    | FTop => Vn
    | FBot => VSet.empty
    | FConj phi1 phi2 => VSet.inter (eval phi1 Vn) (eval phi2 Vn)
    | FDisj phi1 phi2 => VSet.union (eval phi1 Vn) (eval phi2 Vn)
    | FCmp op c => VSet.filter (fun v => cmpOpEval op v c) Vn
    end.

  Module FComp <: ComparableType.
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
              lex (OpComp.compare o1 o2) (V.compare c1 c2)
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof.
      intros x; induction x as [ | | a IHa b IHb | a IHa b IHb | o c ];
        intros y; destruct y; simpl; try (split; intro H; congruence).
      1,2: rewrite lex_eq_iff, IHa, IHb.
      3: rewrite lex_eq_iff, OpComp.compare_eq_iff, VF.compare_eq_iff.
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
      - rewrite lex_opp, OpComp.compare_antisym, VF.compare_antisym;
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
      - exact (lex_lt_trans OpComp.compare_eq_iff
                 (OpComp.compare_lt_trans _ _ _) (VF.compare_lt_trans _ _ _)
                 H1 H2).
    Qed.
  End FComp.
  Module FOT := UOTFromCompare FComp.

  Module Dependees := PairUOT N FOT.
  Module DepElt := PairUOT Pkg Dependees.
  Module DepRel := FSetUOT DepElt.

  Record IsResolution
      (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_dep_closure :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (phi : Formula),
          DepRel.In (p, (n, phi)) D ->
          exists v, VSet.In v (eval phi (C.versions R n)) /\ PkgSet.In (n, v) S
    ; res_version_unique : C.VersionUnique S }.

  Module Reduction.
    Module SOvd := SetOps DepElt C.DepElt DepRel C.DepRel.
    Definition reduce (R : PkgSet.t) (D : DepRel.t) : C.DepRel.t :=
      SOvd.map (fun '(p, (m, phi)) => (p, (m, eval phi (C.versions R m)))) D.

    Lemma mem_reduce : forall R D (p : Pkg.t) (n : N.t) (vs : VSet.t),
        C.DepRel.In (p, (n, vs)) (reduce R D) <->
        exists phi, DepRel.In (p, (n, phi)) D /\ vs = eval phi (C.versions R n).
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
        C.IsResolution R (reduce R D) r S <-> IsResolution R D r S.
    Proof.
      intros R D r S; split; intros [Hsub Hroot Hdep Huniq]; constructor;
        try assumption.
      - intros p Hp m phi HD.
        apply (Hdep p Hp m (eval phi (C.versions R m))).
        apply mem_reduce; exists phi; split; [exact HD | reflexivity].
      - intros p Hp m ws Hmem.
        apply mem_reduce in Hmem; destruct Hmem as [phi [HD ->]].
        exact (Hdep p Hp m phi HD).
    Qed.

    Module Lookup.
      Module DepRelFibred := FibredLabelledRel Pkg N FOT DepElt DepRel.
      Module DepKeys := RelKeys N DepElt DepRel.
      Module PkgPreimage := Preimage Pkg PkgSet.

      Definition realPreimage (R : PkgSet.t) (Dp : DepRel.t) : PkgSet.t :=
        PkgPreimage.preimage fst (DepKeys.hasKey DepRelFibred.node Dp) R.

      Lemma versions_realPreimage : forall R Dp n,
          (exists q m phi, DepRel.In (q, (m, phi)) Dp /\ m = n) ->
          C.versions (realPreimage R Dp) n = C.versions R n.
      Proof.
        intros R Dp m [q [m' [phi [He Hm]]]].
        apply VSet.ext; intro v.
        rewrite !C.mem_versions; unfold realPreimage.
        rewrite PkgPreimage.mem_preimage.
        split.
        - intros [H _]; exact H.
        - intro H; split; [exact H |].
          apply DepKeys.hasKey_iff.
          exists (q, (m', phi)); split; [exact He | exact Hm].
      Qed.

      Lemma dependees_fibre : forall R D (p : Pkg.t),
          C.dependees (reduce R D) p =
          C.dependees (reduce R (DepRelFibred.tailFibre D p)) p.
      Proof.
        intros R D p; apply C.dependees_ext; intros [n vs]; rewrite !mem_reduce.
        split; intros [phi [HD ->]]; exists phi; split; try reflexivity.
        - apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
        - exact (DepRelFibred.tailFibre_subset _ _ _ HD).
      Qed.

      Lemma reduce_realPreimage : forall R Dp,
          reduce (realPreimage R Dp) Dp = reduce R Dp.
      Proof.
        intros R Dp; apply C.DepRel.ext; intros [q [n vs]].
        rewrite !mem_reduce.
        split; intros [phi [HD ->]]; exists phi; split;
          [exact HD | | exact HD |];
          rewrite (versions_realPreimage R Dp n);
          solve [reflexivity
                | exists q, n, phi; split; [exact HD | reflexivity]].
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Theorem versions_lookup : forall R (n : N.t),
          C.versions R n = C.versions (PkgFibred.tailFibre R n) n.
      Proof.
        intros R n; apply C.versions_ext; intro v.
        rewrite PkgFibred.mem_tailFibre; tauto.
      Qed.

      Theorem dependees_lookup : forall R D (p : Pkg.t),
        let Dp := DepRelFibred.tailFibre D p in
        C.dependees (reduce R D) p =
        C.dependees (reduce (realPreimage R Dp) Dp) p.
      Proof.
        intros R D p; cbv zeta;
          rewrite reduce_realPreimage; apply dependees_fibre.
      Qed.

      Module SOdp := SetOps DepElt Pkg DepRel PkgSet.
      Definition tails (D : DepRel.t) : PkgSet.t :=
        SOdp.map (fun '(q, _) => q) D.

      Lemma mem_tails : forall D (q : Pkg.t),
          PkgSet.In q (tails D) <-> exists d, DepRel.In (q, d) D.
      Proof.
        intros D q; unfold tails; rewrite SOdp.mem_map.
        split.
        - intros [[q0 d] [HeD He]]; cbn beta iota in He; subst q0; eauto.
        - intros [d HD]; exists (q, d); split; [exact HD | reflexivity].
      Qed.

      Module SOpcd := SetOps Pkg C.DepElt PkgSet C.DepRel.
      Corollary reduce_glue : forall R D,
          reduce R D =
          SOpcd.unionMap
            (fun p => reduce (realPreimage R (DepRelFibred.tailFibre D p))
                             (DepRelFibred.tailFibre D p))
            (tails D).
      Proof.
        intros R D; apply C.DepRel.ext; intros [q [n ws]].
        rewrite SOpcd.mem_unionMap, mem_reduce.
        split.
        - intros [phi [HD ->]].
          exists q; split; [apply mem_tails; eauto |].
          rewrite reduce_realPreimage, mem_reduce.
          exists phi; split; [| reflexivity].
          apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
        - intros [p [_ Hy]].
          rewrite reduce_realPreimage, mem_reduce in Hy.
          destruct Hy as [phi [Hf ->]].
          apply DepRelFibred.mem_tailFibre in Hf; destruct Hf as [HD _].
          exists phi; split; [exact HD | reflexivity].
      Qed.

    End Lookup.
  End Reduction.
End Versions.
