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

Definition cmpComplement (op : CmpOp) : CmpOp :=
  match op with
  | OpGe => OpLt | OpGt => OpLe | OpLe => OpGt
  | OpLt => OpGe | OpEq => OpNe | OpNe => OpEq
  end.

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

Lemma cmpOpEvalBy_complement : forall A (cmp : A -> A -> comparison) op x c,
    cmpOpEvalBy cmp (cmpComplement op) x c = negb (cmpOpEvalBy cmp op x c).
Proof.
  intros A cmp [ | | | | | ] x c; simpl; destruct (cmp x c); reflexivity.
Qed.

Module Versions (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Module SOpv := SetOps Pkg V PkgSet VSet.
  Definition realVersions (R : PkgSet.t) (n : N.t) : VSet.t :=
    SOpv.filterMap (fun '(m, v) => if N.eq_dec m n then Some v else None) R.

  Lemma realVersions_spec : forall R n v,
      VSet.In v (realVersions R n) <-> PkgSet.In (n, v) R.
  Proof.
    intros R m v; unfold realVersions; rewrite SOpv.mem_filterMap.
    split.
    - intros [[pn pv] [HpR Hp]]; cbn beta iota in Hp.
      destruct (N.eq_dec pn m) as [-> | NE]; [| discriminate].
      injection Hp as <-; exact HpR.
    - intro H; exists (m, v); split; [exact H | cbn beta iota].
      destruct (N.eq_dec m m) as [_ | NE];
        [reflexivity | contradiction NE; reflexivity].
  Qed.

  Inductive Formula : Type :=
  | FTop
  | FBot
  | FConj (f1 f2 : Formula)
  | FDisj (f1 f2 : Formula)
  | FCmp (op : CmpOp) (c : V.t).

  Definition cmpOpEval (op : CmpOp) (v c : V.t) : bool :=
    cmpOpEvalBy V.compare op v c.

  Module VF := UOTCompareFacts V.
  Lemma cmpOpEval_ne_iff : forall v w, cmpOpEval OpNe v w = true <-> v <> w.
  Proof.
    intros v w; unfold cmpOpEval, cmpOpEvalBy.
    destruct (V.compare v w) eqn:Hc; split; intro H.
    - discriminate.
    - apply VF.compare_eq_iff in Hc; contradiction.
    - intro He; subst w;
        rewrite (proj2 (VF.compare_eq_iff v v) eq_refl) in Hc;
        discriminate.
    - reflexivity.
    - intro He; subst w;
        rewrite (proj2 (VF.compare_eq_iff v v) eq_refl) in Hc;
        discriminate.
    - reflexivity.
  Qed.

  Fixpoint eval (f : Formula) (Vn : VSet.t) : VSet.t :=
    match f with
    | FTop => Vn
    | FBot => VSet.empty
    | FConj f1 f2 => VSet.inter (eval f1 Vn) (eval f2 Vn)
    | FDisj f1 f2 => VSet.union (eval f1 Vn) (eval f2 Vn)
    | FCmp op c => VSet.filter (fun v => cmpOpEval op v c) Vn
    end.

  Module FComp <: ComparableType.
    Definition t := Formula.
    Definition rank (f : Formula) : nat :=
      match f with
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
      - rewrite lex_eq_iff, IHa, IHb.
        split;
          [intros [-> ->]; reflexivity
          | intro H; injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb.
        split;
          [intros [-> ->]; reflexivity
          | intro H; injection H as -> ->; auto].
      - rewrite lex_eq_iff, OpComp.compare_eq_iff, VF.compare_eq_iff.
        split;
          [intros [-> ->]; reflexivity
          | intro H; injection H as -> ->; auto].
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
      - (* Conj / Conj / Conj *)
        exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - (* Disj / Disj / Disj *)
        exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - (* Cmp / Cmp / Cmp *)
        exact (lex_lt_trans OpComp.compare_eq_iff
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
        forall (n : N.t) (f : Formula),
          DepRel.In (p, (n, f)) D ->
          exists v, VSet.In v (eval f (realVersions R n)) /\ PkgSet.In (n, v) S
    ; res_version_unique : C.VersionUnique S }.

  Module Reduction.
    Module SOvd := SetOps DepElt C.DepElt DepRel C.DepRel.
    Definition reduce (R : PkgSet.t) (D : DepRel.t) : C.DepRel.t :=
      SOvd.map (fun '(p, (n, f)) => (p, (n, eval f (realVersions R n)))) D.

    Lemma mem_reduce : forall R D (p : Pkg.t) (n : N.t) (ws : VSet.t),
        C.DepRel.In (p, (n, ws)) (reduce R D) <->
        exists f, DepRel.In (p, (n, f)) D /\ ws = eval f (realVersions R n).
    Proof.
      intros R D p n ws; unfold reduce; rewrite SOvd.mem_map.
      split.
      - intros [[q [m f]] [HeD He]]; cbn beta iota in He.
        injection He as -> -> ->.
        exists f; split; [exact HeD | reflexivity].
      - intros [f [HD ->]].
        exists (p, (n, f)); split; [exact HD | reflexivity].
    Qed.

    Theorem version_formula_correct : forall R D r S,
        C.IsResolution R (reduce R D) r S <-> IsResolution R D r S.
    Proof.
      intros R D r S; split; intros [Hsub Hroot Hdep Huniq]; constructor;
        try assumption.
      - intros p Hp m f HD.
        apply (Hdep p Hp m (eval f (realVersions R m))).
        apply mem_reduce; exists f; split; [exact HD | reflexivity].
      - intros p Hp m ws Hmem.
        apply mem_reduce in Hmem; destruct Hmem as [f [HD ->]].
        exact (Hdep p Hp m f HD).
    Qed.
  End Reduction.
End Versions.
