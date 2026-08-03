From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core Versions.

Create HintDb cmp_varf.
Create Rewrite HintDb cmp_varf.

Module VariableFormula (N V : UsualOrderedType)
    (X : FiniteUsualOrderedType) (Y : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive Formula : Type :=
  | FDep (n : N.t) (vs : VSet.t)
  | FConj (f1 f2 : Formula)
  | FDisj (f1 f2 : Formula)
  | FNeg (f : Formula)
  | FVarCmp (x : X.t) (op : CmpOp) (y : Y.t).

  Definition opEvalY (op : CmpOp) (y' y : Y.t) : bool :=
    cmpOpEvalBy Y.compare op y' y.

  Lemma opEvalY_complement : forall op y' y,
      opEvalY (cmpComplement op) y' y = negb (opEvalY op y' y).
  Proof. intros op y' y; apply cmpOpEvalBy_complement. Qed.

  Fixpoint Satisfies (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) : Prop :=
    match f with
    | FDep n vs => exists v, VSet.In v vs /\ PkgSet.In (n, v) S
    | FConj f1 f2 => Satisfies S sigma f1 /\ Satisfies S sigma f2
    | FDisj f1 f2 => Satisfies S sigma f1 \/ Satisfies S sigma f2
    | FNeg f1 => ~ Satisfies S sigma f1
    | FVarCmp x op y => opEvalY op (sigma x) y = true
    end.

  Fixpoint satisfiesb (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
      bool :=
    match f with
    | FDep n vs => VSet.exists_ (fun v => PkgSet.mem (n, v) S) vs
    | FConj f1 f2 => andb (satisfiesb S sigma f1) (satisfiesb S sigma f2)
    | FDisj f1 f2 => orb (satisfiesb S sigma f1) (satisfiesb S sigma f2)
    | FNeg f1 => negb (satisfiesb S sigma f1)
    | FVarCmp x op y => opEvalY op (sigma x) y
    end.

  Lemma satisfiesb_iff : forall S sigma f,
      satisfiesb S sigma f = true <-> Satisfies S sigma f.
  Proof.
    intros S sigma f;
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
      simpl.
    - rewrite VSet.exists_spec'.
      split; intros [v [Hv Hm]]; exists v; split; try assumption;
        apply PkgSet.mem_spec; assumption.
    - rewrite Bool.andb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.orb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.negb_true_iff; split.
      + intros E Hs; apply IHa in Hs; congruence.
      + intro Hn; destruct (satisfiesb S sigma a) eqn:E; [| reflexivity].
        exfalso; apply Hn, IHa; reflexivity.
    - reflexivity.
  Qed.

  Lemma satisfiesb_false_iff : forall S sigma f,
      satisfiesb S sigma f = false <-> ~ Satisfies S sigma f.
  Proof.
    intros S sigma f; split.
    - intros E Hs; apply satisfiesb_iff in Hs; congruence.
    - intro Hn; destruct (satisfiesb S sigma f) eqn:E; [| reflexivity].
      exfalso; apply Hn, satisfiesb_iff; exact E.
  Qed.

  Lemma satisfies_double_neg : forall S sigma f,
      ~ ~ Satisfies S sigma f -> Satisfies S sigma f.
  Proof.
    intros S sigma f Hnn; destruct (satisfiesb S sigma f) eqn:E.
    - apply satisfiesb_iff; exact E.
    - exfalso; apply Hnn, satisfiesb_false_iff; exact E.
  Qed.

  Module XOY := TripleUOT X OpOT Y.
  Module XOYF := UOTCompareFacts XOY.
  Module NF := UOTCompareFacts N.
  Module VSF := UOTCompareFacts VSet.AsUOT.
  #[local] Hint Rewrite NF.compare_eq_iff : cmp_varf.
  #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_varf.
  #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_varf.

  Module FComp <: ComparableType.
    Definition t := Formula.
    Definition rank (f : Formula) : nat :=
      match f with
      | FDep _ _ => 0 | FConj _ _ => 1 | FDisj _ _ => 2 | FNeg _ => 3
      | FVarCmp _ _ _ => 4
      end.

    Fixpoint compare (x y : Formula) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | FDep n1 vs1, FDep n2 vs2 =>
              lex (N.compare n1 n2) (VSet.AsUOT.compare vs1 vs2)
          | FConj a1 b1, FConj a2 b2 => lex (compare a1 a2) (compare b1 b2)
          | FDisj a1 b1, FDisj a2 b2 => lex (compare a1 a2) (compare b1 b2)
          | FNeg a1, FNeg a2 => compare a1 a2
          | FVarCmp x1 o1 y1, FVarCmp x2 o2 y2 =>
              XOY.compare (x1, (o1, y1)) (x2, (o2, y2))
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof.
      intros x; induction x
        as [n1 vs1 | a IHa b IHb | a IHa b IHb | a IHa | x1 o1 y1];
        intros y; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2 | x2 o2 y2]; simpl;
        try (split; intro H; congruence).
      - rewrite lex_eq_iff, NF.compare_eq_iff, VSF.compare_eq_iff;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite IHa; split; intro H; congruence.
      - rewrite XOYF.compare_eq_iff; split; intro H; congruence.
    Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof.
      intros x; induction x
        as [n1 vs1 | a IHa b IHb | a IHa b IHb | a IHa | x1 o1 y1];
        intros y; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2 | x2 o2 y2]; simpl;
        try reflexivity.
      - rewrite lex_opp, NF.compare_antisym, VSF.compare_antisym; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - apply IHa.
      - apply XOYF.compare_antisym.
    Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof.
      intros x; induction x
        as [n1 vs1 | a1 IHa b1 IHb | a1 IHa b1 IHb | a1 IHa | x1 o1 y1];
        intros y z; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2 | x2 o2 y2],
          z as [n3 vs3 | a3 b3 | a3 b3 | a3 | x3 o3 y3]; simpl; intros H1 H2;
        try congruence.
      - exact (lex_lt_trans NF.compare_eq_iff (NF.compare_lt_trans _ _ _)
                 (VSF.compare_lt_trans _ _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (IHa _ _ H1 H2).
      - exact (XOYF.compare_lt_trans _ _ _ H1 H2).
    Qed.
  End FComp.
  Module FOT := UOTFromCompare FComp.

  Module Dependees := FOT.
  Module DepElt := PairUOT Pkg Dependees.
  Module DepRel := FSetUOT DepElt.

  Record IsResolution
      (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t)
      (sigma : X.t -> Y.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_formula_closure :
        forall p, PkgSet.In p S ->
        forall f : Formula, DepRel.In (p, f) D -> Satisfies S sigma f
    ; res_version_unique : C.VersionUnique S }.

  Module Reduction.
    Module DepF := UOTCompareFacts C.Dependees.
    Module DPair := PairUOT FOT FOT.
    Module DPairF := UOTCompareFacts DPair.

    Module XF := UOTCompareFacts X.
    #[local] Hint Rewrite DepF.compare_eq_iff DPairF.compare_eq_iff
      XF.compare_eq_iff : cmp_varf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by DPairF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by XF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by DPairF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by XF.compare_lt_trans : cmp_varf.

    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Var (x : X.t)
      | Disjunct (f1 f2 : Formula)
      | NegDep (n : N.t) (vs : VSet.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, _ => Lt
        | Var _, Orig _ => Gt
        | Var x1, Var x2 => X.compare x1 x2
        | Var _, _ => Lt
        | Disjunct f1 g1, Disjunct f2 g2 => DPair.compare (f1, g1) (f2, g2)
        | Disjunct _ _, NegDep _ _ => Lt
        | Disjunct _ _, _ => Gt
        | NegDep n1 vs1, NegDep n2 vs2 =>
            C.Dependees.compare (n1, vs1) (n2, vs2)
        | NegDep _ _, _ => Gt
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_varf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_varf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_varf. Qed.
    End Name.

    Module VF := UOTCompareFacts V.
    Module YF := UOTCompareFacts Y.
    #[local] Hint Rewrite VF.compare_eq_iff YF.compare_eq_iff : cmp_varf.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by YF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by YF.compare_lt_trans : cmp_varf.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Zero
      | One
      | VarVal (y : Y.t).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, _ => Lt
        | Zero, Orig _ => Gt
        | Zero, Zero => Eq
        | Zero, _ => Lt
        | One, Orig _ => Gt
        | One, Zero => Gt
        | One, One => Eq
        | One, VarVal _ => Lt
        | VarVal y1, VarVal y2 => Y.compare y1 y2
        | VarVal _, _ => Gt
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_varf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_varf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_varf. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module T := Core NameOT VersionOT.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(n, v) := p in (Name.Orig n, Version.Orig v).

    Module SOvv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map Version.Orig vs.

    Definition zeroOne : T.VSet.t :=
      T.VSet.add Version.Zero (T.VSet.singleton Version.One).

    Module YSet := FSetUOT Y.
    Module SOyv := SetOps Y VersionOT YSet T.VSet.
    Definition cmpVersionSet (Y_x : YSet.t) (op : CmpOp) (y : Y.t) : T.VSet.t :=
      SOyv.filterMap (fun y' =>
          if opEvalY op y' y then Some (Version.VarVal y') else None)
        Y_x.

    Module SOvd := SetOps V T.DepElt VSet T.DepRel.
    (* Mutual structural pairs avoid well-founded recursion on a measure; the
       De Morgan, double-negation, and complemented-comparison cases are
       inlined. *)
    Fixpoint encodeNNF (Y_x : X.t -> YSet.t) (p : T.Pkg.t) (f : Formula) :
        T.DepRel.t :=
      match f with
      | FDep n vs => T.DepRel.singleton (p, (Name.Orig n, embedVS vs))
      | FConj a b => T.DepRel.union (encodeNNF Y_x p a) (encodeNNF Y_x p b)
      | FDisj a b =>
          T.DepRel.add (p, (Name.Disjunct a b, zeroOne))
            (T.DepRel.union
               (encodeNNF Y_x (Name.Disjunct a b, Version.Zero) a)
               (encodeNNF Y_x (Name.Disjunct a b, Version.One) b))
      | FNeg a => encodeNNFneg Y_x p a
      | FVarCmp x op y =>
          T.DepRel.singleton (p, (Name.Var x, cmpVersionSet (Y_x x) op y))
      end
    with encodeNNFneg (Y_x : X.t -> YSet.t) (p : T.Pkg.t) (f : Formula) :
        T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.add (p, (Name.NegDep n vs, T.VSet.singleton Version.One))
            (SOvd.map (fun u =>
                 ((Name.Orig n, Version.Orig u),
                  (Name.NegDep n vs, T.VSet.singleton Version.Zero)))
               vs)
      | FConj a b =>
          T.DepRel.add (p, (Name.Disjunct (FNeg a) (FNeg b), zeroOne))
            (T.DepRel.union
               (encodeNNFneg Y_x
                  (Name.Disjunct (FNeg a) (FNeg b), Version.Zero) a)
               (encodeNNFneg Y_x
                  (Name.Disjunct (FNeg a) (FNeg b), Version.One) b))
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg Y_x p a) (encodeNNFneg Y_x p b)
      | FNeg a => encodeNNF Y_x p a
      | FVarCmp x op y =>
          T.DepRel.singleton
            (p, (Name.Var x, cmpVersionSet (Y_x x) (cmpComplement op) y))
      end.

    Fixpoint witnessSet (p : T.Pkg.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b => T.PkgSet.union (witnessSet p a) (witnessSet p b)
      | FDisj a b =>
          T.PkgSet.add (Name.Disjunct a b, Version.Zero)
            (T.PkgSet.add (Name.Disjunct a b, Version.One)
               (T.PkgSet.union
                  (witnessSet (Name.Disjunct a b, Version.Zero) a)
                  (witnessSet (Name.Disjunct a b, Version.One) b)))
      | FNeg a => witnessSetNeg p a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessSetNeg (p : T.Pkg.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs =>
          T.PkgSet.add (Name.NegDep n vs, Version.Zero)
            (T.PkgSet.singleton (Name.NegDep n vs, Version.One))
      | FConj a b =>
          T.PkgSet.add (Name.Disjunct (FNeg a) (FNeg b), Version.Zero)
            (T.PkgSet.add (Name.Disjunct (FNeg a) (FNeg b), Version.One)
               (T.PkgSet.union
                  (witnessSetNeg
                     (Name.Disjunct (FNeg a) (FNeg b), Version.Zero) a)
                  (witnessSetNeg
                     (Name.Disjunct (FNeg a) (FNeg b), Version.One) b)))
      | FDisj a b =>
          T.PkgSet.union (witnessSetNeg p a) (witnessSetNeg p b)
      | FNeg a => witnessSet p a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end.

    Module SOyt := SetOps Y T.Pkg YSet T.PkgSet.
    Definition varBlock (Y_x : X.t -> YSet.t) : T.PkgSet.t :=
      List.fold_right (fun x acc =>
          T.PkgSet.union
            (SOyt.map (fun y => (Name.Var x, Version.VarVal y)) (Y_x x))
            acc)
        T.PkgSet.empty X.enum.

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.

    Module SOet := SetOps DepElt T.Pkg DepRel T.PkgSet.
    Definition reduceReal (Y_x : X.t -> YSet.t) (R : PkgSet.t) (D : DepRel.t) :
        T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg R)
        (T.PkgSet.union
           (SOet.unionMap (fun '(p, f) => witnessSet (embedPkg p) f) D)
           (varBlock Y_x)).

    Module SOed := SetOps DepElt T.DepElt DepRel T.DepRel.
    Definition reduceDeps (Y_x : X.t -> YSet.t) (D : DepRel.t) : T.DepRel.t :=
      SOed.unionMap (fun '(p, f) => encodeNNF Y_x (embedPkg p) f) D.

    Lemma mem_zeroOne : forall w,
        T.VSet.In w zeroOne <-> w = Version.Zero \/ w = Version.One.
    Proof.
      intro w; unfold zeroOne; rewrite SOvv.add_in, SOvv.singleton_in; tauto.
    Qed.

    Lemma mem_cmpVersionSet : forall Y_x op y w,
        T.VSet.In w (cmpVersionSet Y_x op y) <->
        exists y',
          YSet.In y' Y_x /\ opEvalY op y' y = true /\ w = Version.VarVal y'.
    Proof.
      intros Y_x op y w; unfold cmpVersionSet; rewrite SOyv.mem_filterMap.
      split.
      - intros [y' [Hy' Hw]]; cbn beta iota in Hw.
        destruct (opEvalY op y' y) eqn:E; [| discriminate].
        injection Hw as <-; exists y'; auto.
      - intros [y' [Hy' [HE ->]]]; exists y'; split; [exact Hy' | cbn beta iota].
        rewrite HE; reflexivity.
    Qed.

    Lemma mem_varBlock : forall Y_x (q : T.Pkg.t),
        T.PkgSet.In q (varBlock Y_x) <->
        exists x y, YSet.In y (Y_x x) /\ q = (Name.Var x, Version.VarVal y).
    Proof.
      intros Y_x q; unfold varBlock.
      assert (Haux : forall l,
          T.PkgSet.In q
            (List.fold_right (fun x acc =>
                 T.PkgSet.union
                   (SOyt.map (fun y => (Name.Var x, Version.VarVal y))
                      (Y_x x))
                   acc)
               T.PkgSet.empty l) <->
          exists x y, List.In x l /\ YSet.In y (Y_x x) /\
                      q = (Name.Var x, Version.VarVal y)).
      { induction l as [| x l IH]; simpl.
        - split; [intro H; exfalso; exact (SOpt.empty_in _ H)
                 | intros [x [y [[] _]]]].
        - rewrite T.PkgSet.union_spec, SOyt.mem_map, IH; split.
          + intros [[y [Hy Hq]] | [x' [y [Hl [Hy Hq]]]]].
            * exists x, y; split; [left; reflexivity | split; assumption].
            * exists x', y; split; [right; exact Hl | split; assumption].
          + intros [x' [y [[-> | Hl] [Hy Hq]]]].
            * left; exists y; split; [exact Hy | exact Hq].
            * right; exists x', y; split; [exact Hl | split; assumption]. }
      rewrite Haux; split.
      - intros [x [y [_ [Hy Hq]]]]; exists x, y; split; assumption.
      - intros [x [y [Hy Hq]]]; exists x, y;
          split; [apply X.enum_complete | split; assumption].
    Qed.

    Lemma mem_reduceReal : forall Y_x R D (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal Y_x R D) <->
        (exists p, PkgSet.In p R /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\
                     T.PkgSet.In y (witnessSet (embedPkg p) f)) \/
        (exists x y',
            YSet.In y' (Y_x x) /\ y = (Name.Var x, Version.VarVal y')).
    Proof.
      intros Y_x R D y; unfold reduceReal.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap,
        mem_varBlock.
      split.
      - intros [H | [[[q g] [He Hy]] | H]].
        + left; exact H.
        + right; left; exists q, g; split; [exact He | exact Hy].
        + right; right; exact H.
      - intros [H | [[q [g [Hd Hy]]] | H]].
        + left; exact H.
        + right; left; exists (q, g); split; [exact Hd | exact Hy].
        + right; right; exact H.
    Qed.

    Lemma mem_reduceDeps : forall Y_x D (d : T.DepElt.t),
        T.DepRel.In d (reduceDeps Y_x D) <->
        exists p f, DepRel.In (p, f) D /\
                    T.DepRel.In d (encodeNNF Y_x (embedPkg p) f).
    Proof.
      intros Y_x D d; unfold reduceDeps; rewrite SOed.mem_unionMap.
      split.
      - intros [[q g] [He Hd]]; exists q, g; split; [exact He | exact Hd].
      - intros [q [g [Hq Hd]]]; exists (q, g); split; [exact Hq | exact Hd].
    Qed.

    Definition tryInvPkg (p' : T.Pkg.t) : option Pkg.t :=
      match p' with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (p' : T.Pkg.t) (p : Pkg.t),
        tryInvPkg p' = Some p -> embedPkg p = p'.
    Proof.
      intros [n' v'] p H; destruct n', v'; cbn [tryInvPkg] in H;
        try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
    Lemma embedPkg_injective : forall p q : Pkg.t,
        embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOtp.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.
    Definition variableFormulaResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_variableFormulaResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (variableFormulaResolution S) <->
        T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold variableFormulaResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Module SOty := SetOps T.Pkg Y T.PkgSet YSet.
    (* min_elt of the assigned-value candidates keeps the selector
       deterministic and computable; the domain's min is the fallback and y0
       the (unreachable under a nonempty domain) final case. *)
    Definition assignCand (S : T.PkgSet.t) (x : X.t) : YSet.t :=
      SOty.filterMap (fun p' =>
          match p' with
          | (Name.Var x', Version.VarVal y) =>
              if X.eq_dec x' x then Some y else None
          | _ => None
          end)
        S.

    Definition extractAssignment (y0 : Y.t) (Y_x : X.t -> YSet.t)
        (S : T.PkgSet.t) (x : X.t) : Y.t :=
      match YSet.min_elt (assignCand S x) with
      | Some y => y
      | None =>
          match YSet.min_elt (Y_x x) with
          | Some y => y
          | None => y0
          end
      end.

    Lemma witnessSet_name_classify_aux : forall f : Formula,
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSet p f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)) /\
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetNeg p f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)).
    Proof.
      induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros p n v H; simpl in H.
      - exfalso; exact (SOpt.empty_in _ H).
      - rewrite SOpt.add_in, SOpt.singleton_in in H.
        destruct H as [H | H]; injection H as -> _; left; eauto.
      - apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - rewrite !SOpt.add_in in H.
        destruct H as [H | [H | H]]; try (injection H as -> _; right; eauto).
        apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - rewrite !SOpt.add_in in H.
        destruct H as [H | [H | H]]; try (injection H as -> _; right; eauto).
        apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa _ _ _ H).
      - exact (proj1 IHa _ _ _ H).
      - exfalso; exact (SOpt.empty_in _ H).
      - exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSet_not_orig : forall (p : T.Pkg.t) (f : Formula) n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSet p f).
    Proof.
      intros p f n v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma witnessSet_not_var : forall (p : T.Pkg.t) (f : Formula) x v,
        ~ T.PkgSet.In (Name.Var x, v) (witnessSet p f).
    Proof.
      intros p f x v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall Y_x (p : Pkg.t) R D,
        T.PkgSet.In (embedPkg p) (reduceReal Y_x R D) -> PkgSet.In p R.
    Proof.
      intros Y_x [pn pv] R D H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [[q [g [_ Hy]]] | [x [y' [_ Hy]]]]].
      - apply embedPkg_injective in Hq as ->; exact HqR.
      - exfalso; exact (witnessSet_not_orig _ _ _ _ Hy).
      - unfold embedPkg in Hy; discriminate.
    Qed.

    Lemma mem_assignCand : forall S x y,
        YSet.In y (assignCand S x) <->
        T.PkgSet.In (Name.Var x, Version.VarVal y) S.
    Proof.
      intros S x y; unfold assignCand; rewrite SOty.mem_filterMap.
      split.
      - intros [[[n' | x' | f1 f2 | n' vs'] [v' | | | y']] [Hp' Hin]];
          cbn beta iota in Hin; try discriminate.
        destruct (X.eq_dec x' x) as [-> | NE]; [| discriminate].
        injection Hin as <-; exact Hp'.
      - intro H; exists (Name.Var x, Version.VarVal y);
          split; [exact H | cbn beta iota].
        destruct (X.eq_dec x x) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
    Qed.

    Lemma extractAssignment_var_det : forall y0 Y_x (S : T.PkgSet.t) x y,
        T.VersionUnique S ->
        T.PkgSet.In (Name.Var x, Version.VarVal y) S ->
        extractAssignment y0 Y_x S x = y.
    Proof.
      intros y0 Y_x S x y Huniq Hin; unfold extractAssignment.
      destruct (YSet.min_elt (assignCand S x)) as [y' |] eqn:E.
      - apply YSet.min_elt_spec1, mem_assignCand in E.
        assert (Ev := Huniq _ _ _ E Hin); injection Ev as ->; reflexivity.
      - exfalso; apply YSet.min_elt_spec3 in E.
        exact (E y (proj2 (mem_assignCand S x y) Hin)).
    Qed.

    Lemma extractAssignment_mem : forall y0 Y_x R D (S : T.PkgSet.t),
        (forall x, exists y, YSet.In y (Y_x x)) ->
        T.PkgSet.Subset S (reduceReal Y_x R D) ->
        forall x, YSet.In (extractAssignment y0 Y_x S x) (Y_x x).
    Proof.
      intros y0 Y_x R D S Hne Hsub x; unfold extractAssignment.
      destruct (YSet.min_elt (assignCand S x)) as [y' |] eqn:E.
      - apply YSet.min_elt_spec1, mem_assignCand in E.
        apply Hsub, mem_reduceReal in E.
        destruct E as [[q [_ Hq]] | [[q [g [_ Hy]]] | [x' [y'' [Hy'' Hq]]]]].
        + destruct q as [qn qv]; unfold embedPkg in Hq; discriminate.
        + exfalso; exact (witnessSet_not_var _ _ _ _ Hy).
        + injection Hq as Ex Ey; subst; exact Hy''.
      - destruct (YSet.min_elt (Y_x x)) as [y1 |] eqn:E2.
        + apply YSet.min_elt_spec1 in E2; exact E2.
        + exfalso; apply YSet.min_elt_spec3 in E2.
          destruct (Hne x) as [y1 Hy1]; exact (E2 y1 Hy1).
    Qed.

    Lemma encodeNNF_satisfies : forall (R : T.PkgSet.t) (D : T.DepRel.t)
                                    (r : T.Pkg.t) (S : T.PkgSet.t),
        T.IsResolution R D r S ->
        forall y0 Y_x,
          (forall x, exists y, YSet.In y (Y_x x)) ->
          forall (q : T.Pkg.t) (f : Formula),
            (forall d, T.DepRel.In d (encodeNNF Y_x q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S ->
            Satisfies (variableFormulaResolution S)
              (extractAssignment y0 Y_x S) f.
    Proof.
      intros R D r S Hres y0 Y_x Hne;
        destruct Hres as [Hsub Hroot Hdep Huniq].
      cut (forall f : Formula,
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNF Y_x q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S ->
            Satisfies (variableFormulaResolution S)
              (extractAssignment y0 Y_x S) f) /\
        (forall q : T.Pkg.t,
            (forall d,
                T.DepRel.In d (encodeNNFneg Y_x q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S ->
            ~ Satisfies (variableFormulaResolution S)
                (extractAssignment y0 Y_x S) f)).
      { intros H q f; exact (proj1 (H f) q). }
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros q Henc HqS; simpl.
      - assert (Hd : T.DepRel.In (q, (Name.Orig n, embedVS vs)) D).
        { apply Henc; simpl; apply SOed.singleton_in; reflexivity. }
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        unfold embedVS in Hw; apply SOvv.mem_map in Hw;
          destruct Hw as [v [Hv ->]].
        exists v; split; [exact Hv |].
        apply mem_variableFormulaResolution; exact HwS.
      - assert
          (Hd1 : T.DepRel.In
                   (q, (Name.NegDep n vs, T.VSet.singleton Version.One)) D).
        { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
        destruct (Hdep q HqS _ _ Hd1) as [w [Hw HwS]].
        apply SOvv.singleton_in in Hw; subst w.
        intros [v [Hv HvS]].
        apply mem_variableFormulaResolution in HvS.
        assert (Hd2 : T.DepRel.In ((Name.Orig n, Version.Orig v),
                        (Name.NegDep n vs, T.VSet.singleton Version.Zero)) D).
        { apply Henc; simpl; apply SOed.add_in; right.
          apply SOvd.mem_map; exists v; split; [exact Hv | reflexivity]. }
        destruct (Hdep _ HvS _ _ Hd2) as [w2 [Hw2 Hw2S]].
        apply SOvv.singleton_in in Hw2; subst w2.
        assert (E := Huniq _ _ _ HwS Hw2S); discriminate.
      - split.
        + apply (proj1 IHa q); [| exact HqS].
          intros d Hd; apply Henc; simpl;
            apply T.DepRel.union_spec; left; exact Hd.
        + apply (proj1 IHb q); [| exact HqS].
          intros d Hd; apply Henc; simpl;
            apply T.DepRel.union_spec; right; exact Hd.
      - assert (Hd : T.DepRel.In
          (q, (Name.Disjunct (FNeg a) (FNeg b), zeroOne)) D).
        { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        apply mem_zeroOne in Hw.
        intros [HsatA HsatB].
        destruct Hw as [-> | ->].
        + refine (proj2 IHa (Name.Disjunct (FNeg a) (FNeg b), Version.Zero)
                    _ HwS HsatA).
          intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
            apply T.DepRel.union_spec; left; exact Hd'.
        + refine (proj2 IHb (Name.Disjunct (FNeg a) (FNeg b), Version.One)
                    _ HwS HsatB).
          intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
            apply T.DepRel.union_spec; right; exact Hd'.
      - assert (Hd : T.DepRel.In (q, (Name.Disjunct a b, zeroOne)) D).
        { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        apply mem_zeroOne in Hw; destruct Hw as [-> | ->].
        + left;
            apply (proj1 IHa (Name.Disjunct a b, Version.Zero)); [| exact HwS].
          intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
            apply T.DepRel.union_spec; left; exact Hd'.
        + right;
            apply (proj1 IHb (Name.Disjunct a b, Version.One)); [| exact HwS].
          intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
            apply T.DepRel.union_spec; right; exact Hd'.
      - intros [HsatA | HsatB].
        + refine (proj2 IHa q _ HqS HsatA).
          intros d Hd'; apply Henc; simpl;
            apply T.DepRel.union_spec; left; exact Hd'.
        + refine (proj2 IHb q _ HqS HsatB).
          intros d Hd'; apply Henc; simpl;
            apply T.DepRel.union_spec; right; exact Hd'.
      - exact (proj2 IHa q Henc HqS).
      - intro Hn; exact (Hn (proj1 IHa q Henc HqS)).
      - assert (Hd : T.DepRel.In
                       (q, (Name.Var x, cmpVersionSet (Y_x x) op y)) D).
        { apply Henc; simpl; apply SOed.singleton_in; reflexivity. }
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        apply mem_cmpVersionSet in Hw; destruct Hw as [y' [Hy' [HE ->]]].
        rewrite (extractAssignment_var_det y0 Y_x S x y' Huniq HwS); exact HE.
      - assert (Hd : T.DepRel.In
            (q, (Name.Var x, cmpVersionSet (Y_x x) (cmpComplement op) y)) D).
        { apply Henc; simpl; apply SOed.singleton_in; reflexivity. }
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        apply mem_cmpVersionSet in Hw; destruct Hw as [y' [Hy' [HE ->]]].
        rewrite opEvalY_complement in HE; apply Bool.negb_true_iff in HE.
        rewrite (extractAssignment_var_det y0 Y_x S x y' Huniq HwS).
        intro HC; congruence.
    Qed.

    Theorem variable_formula_soundness :
      forall (y0 : Y.t) (Y_x : X.t -> YSet.t),
        (forall x, exists y, YSet.In y (Y_x x)) ->
        forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : T.PkgSet.t),
          T.IsResolution (reduceReal Y_x R D) (reduceDeps Y_x D)
            (embedPkg r) S ->
          IsResolution R D r (variableFormulaResolution S)
            (extractAssignment y0 Y_x S) /\
          forall x, YSet.In (extractAssignment y0 Y_x S x) (Y_x x).
    Proof.
      intros y0 Y_x Hne R D r S Hres.
      assert (H := Hres); destruct H as [Hsub Hroot Hdep Huniq].
      split.
      - constructor.
        + intros p Hp; apply mem_variableFormulaResolution in Hp.
          exact (embedPkg_mem_reduceReal Y_x p R D (Hsub _ Hp)).
        + apply mem_variableFormulaResolution; exact Hroot.
        + intros p Hp f Hdf.
          apply mem_variableFormulaResolution in Hp.
          apply (encodeNNF_satisfies _ _ _ _ Hres y0 Y_x Hne (embedPkg p) f);
            [| exact Hp].
          intros d Hd; apply mem_reduceDeps; exists p, f;
            split; [exact Hdf | exact Hd].
        + intros n v v' Hv Hv'.
          apply mem_variableFormulaResolution in Hv, Hv'.
          unfold embedPkg in Hv, Hv'; simpl in Hv, Hv'.
          assert (E := Huniq _ _ _ Hv Hv').
          injection E as E; exact E.
      - exact (extractAssignment_mem y0 Y_x R D S Hne Hsub).
    Qed.

    Definition depTakenb (S : PkgSet.t) (n : N.t) (vs : VSet.t) : bool :=
      VSet.exists_ (fun u => PkgSet.mem (n, u) S) vs.

    Lemma depTakenb_iff : forall S n vs,
        depTakenb S n vs = true <->
        exists u, VSet.In u vs /\ PkgSet.In (n, u) S.
    Proof.
      intros S n vs; unfold depTakenb.
      rewrite VSet.exists_spec'.
      split; intros [u [Hu Hm]]; exists u; split; try assumption;
        apply PkgSet.mem_spec; assumption.
    Qed.

    Fixpoint witnessSetUntaken (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetUntaken S a) (witnessSetUntaken S b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetUntaken S a) (witnessSetUntaken S b)
      | FNeg a => witnessSetUntakenNeg S a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessSetUntakenNeg (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs =>
          if depTakenb S n vs
          then T.PkgSet.singleton (Name.NegDep n vs, Version.Zero)
          else T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetUntakenNeg S a) (witnessSetUntakenNeg S b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetUntakenNeg S a) (witnessSetUntakenNeg S b)
      | FNeg a => witnessSetUntaken S a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end.

    Fixpoint witnessSetTaken (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
        T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetTaken S sigma a) (witnessSetTaken S sigma b)
      | FDisj a b =>
          if satisfiesb S sigma a
          then T.PkgSet.add (Name.Disjunct a b, Version.Zero)
                 (T.PkgSet.union (witnessSetTaken S sigma a)
                    (witnessSetUntaken S b))
          else T.PkgSet.add (Name.Disjunct a b, Version.One)
                 (T.PkgSet.union (witnessSetUntaken S a)
                    (witnessSetTaken S sigma b))
      | FNeg a => witnessSetTakenNeg S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessSetTakenNeg (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
        T.PkgSet.t :=
      match f with
      | FDep n vs => T.PkgSet.singleton (Name.NegDep n vs, Version.One)
      | FConj a b =>
          if negb (satisfiesb S sigma a)
          then T.PkgSet.add (Name.Disjunct (FNeg a) (FNeg b), Version.Zero)
                 (T.PkgSet.union (witnessSetTakenNeg S sigma a)
                    (witnessSetUntakenNeg S b))
          else T.PkgSet.add (Name.Disjunct (FNeg a) (FNeg b), Version.One)
                 (T.PkgSet.union (witnessSetUntakenNeg S a)
                    (witnessSetTakenNeg S sigma b))
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S sigma a)
            (witnessSetTakenNeg S sigma b)
      | FNeg a => witnessSetTaken S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end.

    Definition sigmaBlock (sigma : X.t -> Y.t) : T.PkgSet.t :=
      List.fold_right (fun x acc =>
          T.PkgSet.add (Name.Var x, Version.VarVal (sigma x)) acc)
        T.PkgSet.empty X.enum.

    Definition coreResolution (S : PkgSet.t) (D : DepRel.t)
        (sigma : X.t -> Y.t) : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg S)
        (T.PkgSet.union
           (SOet.unionMap (fun '(p, f) =>
                if PkgSet.mem p S
                then witnessSetTaken S sigma f
                else witnessSetUntaken S f)
              D)
           (sigmaBlock sigma)).

    Lemma witnessSetUntaken_subset_witnessSet_aux : forall S f,
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetUntaken S f) (witnessSet p f)) /\
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetUntakenNeg S f) (witnessSetNeg p f)).
    Proof.
      intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros p z; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; subst z;
            apply SOpt.add_in; left; reflexivity.
        + exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
          destruct H as [H | H];
          [left; exact (proj1 IHa p _ H) | right; exact (proj1 IHb p _ H)].
      - intro H; apply T.PkgSet.union_spec in H;
          apply SOpt.add_in; right; apply SOpt.add_in; right;
          apply T.PkgSet.union_spec; destruct H as [H | H];
          [left; exact (proj2 IHa _ _ H) | right; exact (proj2 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H;
          apply SOpt.add_in; right; apply SOpt.add_in; right;
          apply T.PkgSet.union_spec; destruct H as [H | H];
          [left; exact (proj1 IHa _ _ H) | right; exact (proj1 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
          destruct H as [H | H];
          [left; exact (proj2 IHa p _ H) | right; exact (proj2 IHb p _ H)].
      - exact (proj2 IHa p z).
      - exact (proj1 IHa p z).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetUntaken_subset_witnessSet : forall S (p : T.Pkg.t) f,
        T.PkgSet.Subset (witnessSetUntaken S f) (witnessSet p f).
    Proof.
      intros S p f;
        exact (proj1 (witnessSetUntaken_subset_witnessSet_aux S f) p).
    Qed.

    Lemma witnessSetTaken_subset_witnessSet_aux : forall S sigma f,
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTaken S sigma f) (witnessSet p f)) /\
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTakenNeg S sigma f)
              (witnessSetNeg p f)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros p z; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; subst z;
          apply SOpt.add_in; right; apply SOpt.singleton_in; reflexivity.
      - intro H; apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
          destruct H as [H | H];
          [left; exact (proj1 IHa p _ H) | right; exact (proj1 IHb p _ H)].
      - destruct (satisfiesb S sigma a); intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + subst z; apply SOpt.add_in; right; apply SOpt.add_in; left;
            reflexivity.
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; left;
            exact (proj2 (witnessSetUntaken_subset_witnessSet_aux S a)
                     _ _ H).
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; right; exact (proj2 IHb _ _ H).
        + subst z; apply SOpt.add_in; left; reflexivity.
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; left; exact (proj2 IHa _ _ H).
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; right;
            exact (proj2 (witnessSetUntaken_subset_witnessSet_aux S b)
                     _ _ H).
      - destruct (satisfiesb S sigma a); intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + subst z; apply SOpt.add_in; left; reflexivity.
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; left; exact (proj1 IHa _ _ H).
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; right;
            exact (proj1 (witnessSetUntaken_subset_witnessSet_aux S b)
                     _ _ H).
        + subst z; apply SOpt.add_in; right; apply SOpt.add_in; left;
            reflexivity.
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; left;
            exact (proj1 (witnessSetUntaken_subset_witnessSet_aux S a)
                     _ _ H).
        + apply SOpt.add_in; right; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; right; exact (proj1 IHb _ _ H).
      - intro H; apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
          destruct H as [H | H];
          [left; exact (proj2 IHa p _ H) | right; exact (proj2 IHb p _ H)].
      - exact (proj2 IHa p z).
      - exact (proj1 IHa p z).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_subset_witnessSet : forall S sigma (p : T.Pkg.t) f,
        T.PkgSet.Subset (witnessSetTaken S sigma f) (witnessSet p f).
    Proof.
      intros S sigma p f;
        exact (proj1 (witnessSetTaken_subset_witnessSet_aux S sigma f) p).
    Qed.

    Lemma witnessSetUntaken_negDep_det_aux : forall S f,
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
            v = Version.Zero) /\
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntakenNeg S f) ->
            v = Version.Zero).
    Proof.
      intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros n vs v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; congruence.
        + exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa n vs v).
      - exact (proj1 IHa n vs v).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetUntaken_negDep_det : forall S f n vs v,
        T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
        v = Version.Zero.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_negDep_det_aux S f)).
    Qed.

    Lemma witnessSetUntaken_negDep_exists_aux : forall S f,
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
            exists u, VSet.In u vs /\ PkgSet.In (n, u) S) /\
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntakenNeg S f) ->
            exists u, VSet.In u vs /\ PkgSet.In (n, u) S).
    Proof.
      intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros n vs v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws) eqn:E; intro H.
        + apply SOpt.singleton_in in H; injection H as -> -> _.
          apply depTakenb_iff; exact E.
        + exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa n vs v).
      - exact (proj1 IHa n vs v).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetUntaken_negDep_exists : forall S f n vs v,
        T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
        exists u, VSet.In u vs /\ PkgSet.In (n, u) S.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_negDep_exists_aux S f)).
    Qed.

    Lemma witnessSetUntaken_disjunct_det_aux : forall S f,
        (forall f1 f2 v,
            T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetUntaken S f) ->
            False) /\
        (forall f1 f2 v,
            T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetUntakenNeg S f) ->
            False).
    Proof.
      intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros f1 f2 v; simpl.
      - intro H; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; congruence.
        + exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa f1 f2 v).
      - exact (proj1 IHa f1 f2 v).
      - intro H; exact (SOpt.empty_in _ H).
      - intro H; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetUntaken_disjunct_det : forall S f f1 f2 v,
        T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetUntaken S f) -> False.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_disjunct_det_aux S f)).
    Qed.

    Lemma witnessSetTaken_disjunct_det_aux : forall S sigma f,
        (forall f1 f2 v,
            T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetTaken S sigma f) ->
            v =
              (if satisfiesb S sigma f1 then Version.Zero else Version.One)) /\
        (forall f1 f2 v,
            T.PkgSet.In (Name.Disjunct f1 f2, v)
              (witnessSetTakenNeg S sigma f) ->
            v = (if satisfiesb S sigma f1 then Version.Zero else Version.One)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros f1 f2 v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; congruence.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
      - destruct (satisfiesb S sigma a) eqn:Ea; intro H;
          apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + injection H as -> -> ->; simpl; rewrite Ea; reflexivity.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S a) _ _ _ H).
        + exact (proj2 IHb _ _ _ H).
        + injection H as -> -> ->; simpl; rewrite Ea; reflexivity.
        + exact (proj2 IHa _ _ _ H).
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S b) _ _ _ H).
      - destruct (satisfiesb S sigma a) eqn:Ea; intro H;
          apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + injection H as -> -> ->; rewrite Ea; reflexivity.
        + exact (proj1 IHa _ _ _ H).
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + injection H as -> -> ->; rewrite Ea; reflexivity.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + exact (proj1 IHb _ _ _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
      - exact (proj2 IHa f1 f2 v).
      - exact (proj1 IHa f1 f2 v).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_disjunct_det : forall S sigma f f1 f2 v,
        T.PkgSet.In (Name.Disjunct f1 f2, v) (witnessSetTaken S sigma f) ->
        v = (if satisfiesb S sigma f1 then Version.Zero else Version.One).
    Proof.
      intros S sigma f;
        exact (proj1 (witnessSetTaken_disjunct_det_aux S sigma f)).
    Qed.

    Lemma witnessSetTaken_negDep_det_aux : forall S sigma f,
        (Satisfies S sigma f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTaken S sigma f) ->
           v = (if depTakenb S n vs then Version.Zero else Version.One)) /\
        (~ Satisfies S sigma f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTakenNeg S sigma f) ->
           v = (if depTakenb S n vs then Version.Zero else Version.One)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros Hyp n vs v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; injection H as -> -> ->.
        destruct (depTakenb S m ws) eqn:E; [| reflexivity].
        exfalso; apply Hyp, depTakenb_iff; exact E.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa (proj1 Hyp) _ _ _ H)
          | exact (proj1 IHb (proj2 Hyp) _ _ _ H)].
      - destruct (satisfiesb S sigma a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [congruence
           | apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + assert (E2 : depTakenb S n vs = true).
          { apply depTakenb_iff;
              exact (proj2 (witnessSetUntaken_negDep_exists_aux S a) _ _ _ H). }
          rewrite E2;
            exact (proj2 (witnessSetUntaken_negDep_det_aux S a) _ _ _ H).
        + apply (proj2 IHb); [| exact H].
          intro Hb'; apply Hyp; split;
            [apply satisfiesb_iff; exact Ea | exact Hb'].
        + apply (proj2 IHa); [| exact H].
          apply satisfiesb_false_iff; exact Ea.
        + assert (E2 : depTakenb S n vs = true).
          { apply depTakenb_iff;
              exact (proj2 (witnessSetUntaken_negDep_exists_aux S b) _ _ _ H). }
          rewrite E2;
            exact (proj2 (witnessSetUntaken_negDep_det_aux S b) _ _ _ H).
      - destruct (satisfiesb S sigma a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [congruence
           | apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + apply (proj1 IHa); [apply satisfiesb_iff; exact Ea | exact H].
        + assert (E2 : depTakenb S n vs = true).
          { apply depTakenb_iff;
              exact (proj1 (witnessSetUntaken_negDep_exists_aux S b) _ _ _ H). }
          rewrite E2;
            exact (proj1 (witnessSetUntaken_negDep_det_aux S b) _ _ _ H).
        + assert (E2 : depTakenb S n vs = true).
          { apply depTakenb_iff;
              exact (proj1 (witnessSetUntaken_negDep_exists_aux S a) _ _ _ H). }
          rewrite E2;
            exact (proj1 (witnessSetUntaken_negDep_det_aux S a) _ _ _ H).
        + apply (proj1 IHb); [| exact H].
          destruct Hyp as [Ha | Hb]; [| exact Hb].
          exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [apply (proj2 IHa); [intro Ha; exact (Hyp (or_introl Ha)) | exact H]
          | apply (proj2 IHb);
              [intro Hb; exact (Hyp (or_intror Hb)) | exact H]].
      - exact (proj2 IHa Hyp n vs v).
      - exact (proj1 IHa (satisfies_double_neg S sigma a Hyp) n vs v).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_negDep_det : forall S sigma f,
        Satisfies S sigma f ->
        forall n vs v,
          T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTaken S sigma f) ->
          v = (if depTakenb S n vs then Version.Zero else Version.One).
    Proof.
      intros S sigma f;
        exact (proj1 (witnessSetTaken_negDep_det_aux S sigma f)).
    Qed.

    Lemma witnessSetUntaken_name_classify_aux : forall S f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetUntaken S f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetUntakenNeg S f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)).
    Proof.
      intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros n v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; injection H as -> _.
          left; exists m, ws; reflexivity.
        + exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ H) | exact (proj1 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ H) | exact (proj2 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ H) | exact (proj1 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ H) | exact (proj2 IHb _ _ H)].
      - exact (proj2 IHa n v).
      - exact (proj1 IHa n v).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetUntaken_name_classify :
      forall S f (n : Name.t) (v : Version.t),
        T.PkgSet.In (n, v) (witnessSetUntaken S f) ->
        (exists n' vs, n = Name.NegDep n' vs) \/
        (exists f1 f2, n = Name.Disjunct f1 f2).
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_name_classify_aux S f)).
    Qed.

    Lemma witnessSetTaken_name_classify_aux : forall S sigma f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTaken S sigma f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTakenNeg S sigma f) ->
            (exists n' vs, n = Name.NegDep n' vs) \/
            (exists f1 f2, n = Name.Disjunct f1 f2)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros n v; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; injection H as -> _.
        left; exists m, ws; reflexivity.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ H) | exact (proj1 IHb _ _ H)].
      - destruct (satisfiesb S sigma a); intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [injection H as -> _; right; eauto
           | apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + exact (proj2 (witnessSetUntaken_name_classify_aux S a) _ _ H).
        + exact (proj2 IHb _ _ H).
        + exact (proj2 IHa _ _ H).
        + exact (proj2 (witnessSetUntaken_name_classify_aux S b) _ _ H).
      - destruct (satisfiesb S sigma a); intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [injection H as -> _; right; eauto
           | apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + exact (proj1 IHa _ _ H).
        + exact (proj1 (witnessSetUntaken_name_classify_aux S b) _ _ H).
        + exact (proj1 (witnessSetUntaken_name_classify_aux S a) _ _ H).
        + exact (proj1 IHb _ _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ H) | exact (proj2 IHb _ _ H)].
      - exact (proj2 IHa n v).
      - exact (proj1 IHa n v).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_name_classify :
      forall S sigma f (n : Name.t) (v : Version.t),
        T.PkgSet.In (n, v) (witnessSetTaken S sigma f) ->
        (exists n' vs, n = Name.NegDep n' vs) \/
        (exists f1 f2, n = Name.Disjunct f1 f2).
    Proof.
      intros S sigma f;
        exact (proj1 (witnessSetTaken_name_classify_aux S sigma f)).
    Qed.

    Lemma witnessSetUntaken_not_orig : forall S f n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSetUntaken S f).
    Proof.
      intros S f n v H.
      destruct (witnessSetUntaken_name_classify S f _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma witnessSetTaken_not_orig : forall S sigma f n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSetTaken S sigma f).
    Proof.
      intros S sigma f n v H.
      destruct (witnessSetTaken_name_classify S sigma f _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma witnessSetUntaken_not_var : forall S f x v,
        ~ T.PkgSet.In (Name.Var x, v) (witnessSetUntaken S f).
    Proof.
      intros S f x v H.
      destruct (witnessSetUntaken_name_classify S f _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma witnessSetTaken_not_var : forall S sigma f x v,
        ~ T.PkgSet.In (Name.Var x, v) (witnessSetTaken S sigma f).
    Proof.
      intros S sigma f x v H.
      destruct (witnessSetTaken_name_classify S sigma f _ _ H)
        as [[n' [vs E]] | [f1 [f2 E]]]; discriminate.
    Qed.

    Lemma mem_sigmaBlock : forall sigma (q : T.Pkg.t),
        T.PkgSet.In q (sigmaBlock sigma) <->
        exists x, q = (Name.Var x, Version.VarVal (sigma x)).
    Proof.
      intros sigma q; unfold sigmaBlock.
      assert (Haux : forall l,
          T.PkgSet.In q
            (List.fold_right (fun x acc =>
                 T.PkgSet.add (Name.Var x, Version.VarVal (sigma x)) acc)
               T.PkgSet.empty l) <->
          exists x, List.In x l /\ q = (Name.Var x, Version.VarVal (sigma x))).
      { induction l as [| x l IH]; simpl.
        - split; [intro H; exfalso; exact (SOpt.empty_in _ H)
                 | intros [x [[] _]]].
        - rewrite SOpt.add_in, IH; split.
          + intros [-> | [x' [Hl Hq]]].
            * exists x; split; [left; reflexivity | reflexivity].
            * exists x'; split; [right; exact Hl | exact Hq].
          + intros [x' [[-> | Hl] Hq]];
              [left; exact Hq | right; exists x'; split; assumption]. }
      rewrite Haux; split.
      - intros [x [_ Hq]]; exists x; exact Hq.
      - intros [x Hq]; exists x; split; [apply X.enum_complete | exact Hq].
    Qed.

    Lemma mem_coreResolution : forall S D sigma (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution S D sigma) <->
        (exists p, PkgSet.In p S /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\
           T.PkgSet.In y (if PkgSet.mem p S
                          then witnessSetTaken S sigma f
                          else witnessSetUntaken S f)) \/
        (exists x, y = (Name.Var x, Version.VarVal (sigma x))).
    Proof.
      intros S D sigma y; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap,
        mem_sigmaBlock.
      split.
      - intros [H | [[[q g] [He Hy]] | H]].
        + left; exact H.
        + right; left; exists q, g; split; [exact He | exact Hy].
        + right; right; exact H.
      - intros [H | [[q [g [Hd Hy]]] | H]].
        + left; exact H.
        + right; left; exists (q, g); split; [exact Hd | exact Hy].
        + right; right; exact H.
    Qed.

    Lemma witnessSet_subset_coreResolution : forall S D sigma p f,
        DepRel.In (p, f) D ->
        T.PkgSet.Subset
          (if PkgSet.mem p S
           then witnessSetTaken S sigma f
           else witnessSetUntaken S f)
          (coreResolution S D sigma).
    Proof.
      intros S D sigma p f Hd y Hy; apply mem_coreResolution; right; left.
      exists p, f; split; [exact Hd | exact Hy].
    Qed.

    Lemma witnessSetTaken_disj_zero_mono_aux : forall S sigma f,
        (forall f1 f2,
            T.PkgSet.In (Name.Disjunct f1 f2, Version.Zero)
              (witnessSetTaken S sigma f) ->
            Satisfies S sigma f1 /\
            T.PkgSet.Subset (witnessSetTaken S sigma f1)
              (witnessSetTaken S sigma f) /\
            T.PkgSet.Subset (witnessSetUntaken S f2)
              (witnessSetTaken S sigma f)) /\
        (forall f1 f2,
            T.PkgSet.In (Name.Disjunct f1 f2, Version.Zero)
              (witnessSetTakenNeg S sigma f) ->
            Satisfies S sigma f1 /\
            T.PkgSet.Subset (witnessSetTaken S sigma f1)
              (witnessSetTakenNeg S sigma f) /\
            T.PkgSet.Subset (witnessSetUntaken S f2)
              (witnessSetTakenNeg S sigma f)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros f1 f2; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; congruence.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
        + destruct (proj1 IHa f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; left; [apply H1 | apply H2]; exact Hy.
        + destruct (proj1 IHb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; right; [apply H1 | apply H2]; exact Hy.
      - destruct (satisfiesb S sigma a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + congruence.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S a) _ _ _ H).
        + destruct (proj2 IHb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; right;
            [apply H1 | apply H2]; exact Hy.
        + injection H as -> ->.
          split; [apply satisfiesb_false_iff; exact Ea |].
          split; intros y Hy; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; [left | right]; exact Hy.
        + destruct (proj2 IHa f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; left;
            [apply H1 | apply H2]; exact Hy.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S b) _ _ _ H).
      - destruct (satisfiesb S sigma a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + injection H as -> ->.
          split; [apply satisfiesb_iff; exact Ea |].
          split; intros y Hy; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; [left | right]; exact Hy.
        + destruct (proj1 IHa f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; left;
            [apply H1 | apply H2]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + congruence.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + destruct (proj1 IHb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; right;
            [apply H1 | apply H2]; exact Hy.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
        + destruct (proj2 IHa f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; left; [apply H1 | apply H2]; exact Hy.
        + destruct (proj2 IHb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; right; [apply H1 | apply H2]; exact Hy.
      - exact (proj2 IHa f1 f2).
      - exact (proj1 IHa f1 f2).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_disj_one_mono_aux : forall S sigma f,
        (Satisfies S sigma f ->
         forall f1 f2,
           T.PkgSet.In (Name.Disjunct f1 f2, Version.One)
             (witnessSetTaken S sigma f) ->
           Satisfies S sigma f2 /\
           T.PkgSet.Subset (witnessSetUntaken S f1)
             (witnessSetTaken S sigma f) /\
           T.PkgSet.Subset (witnessSetTaken S sigma f2)
             (witnessSetTaken S sigma f)) /\
        (~ Satisfies S sigma f ->
         forall f1 f2,
           T.PkgSet.In (Name.Disjunct f1 f2, Version.One)
             (witnessSetTakenNeg S sigma f) ->
           Satisfies S sigma f2 /\
           T.PkgSet.Subset (witnessSetUntaken S f1)
             (witnessSetTakenNeg S sigma f) /\
           T.PkgSet.Subset (witnessSetTaken S sigma f2)
             (witnessSetTakenNeg S sigma f)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros Hyp f1 f2; simpl.
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; apply SOpt.singleton_in in H; congruence.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
        + destruct (proj1 IHa (proj1 Hyp) f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; left; [apply H1 | apply H2]; exact Hy.
        + destruct (proj1 IHb (proj2 Hyp) f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; right; [apply H1 | apply H2]; exact Hy.
      - destruct (satisfiesb S sigma a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + injection H as -> ->.
          split.
          { intro Hb'; apply Hyp; split;
              [apply satisfiesb_iff; exact Ea | exact Hb']. }
          split; intros y Hy; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; [left | right]; exact Hy.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S a) _ _ _ H).
        + assert (Hnb : ~ Satisfies S sigma b).
          { intro Hb'; apply Hyp; split;
              [apply satisfiesb_iff; exact Ea | exact Hb']. }
          destruct (proj2 IHb Hnb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; right;
            [apply H1 | apply H2]; exact Hy.
        + congruence.
        + destruct
            (proj2 IHa (proj1 (satisfiesb_false_iff S sigma a) Ea) f1 f2 H)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; left;
            [apply H1 | apply H2]; exact Hy.
        + exfalso;
            exact (proj2 (witnessSetUntaken_disjunct_det_aux S b) _ _ _ H).
      - destruct (satisfiesb S sigma a) eqn:Ea; intro H; apply SOpt.add_in in H;
          (destruct H as [H | H];
           [| apply T.PkgSet.union_spec in H; destruct H as [H | H]]).
        + congruence.
        + destruct (proj1 IHa (proj1 (satisfiesb_iff S sigma a) Ea) f1 f2 H)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; left;
            [apply H1 | apply H2]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + injection H as -> ->.
          assert (Hb : Satisfies S sigma b).
          { destruct Hyp as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
          split; [exact Hb |].
          split; intros y Hy; apply SOpt.add_in; right;
            apply T.PkgSet.union_spec; [left | right]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ H).
        + assert (Hb : Satisfies S sigma b).
          { destruct Hyp as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
          destruct (proj1 IHb Hb f1 f2 H) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply SOpt.add_in; right; apply T.PkgSet.union_spec; right;
            [apply H1 | apply H2]; exact Hy.
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
        + destruct (proj2 IHa (fun Ha => Hyp (or_introl Ha)) f1 f2 H)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; left; [apply H1 | apply H2]; exact Hy.
        + destruct (proj2 IHb (fun Hb => Hyp (or_intror Hb)) f1 f2 H)
            as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy;
            apply T.PkgSet.union_spec; right; [apply H1 | apply H2]; exact Hy.
      - exact (proj2 IHa Hyp f1 f2).
      - exact (proj1 IHa (satisfies_double_neg S sigma a Hyp) f1 f2).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
      - intro H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma coreResolution_disj_zero : forall S D sigma f1 f2,
        T.PkgSet.In (Name.Disjunct f1 f2, Version.Zero)
          (coreResolution S D sigma) ->
        Satisfies S sigma f1 /\
        T.PkgSet.Subset (witnessSetTaken S sigma f1)
          (coreResolution S D sigma) /\
        T.PkgSet.Subset (witnessSetUntaken S f2)
          (coreResolution S D sigma).
    Proof.
      intros S D sigma f1 f2 H; apply mem_coreResolution in H.
      destruct H as [[p [_ Hp]] | [[p [g [Hd Hw]]] | [x Hq]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - pose proof (witnessSet_subset_coreResolution S D sigma p g Hd)
          as Hsub.
        revert Hw Hsub; destruct (PkgSet.mem p S); intros Hw Hsub.
        + destruct (proj1 (witnessSetTaken_disj_zero_mono_aux S sigma g)
                      f1 f2 Hw) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy; apply Hsub;
            [apply H1 | apply H2]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ Hw).
      - discriminate.
    Qed.

    Lemma coreResolution_disj_one : forall S D sigma f1 f2,
        (forall p, PkgSet.In p S ->
         forall f, DepRel.In (p, f) D -> Satisfies S sigma f) ->
        T.PkgSet.In (Name.Disjunct f1 f2, Version.One)
          (coreResolution S D sigma) ->
        Satisfies S sigma f2 /\
        T.PkgSet.Subset (witnessSetUntaken S f1)
          (coreResolution S D sigma) /\
        T.PkgSet.Subset (witnessSetTaken S sigma f2)
          (coreResolution S D sigma).
    Proof.
      intros S D sigma f1 f2 Hclo H; apply mem_coreResolution in H.
      destruct H as [[p [_ Hp]] | [[p [g [Hd Hw]]] | [x Hq]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - pose proof (witnessSet_subset_coreResolution S D sigma p g Hd)
          as Hsub.
        revert Hw Hsub; destruct (PkgSet.mem p S) eqn:Ep; intros Hw Hsub.
        + assert (Hsat : Satisfies S sigma g).
          { apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hd]. }
          destruct (proj1 (witnessSetTaken_disj_one_mono_aux S sigma g)
                      Hsat f1 f2 Hw) as (Hs & H1 & H2).
          split; [exact Hs |]; split; intros y Hy; apply Hsub;
            [apply H1 | apply H2]; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ _ Hw).
      - discriminate.
    Qed.

    Lemma encodeNNF_dep_closure_aux :
      forall (S : PkgSet.t) (sigma : X.t -> Y.t) (Y_x : X.t -> YSet.t)
             (w : T.PkgSet.t),
        (forall x, YSet.In (sigma x) (Y_x x)) ->
        (forall p, PkgSet.In p S -> T.PkgSet.In (embedPkg p) w) ->
        (forall n v, T.PkgSet.In (Name.Orig n, v) w ->
           exists p, PkgSet.In p S /\ embedPkg p = (Name.Orig n, v)) ->
        (forall f1 f2, T.PkgSet.In (Name.Disjunct f1 f2, Version.Zero) w ->
           Satisfies S sigma f1 /\
           T.PkgSet.Subset (witnessSetTaken S sigma f1) w /\
           T.PkgSet.Subset (witnessSetUntaken S f2) w) ->
        (forall f1 f2, T.PkgSet.In (Name.Disjunct f1 f2, Version.One) w ->
           Satisfies S sigma f2 /\
           T.PkgSet.Subset (witnessSetUntaken S f1) w /\
           T.PkgSet.Subset (witnessSetTaken S sigma f2) w) ->
        (forall x, T.PkgSet.In (Name.Var x, Version.VarVal (sigma x)) w) ->
        forall f : Formula,
          (forall q0 : T.Pkg.t,
              (~ T.PkgSet.In q0 w /\
               T.PkgSet.Subset (witnessSetUntaken S f) w) \/
              (Satisfies S sigma f /\
               T.PkgSet.Subset (witnessSetTaken S sigma f) w) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeNNF Y_x q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w) /\
          (forall q0 : T.Pkg.t,
              (~ T.PkgSet.In q0 w /\
               T.PkgSet.Subset (witnessSetUntakenNeg S f) w) \/
              (~ Satisfies S sigma f /\
               T.PkgSet.Subset (witnessSetTakenNeg S sigma f) w) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeNNFneg Y_x q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w).
    Proof.
      intros S sigma Y_x w Hins Hemb Horig Hdz Hdo Hvar f.
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros q0 Hwit q m ws Henc Hqw.
      - apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
        destruct Hwit as [[Hq0 _] | [Hsat _]].
        + exfalso; exact (Hq0 Hqw).
        + destruct Hsat as [u [Hu HuS]].
          exists (Version.Orig u); split.
          * unfold embedVS; apply SOvv.mem_map;
              exists u; split; [exact Hu | reflexivity].
          * exact (Hemb (n, u) HuS).
      - apply SOed.add_in in Henc; destruct Henc as [He | He].
        + injection He as -> -> ->.
          destruct Hwit as [[Hq0 _] | [_ Hsub]].
          * exfalso; exact (Hq0 Hqw).
          * exists Version.One; split; [apply SOvv.singleton_in; reflexivity |].
            apply Hsub, SOpt.singleton_in; reflexivity.
        + apply SOvd.mem_map in He; destruct He as [u [Hu He]];
            injection He as -> -> ->.
          destruct (Horig n (Version.Orig u) Hqw) as [[pn pv] [HpS Hpe]].
          unfold embedPkg in Hpe; simpl in Hpe; injection Hpe as -> ->.
          destruct Hwit as [[_ Hsub] | [Hns _]].
          * assert (E : depTakenb S n vs = true).
            { apply depTakenb_iff; exists u; split; assumption. }
            exists Version.Zero;
              split; [apply SOvv.singleton_in; reflexivity |].
            apply Hsub.
            change (T.PkgSet.In (Name.NegDep n vs, Version.Zero)
                      (if depTakenb S n vs
                       then T.PkgSet.singleton (Name.NegDep n vs, Version.Zero)
                       else T.PkgSet.empty)).
            rewrite E; apply SOpt.singleton_in; reflexivity.
          * exfalso; apply Hns; exists u; split; assumption.
      - apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
        + refine (proj1 IHa q0 _ q m ws He Hqw).
          destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]].
          * left; split; [exact Hq0 |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
          * right; split; [exact (proj1 Hsat) |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
        + refine (proj1 IHb q0 _ q m ws He Hqw).
          destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]].
          * left; split; [exact Hq0 |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
          * right; split; [exact (proj2 Hsat) |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
      - apply SOed.add_in in Henc; destruct Henc as [He | He].
        + injection He as -> -> ->.
          destruct Hwit as [[Hq0 _] | [_ Hsub]].
          * exfalso; exact (Hq0 Hqw).
          * destruct (satisfiesb S sigma a) eqn:Ea.
            -- exists Version.One;
               split; [apply mem_zeroOne; right; reflexivity |].
               apply Hsub; simpl; rewrite Ea;
                 apply SOpt.add_in; left; reflexivity.
            -- exists Version.Zero;
               split; [apply mem_zeroOne; left; reflexivity |].
               apply Hsub; simpl; rewrite Ea;
                 apply SOpt.add_in; left; reflexivity.
        + apply T.DepRel.union_spec in He; destruct He as [He | He].
          * refine (proj2 IHa (Name.Disjunct (FNeg a) (FNeg b), Version.Zero)
                      _ q m ws He Hqw).
            destruct (T.PkgSet.mem
                        (Name.Disjunct (FNeg a) (FNeg b), Version.Zero) w)
              eqn:EM.
            -- apply T.PkgSet.mem_spec in EM.
               destruct (Hdz _ _ EM) as (HsF & HsubT & _).
               right; split; [exact HsF | exact HsubT].
            -- left; split.
               { intro Hin; apply T.PkgSet.mem_spec in Hin; congruence. }
               destruct Hwit as [[_ Hsub] | [Hns Hsub]].
               ++ intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
               ++ destruct (satisfiesb S sigma a) eqn:Ea.
                  ** intros y Hy; apply Hsub; simpl; rewrite Ea;
                       apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; left; exact Hy.
                  ** exfalso.
                     assert (Hin : T.PkgSet.In
                         (Name.Disjunct (FNeg a) (FNeg b), Version.Zero) w).
                     { apply Hsub; simpl; rewrite Ea;
                         apply SOpt.add_in; left; reflexivity. }
                     apply T.PkgSet.mem_spec in Hin; congruence.
          * refine (proj2 IHb (Name.Disjunct (FNeg a) (FNeg b), Version.One)
                      _ q m ws He Hqw).
            destruct (T.PkgSet.mem
                        (Name.Disjunct (FNeg a) (FNeg b), Version.One) w)
              eqn:EM.
            -- apply T.PkgSet.mem_spec in EM.
               destruct (Hdo _ _ EM) as (HsF & _ & HsubT).
               right; split; [exact HsF | exact HsubT].
            -- left; split.
               { intro Hin; apply T.PkgSet.mem_spec in Hin; congruence. }
               destruct Hwit as [[_ Hsub] | [Hns Hsub]].
               ++ intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
               ++ destruct (satisfiesb S sigma a) eqn:Ea.
                  ** exfalso.
                     assert (Hin : T.PkgSet.In
                         (Name.Disjunct (FNeg a) (FNeg b), Version.One) w).
                     { apply Hsub; simpl; rewrite Ea;
                         apply SOpt.add_in; left; reflexivity. }
                     apply T.PkgSet.mem_spec in Hin; congruence.
                  ** intros y Hy; apply Hsub; simpl; rewrite Ea;
                       apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; right; exact Hy.
      - apply SOed.add_in in Henc; destruct Henc as [He | He].
        + injection He as -> -> ->.
          destruct Hwit as [[Hq0 _] | [_ Hsub]].
          * exfalso; exact (Hq0 Hqw).
          * destruct (satisfiesb S sigma a) eqn:Ea.
            -- exists Version.Zero;
               split; [apply mem_zeroOne; left; reflexivity |].
               apply Hsub; simpl; rewrite Ea;
                 apply SOpt.add_in; left; reflexivity.
            -- exists Version.One;
               split; [apply mem_zeroOne; right; reflexivity |].
               apply Hsub; simpl; rewrite Ea;
                 apply SOpt.add_in; left; reflexivity.
        + apply T.DepRel.union_spec in He; destruct He as [He | He].
          * refine (proj1 IHa (Name.Disjunct a b, Version.Zero)
                      _ q m ws He Hqw).
            destruct (T.PkgSet.mem (Name.Disjunct a b, Version.Zero) w) eqn:EM.
            -- apply T.PkgSet.mem_spec in EM.
               destruct (Hdz _ _ EM) as (HsF & HsubT & _).
               right; split; [exact HsF | exact HsubT].
            -- left; split.
               { intro Hin; apply T.PkgSet.mem_spec in Hin; congruence. }
               destruct Hwit as [[_ Hsub] | [Hsat Hsub]].
               ++ intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
               ++ destruct (satisfiesb S sigma a) eqn:Ea.
                  ** exfalso.
                     assert
                       (Hin : T.PkgSet.In (Name.Disjunct a b, Version.Zero) w).
                     { apply Hsub; simpl; rewrite Ea;
                         apply SOpt.add_in; left; reflexivity. }
                     apply T.PkgSet.mem_spec in Hin; congruence.
                  ** intros y Hy; apply Hsub; simpl; rewrite Ea;
                       apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; left; exact Hy.
          * refine (proj1 IHb (Name.Disjunct a b, Version.One) _ q m ws He Hqw).
            destruct (T.PkgSet.mem (Name.Disjunct a b, Version.One) w) eqn:EM.
            -- apply T.PkgSet.mem_spec in EM.
               destruct (Hdo _ _ EM) as (HsF & _ & HsubT).
               right; split; [exact HsF | exact HsubT].
            -- left; split.
               { intro Hin; apply T.PkgSet.mem_spec in Hin; congruence. }
               destruct Hwit as [[_ Hsub] | [Hsat Hsub]].
               ++ intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
               ++ destruct (satisfiesb S sigma a) eqn:Ea.
                  ** intros y Hy; apply Hsub; simpl; rewrite Ea;
                       apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; right; exact Hy.
                  ** exfalso.
                     assert
                       (Hin : T.PkgSet.In (Name.Disjunct a b, Version.One) w).
                     { apply Hsub; simpl; rewrite Ea;
                         apply SOpt.add_in; left; reflexivity. }
                     apply T.PkgSet.mem_spec in Hin; congruence.
      - apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
        + refine (proj2 IHa q0 _ q m ws He Hqw).
          destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]].
          * left; split; [exact Hq0 |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
          * right; split; [intro Ha; exact (Hns (or_introl Ha)) |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
        + refine (proj2 IHb q0 _ q m ws He Hqw).
          destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]].
          * left; split; [exact Hq0 |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
          * right; split; [intro Hb; exact (Hns (or_intror Hb)) |].
            intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
      - exact (proj2 IHa q0 Hwit q m ws Henc Hqw).
      - destruct Hwit as [[Hq0 Hsub] | [Hnn Hsub]].
        + exact (proj1 IHa q0 (or_introl (conj Hq0 Hsub)) q m ws Henc Hqw).
        + exact (proj1 IHa q0
                   (or_intror (conj (satisfies_double_neg S sigma a Hnn) Hsub))
                   q m ws Henc Hqw).
      - apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
        destruct Hwit as [[Hq0 _] | [Hsat _]].
        + exfalso; exact (Hq0 Hqw).
        + exists (Version.VarVal (sigma x)); split.
          * apply mem_cmpVersionSet; exists (sigma x);
              split; [apply Hins | split; [exact Hsat | reflexivity]].
          * exact (Hvar x).
      - apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
        destruct Hwit as [[Hq0 _] | [Hns _]].
        + exfalso; exact (Hq0 Hqw).
        + exists (Version.VarVal (sigma x)); split.
          * apply mem_cmpVersionSet; exists (sigma x);
              split; [apply Hins |].
            split; [| reflexivity].
            rewrite opEvalY_complement; apply Bool.negb_true_iff.
            destruct (opEvalY op (sigma x) y) eqn:E;
              [exfalso; exact (Hns E) | reflexivity].
          * exact (Hvar x).
    Qed.

    Theorem variable_formula_completeness :
      forall (Y_x : X.t -> YSet.t) (R : PkgSet.t) (D : DepRel.t)
             (r : Pkg.t) (sigma : X.t -> Y.t),
        (forall x, YSet.In (sigma x) (Y_x x)) ->
        forall (S : PkgSet.t),
          IsResolution R D r S sigma ->
          T.IsResolution (reduceReal Y_x R D) (reduceDeps Y_x D) (embedPkg r)
            (coreResolution S D sigma).
    Proof.
      intros Y_x R D r sigma Hins S Hres;
        destruct Hres as [Hsub Hroot Hclo Huniq].
      assert (Hemb : forall p, PkgSet.In p S ->
          T.PkgSet.In (embedPkg p) (coreResolution S D sigma)).
      { intros p Hp; apply mem_coreResolution; left.
        exists p; split; [exact Hp | reflexivity]. }
      assert (Horig : forall n v,
          T.PkgSet.In (Name.Orig n, v) (coreResolution S D sigma) ->
          exists p, PkgSet.In p S /\ embedPkg p = (Name.Orig n, v)).
      { intros n v Hv; apply mem_coreResolution in Hv.
        destruct Hv as [[p [Hp Hpe]] | [[p [g [Hd Hw]]] | [x Hq]]].
        - exists p; split; [exact Hp | symmetry; exact Hpe].
        - exfalso; revert Hw; destruct (PkgSet.mem p S); intro Hw;
            [exact (witnessSetTaken_not_orig _ _ _ _ _ Hw)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw)].
        - discriminate. }
      assert (Hvar : forall x,
          T.PkgSet.In (Name.Var x, Version.VarVal (sigma x))
            (coreResolution S D sigma)).
      { intro x; apply mem_coreResolution; right; right;
          exists x; reflexivity. }
      assert (Hdz := fun f1 f2 => coreResolution_disj_zero S D sigma f1 f2).
      assert (Hdo := fun f1 f2 =>
                       coreResolution_disj_one S D sigma f1 f2 Hclo).
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy.
        apply mem_reduceReal.
        destruct Hy as [[p [Hp ->]] | [[p [g [Hd Hw]]] | [x ->]]].
        + left; exists p; split; [apply Hsub; exact Hp | reflexivity].
        + right; left; exists p, g; split; [exact Hd |].
          revert Hw; destruct (PkgSet.mem p S); intro Hw;
            [exact (witnessSetTaken_subset_witnessSet
                      S sigma (embedPkg p) g _ Hw)
            | exact (witnessSetUntaken_subset_witnessSet
                       S (embedPkg p) g _ Hw)].
        + right; right; exists x, (sigma x);
            split; [apply Hins | reflexivity].
      - exact (Hemb r Hroot).
      - intros q Hq m vs Hd.
        apply mem_reduceDeps in Hd; destruct Hd as [p [g [Hpg Henc]]].
        destruct (PkgSet.mem p S) eqn:Ep.
        + refine (proj1 (encodeNNF_dep_closure_aux S sigma Y_x _
            Hins Hemb Horig Hdz Hdo Hvar g) (embedPkg p) _ q m vs Henc Hq).
          right; split.
          * apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hpg].
          * pose proof (witnessSet_subset_coreResolution S D sigma p g Hpg)
              as Hs; rewrite Ep in Hs; exact Hs.
        + refine (proj1 (encodeNNF_dep_closure_aux S sigma Y_x _
            Hins Hemb Horig Hdz Hdo Hvar g) (embedPkg p) _ q m vs Henc Hq).
          left; split.
          * intro Hin; destruct p as [pn pv].
            destruct (Horig pn (Version.Orig pv) Hin) as [[qn qv] [HqS Hqe]].
            unfold embedPkg in Hqe; simpl in Hqe; injection Hqe as -> ->.
            apply PkgSet.mem_spec in HqS; congruence.
          * pose proof (witnessSet_subset_coreResolution S D sigma p g Hpg)
              as Hs; rewrite Ep in Hs; exact Hs.
      - intros n v v' Hv Hv'.
        apply mem_coreResolution in Hv, Hv'.
        destruct Hv as [[p1 [Hp1 He1]] | [[p1 [g1 [Hd1 Hw1]]] | [x1 Hq1]]];
          destruct Hv' as [[p2 [Hp2 He2]] | [[p2 [g2 [Hd2 Hw2]]] | [x2 Hq2]]].
        + destruct p1 as [n1 w1]; destruct p2 as [n2 w2].
          unfold embedPkg in He1, He2; simpl in He1, He2.
          injection He1 as -> ->; injection He2 as -> ->.
          f_equal; exact (Huniq _ _ _ Hp1 Hp2).
        + destruct p1 as [n1 w1]; unfold embedPkg in He1; simpl in He1;
            injection He1 as -> ->.
          exfalso; revert Hw2; destruct (PkgSet.mem p2 S); intro Hw2;
            [exact (witnessSetTaken_not_orig _ _ _ _ _ Hw2)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw2)].
        + destruct p1 as [n1 w1]; unfold embedPkg in He1; simpl in He1;
            injection He1 as -> ->.
          discriminate Hq2.
        + destruct p2 as [n2 w2]; unfold embedPkg in He2; simpl in He2;
            injection He2 as -> ->.
          exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
            [exact (witnessSetTaken_not_orig _ _ _ _ _ Hw1)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw1)].
        + destruct n as [n0 | x | f1 f2 | n0 vs0].
          * exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
              [exact (witnessSetTaken_not_orig _ _ _ _ _ Hw1)
              | exact (witnessSetUntaken_not_orig _ _ _ _ Hw1)].
          * exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
              [exact (witnessSetTaken_not_var _ _ _ _ _ Hw1)
              | exact (witnessSetUntaken_not_var _ _ _ _ Hw1)].
          * assert (G : forall p g v0, DepRel.In (p, g) D ->
                T.PkgSet.In (Name.Disjunct f1 f2, v0)
                  (if PkgSet.mem p S then witnessSetTaken S sigma g
                   else witnessSetUntaken S g) ->
                v0 =
                  (if satisfiesb S sigma f1
                   then Version.Zero else Version.One)).
            { intros p g v0 _ Hw; revert Hw;
                destruct (PkgSet.mem p S); intro Hw.
              - exact (witnessSetTaken_disjunct_det _ _ _ _ _ _ Hw).
              - exfalso;
                  exact (witnessSetUntaken_disjunct_det _ _ _ _ _ Hw). }
            rewrite (G _ _ _ Hd1 Hw1), (G _ _ _ Hd2 Hw2); reflexivity.
          * assert (G : forall p g v0, DepRel.In (p, g) D ->
                T.PkgSet.In (Name.NegDep n0 vs0, v0)
                  (if PkgSet.mem p S then witnessSetTaken S sigma g
                   else witnessSetUntaken S g) ->
                v0 =
                  (if depTakenb S n0 vs0 then Version.Zero else Version.One)).
            { intros p g v0 Hd Hw; revert Hw;
                destruct (PkgSet.mem p S) eqn:Ep; intro Hw.
              - apply (witnessSetTaken_negDep_det S sigma g); [| exact Hw].
                apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hd].
              - assert (E : depTakenb S n0 vs0 = true).
                { apply depTakenb_iff;
                    exact (witnessSetUntaken_negDep_exists _ _ _ _ _ Hw). }
                rewrite E;
                  exact (witnessSetUntaken_negDep_det _ _ _ _ _ Hw). }
            rewrite (G _ _ _ Hd1 Hw1), (G _ _ _ Hd2 Hw2); reflexivity.
        + injection Hq2 as -> ->.
          exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
            [exact (witnessSetTaken_not_var _ _ _ _ _ Hw1)
            | exact (witnessSetUntaken_not_var _ _ _ _ Hw1)].
        + injection Hq1 as -> ->.
          destruct p2 as [n2 w2]; unfold embedPkg in He2; simpl in He2;
            discriminate He2.
        + injection Hq1 as -> ->.
          exfalso; revert Hw2; destruct (PkgSet.mem p2 S); intro Hw2;
            [exact (witnessSetTaken_not_var _ _ _ _ _ Hw2)
            | exact (witnessSetUntaken_not_var _ _ _ _ Hw2)].
        + injection Hq1 as -> ->; injection Hq2 as -> ->; reflexivity.
    Qed.

    Module Lookup.
      Inductive Atom : Type :=
      | APos (n : N.t) (vs : VSet.t)
      | ANeg (n : N.t) (vs : VSet.t)
      | ADisj (f1 f2 : Formula)
      | AVar (x : X.t) (ys : YSet.t).
      Module XYS := PairUOT X YSet.AsUOT.
      Module XYSF := UOTCompareFacts XYS.
      #[local] Hint Rewrite XYSF.compare_eq_iff : cmp_varf.
      #[local] Hint Extern 1 => cmp_by XYSF.compare_antisym : cmp_varf.
      #[local] Hint Extern 1 => cmp_by XYSF.compare_lt_trans : cmp_varf.

      Module AComp <: ComparableType.
        Definition t := Atom.
        Definition compare (x y : t) : comparison :=
          match x, y with
          | APos n1 vs1, APos n2 vs2 => C.Dependees.compare (n1, vs1) (n2, vs2)
          | APos _ _, _ => Lt
          | ANeg _ _, APos _ _ => Gt
          | ANeg n1 vs1, ANeg n2 vs2 => C.Dependees.compare (n1, vs1) (n2, vs2)
          | ANeg _ _, _ => Lt
          | ADisj f1 g1, ADisj f2 g2 => DPair.compare (f1, g1) (f2, g2)
          | ADisj _ _, AVar _ _ => Lt
          | ADisj _ _, _ => Gt
          | AVar x1 ys1, AVar x2 ys2 => XYS.compare (x1, ys1) (x2, ys2)
          | AVar _ _, _ => Gt
          end.

        Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
        Proof. cmp_eq_iff cmp_varf. Qed.

        Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
        Proof. cmp_antisym cmp_varf. Qed.

        Lemma compare_lt_trans : forall x y z,
            compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
        Proof. cmp_lt_trans cmp_varf. Qed.
      End AComp.
      Module AOT := UOTFromCompare AComp.
      Module AtomSet := FSetUOT AOT.

      (* Mutual structural pairs for the same reason as encodeNNF. *)
      Fixpoint deepAtoms (Y_x : X.t -> YSet.t) (f : Formula) : AtomSet.t :=
        match f with
        | FDep n vs => AtomSet.singleton (APos n vs)
        | FConj a b => AtomSet.union (deepAtoms Y_x a) (deepAtoms Y_x b)
        | FDisj a b =>
            AtomSet.add (ADisj a b)
              (AtomSet.union (deepAtoms Y_x a) (deepAtoms Y_x b))
        | FNeg a => deepAtomsNeg Y_x a
        | FVarCmp x op y =>
            AtomSet.singleton
              (AVar x (YSet.filter (fun y' => opEvalY op y' y) (Y_x x)))
        end
      with deepAtomsNeg (Y_x : X.t -> YSet.t) (f : Formula) : AtomSet.t :=
        match f with
        | FDep n vs => AtomSet.singleton (ANeg n vs)
        | FConj a b =>
            AtomSet.add (ADisj (FNeg a) (FNeg b))
              (AtomSet.union (deepAtomsNeg Y_x a) (deepAtomsNeg Y_x b))
        | FDisj a b => AtomSet.union (deepAtomsNeg Y_x a) (deepAtomsNeg Y_x b)
        | FNeg a => deepAtoms Y_x a
        | FVarCmp x op y =>
            AtomSet.singleton
              (AVar x (YSet.filter (fun y' => opEvalY (cmpComplement op) y' y)
                         (Y_x x)))
        end.

      Fixpoint negAtoms (f : Formula) : AtomSet.t :=
        match f with
        | FDep _ _ => AtomSet.empty
        | FConj a b => AtomSet.union (negAtoms a) (negAtoms b)
        | FDisj a b => AtomSet.union (negAtoms a) (negAtoms b)
        | FNeg a => negAtomsNeg a
        | FVarCmp _ _ _ => AtomSet.empty
        end
      with negAtomsNeg (f : Formula) : AtomSet.t :=
        match f with
        | FDep n vs => AtomSet.singleton (ANeg n vs)
        | FConj a b => AtomSet.union (negAtomsNeg a) (negAtomsNeg b)
        | FDisj a b => AtomSet.union (negAtomsNeg a) (negAtomsNeg b)
        | FNeg a => negAtoms a
        | FVarCmp _ _ _ => AtomSet.empty
        end.

      Module NEqb := UOTEqb N.
      Definition occursNegOnb (f : Formula) (n : N.t) (v : V.t) : bool :=
        AtomSet.exists_ (fun a =>
            match a with
            | ANeg n' vs => andb (NEqb.eqb n' n) (VSet.mem v vs)
            | _ => false
            end)
          (negAtoms f).

      Definition withDisj (Y_x : X.t -> YSet.t) (D : DepRel.t)
          (a b : Formula) : DepRel.t :=
        DepRel.filter (fun '(_, f) =>
            AtomSet.mem (ADisj a b) (deepAtoms Y_x f)) D.

      Lemma mem_withDisj : forall Y_x D a b (p : Pkg.t) (f : Formula),
          DepRel.In (p, f) (withDisj Y_x D a b) <->
          DepRel.In (p, f) D /\ AtomSet.In (ADisj a b) (deepAtoms Y_x f).
      Proof.
        intros Y_x D a b p f; unfold withDisj.
        rewrite DepRel.filter_spec'.
        cbn beta iota; rewrite AtomSet.mem_spec; reflexivity.
      Qed.

      Definition withNegOn (D : DepRel.t) (n : N.t) (v : V.t) : DepRel.t :=
        DepRel.filter (fun '(_, f) => occursNegOnb f n v) D.

      Module DepRelFibred := FibredRel Pkg Dependees DepElt DepRel.
      Definition subInstanceOrig (D : DepRel.t) (p : Pkg.t) : DepRel.t :=
        let '(n, v) := p in
        DepRel.union (DepRelFibred.tailFibre D (n, v)) (withNegOn D n v).

      Lemma encodeNNF_src_orig_aux : forall Y_x f,
          (forall (q : T.Pkg.t) n v (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig n, Version.Orig v), d)
                (encodeNNF Y_x q f) ->
              q = (Name.Orig n, Version.Orig v) \/
              exists vs, AtomSet.In (ANeg n vs) (negAtoms f) /\
                VSet.In v vs) /\
          (forall (q : T.Pkg.t) n v (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig n, Version.Orig v), d)
                (encodeNNFneg Y_x q f) ->
              q = (Name.Orig n, Version.Orig v) \/
              exists vs, AtomSet.In (ANeg n vs) (negAtomsNeg f) /\
                VSet.In v vs).
      Proof.
        intros Y_x.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          split; intros q n v d H; simpl in H; simpl.
        - apply SOed.singleton_in in H; left; congruence.
        - apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
          apply SOvd.mem_map in H; destruct H as [u [Hu He]].
          injection He as -> -> ->.
          right; exists ws; split;
            [apply AtomSet.singleton_spec; reflexivity | exact Hu].
        - apply T.DepRel.union_spec in H; destruct H as [H | H].
          + destruct (proj1 IHa _ _ _ _ H) as [E | [vs [Ha Hv]]];
              [left; exact E |].
            right; exists vs; split;
              [apply AtomSet.union_spec; left; exact Ha | exact Hv].
          + destruct (proj1 IHb _ _ _ _ H) as [E | [vs [Ha Hv]]];
              [left; exact E |].
            right; exists vs; split;
              [apply AtomSet.union_spec; right; exact Ha | exact Hv].
        - apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
          apply T.DepRel.union_spec in H; destruct H as [H | H].
          + destruct (proj2 IHa _ _ _ _ H) as [E | [vs [Ha Hv]]];
              [discriminate |].
            right; exists vs; split;
              [apply AtomSet.union_spec; left; exact Ha | exact Hv].
          + destruct (proj2 IHb _ _ _ _ H) as [E | [vs [Ha Hv]]];
              [discriminate |].
            right; exists vs; split;
              [apply AtomSet.union_spec; right; exact Ha | exact Hv].
        - apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
          apply T.DepRel.union_spec in H; destruct H as [H | H].
          + destruct (proj1 IHa _ _ _ _ H) as [E | [vs [Ha Hv]]];
              [discriminate |].
            right; exists vs; split;
              [apply AtomSet.union_spec; left; exact Ha | exact Hv].
          + destruct (proj1 IHb _ _ _ _ H) as [E | [vs [Ha Hv]]];
              [discriminate |].
            right; exists vs; split;
              [apply AtomSet.union_spec; right; exact Ha | exact Hv].
        - apply T.DepRel.union_spec in H; destruct H as [H | H].
          + destruct (proj2 IHa _ _ _ _ H) as [E | [vs [Ha Hv]]];
              [left; exact E |].
            right; exists vs; split;
              [apply AtomSet.union_spec; left; exact Ha | exact Hv].
          + destruct (proj2 IHb _ _ _ _ H) as [E | [vs [Ha Hv]]];
              [left; exact E |].
            right; exists vs; split;
              [apply AtomSet.union_spec; right; exact Ha | exact Hv].
        - exact (proj2 IHa _ _ _ _ H).
        - exact (proj1 IHa _ _ _ _ H).
        - apply SOed.singleton_in in H; left; congruence.
        - apply SOed.singleton_in in H; left; congruence.
      Qed.

      Lemma occursNegOnb_iff : forall f n v,
          occursNegOnb f n v = true <->
          exists vs, AtomSet.In (ANeg n vs) (negAtoms f) /\ VSet.In v vs.
      Proof.
        intros f n v; unfold occursNegOnb.
        rewrite AtomSet.exists_spec'.
        split.
        - intros [[m ws | m ws | f1 f2 | x ys] [Ha Hm]]; simpl in Hm;
            try discriminate.
          apply Bool.andb_true_iff in Hm as [Hn Hv].
          apply NEqb.eqb_true_iff in Hn as ->.
          exists ws; split; [exact Ha | apply VSet.mem_spec; exact Hv].
        - intros [vs [Ha Hv]].
          exists (ANeg n vs); split; [exact Ha |]; simpl.
          rewrite NEqb.eqb_refl; simpl; apply VSet.mem_spec; exact Hv.
      Qed.

      Theorem dependees_lookupOrig : forall Y_x D n v,
          T.dependees (reduceDeps Y_x D) (Name.Orig n, Version.Orig v) =
          T.dependees (reduceDeps Y_x (subInstanceOrig D (n, v)))
            (Name.Orig n, Version.Orig v).
      Proof.
        intros Y_x D n v; apply T.dependees_ext; intro h.
        split; intro H;
          apply mem_reduceDeps in H; destruct H as [p [f [Hd He]]];
          apply mem_reduceDeps; unfold encodeNNF in He.
        - destruct (proj1 (encodeNNF_src_orig_aux Y_x f) _ _ _ _ He)
            as [Eq | [vs [Ha Hv]]].
          + destruct p as [pn pv]; unfold embedPkg in Eq; simpl in Eq;
              injection Eq as -> ->.
            exists (n, v), f; split; [| exact He].
            unfold subInstanceOrig; apply DepRel.union_spec; left.
            unfold DepRelFibred.tailFibre;
              rewrite DepRel.filter_spec'.
            split; [exact Hd |].
            change ((if Pkg.eq_dec (n, v) (n, v) then true else false) = true).
            destruct (Pkg.eq_dec (n, v) (n, v)) as [_ | Hne];
              [reflexivity | exfalso; apply Hne; reflexivity].
          + exists p, f; split; [| exact He].
            unfold subInstanceOrig; apply DepRel.union_spec; right.
            unfold withNegOn;
              rewrite DepRel.filter_spec'.
            split; [exact Hd |].
            apply occursNegOnb_iff; exists vs; split; [exact Ha | exact Hv].
        - exists p, f; split; [| exact He].
          unfold subInstanceOrig in Hd; apply DepRel.union_spec in Hd.
          unfold DepRelFibred.tailFibre, withNegOn in Hd.
          destruct Hd as [Hd | Hd];
            rewrite DepRel.filter_spec' in Hd;
            exact (proj1 Hd).
      Qed.

      Lemma encodeNNF_src_disj_aux : forall Y_x f,
          (forall (q : T.Pkg.t) a b (i : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct a b, i), d) (encodeNNF Y_x q f) ->
              q = (Name.Disjunct a b, i) \/
              (AtomSet.In (ADisj a b) (deepAtoms Y_x f) /\
               T.DepRel.In ((Name.Disjunct a b, i), d)
                 (T.DepRel.union
                    (encodeNNF Y_x (Name.Disjunct a b, Version.Zero) a)
                    (encodeNNF Y_x (Name.Disjunct a b, Version.One) b)))) /\
          (forall (q : T.Pkg.t) a b (i : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct a b, i), d) (encodeNNFneg Y_x q f) ->
              q = (Name.Disjunct a b, i) \/
              (AtomSet.In (ADisj a b) (deepAtomsNeg Y_x f) /\
               T.DepRel.In ((Name.Disjunct a b, i), d)
                 (T.DepRel.union
                    (encodeNNF Y_x (Name.Disjunct a b, Version.Zero) a)
                    (encodeNNF Y_x (Name.Disjunct a b, Version.One) b)))).
      Proof.
        intros Y_x.
        induction f as [m ws | a1 IHa b1 IHb | a1 IHa b1 IHb | a1 IHa | x op y];
          split; intros q a b i d H; simpl in H; simpl.
        - apply SOed.singleton_in in H; left; congruence.
        - apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
          apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
        - apply T.DepRel.union_spec in H; destruct H as [H | H].
          + destruct (proj1 IHa _ _ _ _ _ H) as [E | [Ha He]];
              [left; exact E |].
            right; split;
              [apply AtomSet.union_spec; left; exact Ha | exact He].
          + destruct (proj1 IHb _ _ _ _ _ H) as [E | [Ha He]];
              [left; exact E |].
            right; split;
              [apply AtomSet.union_spec; right; exact Ha | exact He].
        - apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
          apply T.DepRel.union_spec in H; destruct H as [H | H].
          + destruct (proj2 IHa _ _ _ _ _ H) as [E | [Ha He]].
            * injection E as <- <- <-.
              right; split; [apply AtomSet.add_spec; left; reflexivity |].
              simpl; apply T.DepRel.union_spec; left; exact H.
            * right; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; left;
                 exact Ha
                | exact He].
          + destruct (proj2 IHb _ _ _ _ _ H) as [E | [Ha He]].
            * injection E as <- <- <-.
              right; split; [apply AtomSet.add_spec; left; reflexivity |].
              simpl; apply T.DepRel.union_spec; right; exact H.
            * right; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; right;
                 exact Ha
                | exact He].
        - apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
          apply T.DepRel.union_spec in H; destruct H as [H | H].
          + destruct (proj1 IHa _ _ _ _ _ H) as [E | [Ha He]].
            * injection E as <- <- <-.
              right; split; [apply AtomSet.add_spec; left; reflexivity |].
              apply T.DepRel.union_spec; left; exact H.
            * right; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; left;
                 exact Ha
                | exact He].
          + destruct (proj1 IHb _ _ _ _ _ H) as [E | [Ha He]].
            * injection E as <- <- <-.
              right; split; [apply AtomSet.add_spec; left; reflexivity |].
              apply T.DepRel.union_spec; right; exact H.
            * right; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; right;
                 exact Ha
                | exact He].
        - apply T.DepRel.union_spec in H; destruct H as [H | H].
          + destruct (proj2 IHa _ _ _ _ _ H) as [E | [Ha He]];
              [left; exact E |].
            right; split;
              [apply AtomSet.union_spec; left; exact Ha | exact He].
          + destruct (proj2 IHb _ _ _ _ _ H) as [E | [Ha He]];
              [left; exact E |].
            right; split;
              [apply AtomSet.union_spec; right; exact Ha | exact He].
        - exact (proj2 IHa _ _ _ _ _ H).
        - exact (proj1 IHa _ _ _ _ _ H).
        - apply SOed.singleton_in in H; left; congruence.
        - apply SOed.singleton_in in H; left; congruence.
      Qed.

      Theorem dependees_lookupDisjunct : forall Y_x D a b (i : Version.t),
          T.dependees (reduceDeps Y_x D) (Name.Disjunct a b, i) =
          T.dependees (reduceDeps Y_x (withDisj Y_x D a b))
            (Name.Disjunct a b, i).
      Proof.
        intros Y_x D a b i; apply T.dependees_ext; intro h;
          rewrite !mem_reduceDeps.
        split; intros [p [f [Hd He]]].
        - destruct (proj1 (encodeNNF_src_disj_aux Y_x f) _ _ _ _ _ He)
            as [Eq | [Ha _]].
          + destruct p as [pn pv]; unfold embedPkg in Eq; simpl in Eq;
              discriminate.
          + exists p, f; split;
              [apply mem_withDisj; split; [exact Hd | exact Ha] | exact He].
        - apply mem_withDisj in Hd; destruct Hd as [Hd _].
          exists p, f; split; [exact Hd | exact He].
      Qed.

      Lemma encodeNNF_src_negDep_aux : forall Y_x f,
          (forall (q : T.Pkg.t) n vs (i : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d) (encodeNNF Y_x q f) ->
              q = (Name.NegDep n vs, i)) /\
          (forall (q : T.Pkg.t) n vs (i : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d) (encodeNNFneg Y_x q f) ->
              q = (Name.NegDep n vs, i)).
      Proof.
        intros Y_x.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          split; intros q n vs i d H; simpl in H.
        - apply SOed.singleton_in in H; congruence.
        - apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
          apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
        - apply T.DepRel.union_spec in H; destruct H as [H | H];
            [exact (proj1 IHa _ _ _ _ _ H) | exact (proj1 IHb _ _ _ _ _ H)].
        - apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
          apply T.DepRel.union_spec in H; destruct H as [H | H];
            [assert (E := proj2 IHa _ _ _ _ _ H); discriminate
            | assert (E := proj2 IHb _ _ _ _ _ H); discriminate].
        - apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
          apply T.DepRel.union_spec in H; destruct H as [H | H];
            [assert (E := proj1 IHa _ _ _ _ _ H); discriminate
            | assert (E := proj1 IHb _ _ _ _ _ H); discriminate].
        - apply T.DepRel.union_spec in H; destruct H as [H | H];
            [exact (proj2 IHa _ _ _ _ _ H) | exact (proj2 IHb _ _ _ _ _ H)].
        - exact (proj2 IHa _ _ _ _ _ H).
        - exact (proj1 IHa _ _ _ _ _ H).
        - apply SOed.singleton_in in H; congruence.
        - apply SOed.singleton_in in H; congruence.
      Qed.

      Theorem dependees_lookupNegDep : forall Y_x D n vs (i : Version.t),
          T.dependees (reduceDeps Y_x D) (Name.NegDep n vs, i) =
          T.DependeesSet.empty.
      Proof.
        intros Y_x D n vs i; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [f [_ He]]]; unfold encodeNNF in He.
        assert (E := proj1 (encodeNNF_src_negDep_aux Y_x f) _ _ _ _ _ He).
        unfold embedPkg in E; simpl in E; discriminate.
      Qed.

      Lemma encodeNNF_src_var_aux : forall Y_x f,
          (forall (q : T.Pkg.t) x (y : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Var x, y), d) (encodeNNF Y_x q f) ->
              q = (Name.Var x, y)) /\
          (forall (q : T.Pkg.t) x (y : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Var x, y), d) (encodeNNFneg Y_x q f) ->
              q = (Name.Var x, y)).
      Proof.
        intros Y_x.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x0 op y0];
          split; intros q x y d H; simpl in H.
        - apply SOed.singleton_in in H; congruence.
        - apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
          apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
        - apply T.DepRel.union_spec in H; destruct H as [H | H];
            [exact (proj1 IHa _ _ _ _ H) | exact (proj1 IHb _ _ _ _ H)].
        - apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
          apply T.DepRel.union_spec in H; destruct H as [H | H];
            [assert (E := proj2 IHa _ _ _ _ H); discriminate
            | assert (E := proj2 IHb _ _ _ _ H); discriminate].
        - apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
          apply T.DepRel.union_spec in H; destruct H as [H | H];
            [assert (E := proj1 IHa _ _ _ _ H); discriminate
            | assert (E := proj1 IHb _ _ _ _ H); discriminate].
        - apply T.DepRel.union_spec in H; destruct H as [H | H];
            [exact (proj2 IHa _ _ _ _ H) | exact (proj2 IHb _ _ _ _ H)].
        - exact (proj2 IHa _ _ _ _ H).
        - exact (proj1 IHa _ _ _ _ H).
        - apply SOed.singleton_in in H; congruence.
        - apply SOed.singleton_in in H; congruence.
      Qed.

      Theorem dependees_lookupVar : forall Y_x D x (y : Version.t),
          T.dependees (reduceDeps Y_x D) (Name.Var x, y) = T.DependeesSet.empty.
      Proof.
        intros Y_x D x y; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [f [_ He]]]; unfold encodeNNF in He.
        assert (E := proj1 (encodeNNF_src_var_aux Y_x f) _ _ _ _ He).
        unfold embedPkg in E; simpl in E; discriminate.
      Qed.

      Lemma witnessSet_src_aux : forall f,
          (forall (q : T.Pkg.t) nm (w : Version.t),
              T.PkgSet.In (nm, w) (witnessSet q f) ->
              (exists a b, nm = Name.Disjunct a b) \/
              (exists n vs, nm = Name.NegDep n vs)) /\
          (forall (q : T.Pkg.t) nm (w : Version.t),
              T.PkgSet.In (nm, w) (witnessSetNeg q f) ->
              (exists a b, nm = Name.Disjunct a b) \/
              (exists n vs, nm = Name.NegDep n vs)).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          split; intros q nm w H; simpl in H.
        - destruct (SOpt.empty_in _ H).
        - apply SOpt.add_in in H; destruct H as [H | H];
            [| apply SOpt.singleton_in in H];
            right; exists m, ws; congruence.
        - apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
        - apply SOpt.add_in in H; destruct H as [H | H];
            [left; exists (FNeg a), (FNeg b); congruence |].
          apply SOpt.add_in in H; destruct H as [H | H];
            [left; exists (FNeg a), (FNeg b); congruence |].
          apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
        - apply SOpt.add_in in H; destruct H as [H | H];
            [left; exists a, b; congruence |].
          apply SOpt.add_in in H; destruct H as [H | H];
            [left; exists a, b; congruence |].
          apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (proj1 IHa _ _ _ H) | exact (proj1 IHb _ _ _ H)].
        - apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (proj2 IHa _ _ _ H) | exact (proj2 IHb _ _ _ H)].
        - exact (proj2 IHa _ _ _ H).
        - exact (proj1 IHa _ _ _ H).
        - destruct (SOpt.empty_in _ H).
        - destruct (SOpt.empty_in _ H).
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Theorem reduceReal_lookupOrig : forall Y_x R D n v,
          T.PkgSet.In (Name.Orig n, Version.Orig v) (reduceReal Y_x R D) <->
          T.PkgSet.In (Name.Orig n, Version.Orig v)
            (reduceReal Y_x (PkgFibred.idFibre R (n, v)) DepRel.empty).
      Proof.
        intros Y_x R D n v; rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [HR Hq]] | [[p [f [_ Hw]]] | [x [y [_ Hq]]]]].
          + unfold embedPkg in Hq; injection Hq as <- <-.
            left; exists (n, v).
            split; [apply PkgFibred.mem_idFibre; split; [exact HR | reflexivity]
                   | reflexivity].
          + exfalso; destruct (proj1 (witnessSet_src_aux f) _ _ _ Hw)
              as [[a [b He]] | [m [ws He]]]; discriminate He.
          + discriminate Hq.
        - intros [[[qn qv] [HR Hq]] | [[p [f [Hd _]]] | [x [y [_ Hq]]]]].
          + apply PkgFibred.mem_idFibre in HR; destruct HR as [HR _].
            left; exists (qn, qv); split; [exact HR | exact Hq].
          + destruct (DepRel.empty_spec Hd).
          + discriminate Hq.
      Qed.

      Theorem reduceReal_lookupVar : forall Y_x R D x (w : Version.t),
          T.PkgSet.In (Name.Var x, w) (reduceReal Y_x R D) <->
          T.PkgSet.In (Name.Var x, w)
            (reduceReal Y_x PkgSet.empty DepRel.empty).
      Proof.
        intros Y_x R D x w; rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [[p [f [_ Hw]]] | Hv]].
          + unfold embedPkg in Hq; discriminate Hq.
          + exfalso; destruct (proj1 (witnessSet_src_aux f) _ _ _ Hw)
              as [[a [b He]] | [m [ws He]]]; discriminate He.
          + right; right; exact Hv.
        - intros [[p [Hp _]] | [[p [f [Hd _]]] | Hv]].
          + destruct (PkgSet.empty_spec Hp).
          + destruct (DepRel.empty_spec Hd).
          + right; right; exact Hv.
      Qed.
    End Lookup.
  End Reduction.
End VariableFormula.
