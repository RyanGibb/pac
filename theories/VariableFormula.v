From Stdlib Require Import MSets List Lia.
From PackageCalculus Require Import Prelude Core Versions.

Create HintDb cmp_varf.
Create Rewrite HintDb cmp_varf.

(* Each spine-fused fixpoint family is four functions, so its lemmas are
   four-way conjunctions; repeat split would run past the conjunction and
   into the products and conjunctions of the conjuncts themselves. *)
Ltac split4v := split; [| split; [| split]].

Module VariableFormula (N V : UsualOrderedType)
    (X : FiniteUsualOrderedType) (Y : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive Formula : Type :=
  | FDep (m : N.t) (vs : VSet.t)
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
    | FDep m vs => exists v, VSet.In v vs /\ PkgSet.In (m, v) S
    | FConj f1 f2 => Satisfies S sigma f1 /\ Satisfies S sigma f2
    | FDisj f1 f2 => Satisfies S sigma f1 \/ Satisfies S sigma f2
    | FNeg f1 => ~ Satisfies S sigma f1
    | FVarCmp x op y => opEvalY op (sigma x) y = true
    end.

  Fixpoint satisfiesb (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
      bool :=
    match f with
    | FDep m vs => VSet.exists_ (fun v => PkgSet.mem (m, v) S) vs
    | FConj f1 f2 => andb (satisfiesb S sigma f1) (satisfiesb S sigma f2)
    | FDisj f1 f2 => orb (satisfiesb S sigma f1) (satisfiesb S sigma f2)
    | FNeg f1 => negb (satisfiesb S sigma f1)
    | FVarCmp x op y => opEvalY op (sigma x) y
    end.

  Lemma satisfiesb_iff : forall S sigma f,
      satisfiesb S sigma f = true <-> Satisfies S sigma f.
  Proof.
    intros S sigma f;
      induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
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
    Module FList := ListComp FComp.
    Module FListOT := UOTFromCompare FList.
    Module FListF := UOTCompareFacts FListOT.

    Module XF := UOTCompareFacts X.
    #[local] Hint Rewrite DepF.compare_eq_iff FListF.compare_eq_iff
      XF.compare_eq_iff : cmp_varf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by FListF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by XF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by FListF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by XF.compare_lt_trans : cmp_varf.

    Module Name.
      Inductive name : Type :=
      | Orig (m : N.t)
      | Var (x : X.t)
      | Disjunct (fs : list Formula).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, _ => Lt
        | Var _, Orig _ => Gt
        | Var x1, Var x2 => X.compare x1 x2
        | Var _, _ => Lt
        | Disjunct fs1, Disjunct fs2 => FListOT.compare fs1 fs2
        | Disjunct _, _ => Gt
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
    Module NatF := UOTCompareFacts Nat_as_OT.
    #[local] Hint Rewrite VF.compare_eq_iff YF.compare_eq_iff
      NatF.compare_eq_iff : cmp_varf.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by YF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by NatF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by YF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by NatF.compare_lt_trans : cmp_varf.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Idx (i : nat)
      | VarVal (y : Y.t)
      | Bot.
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, _ => Lt
        | Idx _, Orig _ => Gt
        | Idx i, Idx j => Nat.compare i j
        | Idx _, _ => Lt
        | VarVal y1, VarVal y2 => Y.compare y1 y2
        | VarVal _, Bot => Lt
        | VarVal _, _ => Gt
        | Bot, Bot => Eq
        | Bot, _ => Gt
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
    Module NSet := FSetUOT N.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(m, v) := p in (Name.Orig m, Version.Orig v).

    Module SOvv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map Version.Orig vs.

    Module YSet := FSetUOT Y.
    Module SOyv := SetOps Y VersionOT YSet T.VSet.
    Definition cmpVersionSet (Y_x : YSet.t) (op : CmpOp) (y : Y.t) : T.VSet.t :=
      SOyv.filterMap (fun y' =>
          if opEvalY op y' y then Some (Version.VarVal y') else None)
        Y_x.

    Fixpoint disjSpine (f : Formula) : list Formula :=
      match f with
      | FDisj a b => a :: disjSpine b
      | _ => f :: nil
      end.

    Fixpoint negConjSpine (f : Formula) : list Formula :=
      match f with
      | FConj a b => FNeg a :: negConjSpine b
      | _ => FNeg f :: nil
      end.

    Definition idxSet (k : nat) : T.VSet.t :=
      T.VSet.ofList (List.map Version.Idx (List.seq 0 k)).

    Definition idxPkgs (n : Name.t) (k : nat) : T.PkgSet.t :=
      T.PkgSet.ofList (List.map (fun i => (n, Version.Idx i)) (List.seq 0 k)).

    Definition complementVS (Vq : N.t -> VSet.t) (m : N.t) (vs : VSet.t) : T.VSet.t :=
      T.VSet.add Version.Bot (embedVS (VSet.diff (Vq m) vs)).

    (* A four-way mutual structural family avoids well-founded recursion on
       a measure; the De Morgan, double-negation, and complemented-comparison
       cases are inlined.  The spine walkers carry the position of the
       alternative they are encoding, and repeat their sibling's non-spine
       cases for the same reason: calling the sibling on the matched term
       itself would leave the guard condition. *)
    Fixpoint encodeNNF (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t)
        (p : T.Pkg.t) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep m vs => T.DepRel.singleton (p, (Name.Orig m, embedVS vs))
      | FConj a b =>
          T.DepRel.union (encodeNNF Y_x Vq p a) (encodeNNF Y_x Vq p b)
      | FDisj a b =>
          let n := Name.Disjunct (a :: disjSpine b) in
          T.DepRel.add (p, (n, idxSet (List.length (a :: disjSpine b))))
            (T.DepRel.union (encodeNNF Y_x Vq (n, Version.Idx 0) a)
               (encodeDisj Y_x Vq n 1 b))
      | FNeg a => encodeNNFneg Y_x Vq p a
      | FVarCmp x op y =>
          T.DepRel.singleton (p, (Name.Var x, cmpVersionSet (Y_x x) op y))
      end
    with encodeDisj (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t) (n : Name.t)
        (i : nat) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep m vs =>
          T.DepRel.singleton ((n, Version.Idx i), (Name.Orig m, embedVS vs))
      | FConj a b =>
          T.DepRel.union (encodeNNF Y_x Vq (n, Version.Idx i) a)
            (encodeNNF Y_x Vq (n, Version.Idx i) b)
      | FDisj a b =>
          T.DepRel.union (encodeNNF Y_x Vq (n, Version.Idx i) a)
            (encodeDisj Y_x Vq n (S i) b)
      | FNeg a => encodeNNFneg Y_x Vq (n, Version.Idx i) a
      | FVarCmp x op y =>
          T.DepRel.singleton
            ((n, Version.Idx i), (Name.Var x, cmpVersionSet (Y_x x) op y))
      end
    with encodeNNFneg (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t)
        (p : T.Pkg.t) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep m vs => T.DepRel.singleton (p, (Name.Orig m, complementVS Vq m vs))
      | FConj a b =>
          let n := Name.Disjunct (FNeg a :: negConjSpine b) in
          T.DepRel.add
            (p, (n, idxSet (List.length (FNeg a :: negConjSpine b))))
            (T.DepRel.union (encodeNNFneg Y_x Vq (n, Version.Idx 0) a)
               (encodeConjNeg Y_x Vq n 1 b))
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg Y_x Vq p a) (encodeNNFneg Y_x Vq p b)
      | FNeg a => encodeNNF Y_x Vq p a
      | FVarCmp x op y =>
          T.DepRel.singleton
            (p, (Name.Var x, cmpVersionSet (Y_x x) (cmpComplement op) y))
      end
    with encodeConjNeg (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t)
        (n : Name.t) (i : nat) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep m vs =>
          T.DepRel.singleton ((n, Version.Idx i), (Name.Orig m, complementVS Vq m vs))
      | FConj a b =>
          T.DepRel.union (encodeNNFneg Y_x Vq (n, Version.Idx i) a)
            (encodeConjNeg Y_x Vq n (S i) b)
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg Y_x Vq (n, Version.Idx i) a)
            (encodeNNFneg Y_x Vq (n, Version.Idx i) b)
      | FNeg a => encodeNNF Y_x Vq (n, Version.Idx i) a
      | FVarCmp x op y =>
          T.DepRel.singleton
            ((n, Version.Idx i),
             (Name.Var x, cmpVersionSet (Y_x x) (cmpComplement op) y))
      end.

    Fixpoint witnessSet (p : T.Pkg.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b => T.PkgSet.union (witnessSet p a) (witnessSet p b)
      | FDisj a b =>
          let n := Name.Disjunct (a :: disjSpine b) in
          T.PkgSet.union (idxPkgs n (List.length (a :: disjSpine b)))
            (T.PkgSet.union (witnessSet (n, Version.Idx 0) a)
               (witnessDisj n 1 b))
      | FNeg a => witnessSetNeg p a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessDisj (n : Name.t) (i : nat) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSet (n, Version.Idx i) a)
            (witnessSet (n, Version.Idx i) b)
      | FDisj a b =>
          T.PkgSet.union (witnessSet (n, Version.Idx i) a)
            (witnessDisj n (S i) b)
      | FNeg a => witnessSetNeg (n, Version.Idx i) a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessSetNeg (p : T.Pkg.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          let n := Name.Disjunct (FNeg a :: negConjSpine b) in
          T.PkgSet.union (idxPkgs n (List.length (FNeg a :: negConjSpine b)))
            (T.PkgSet.union (witnessSetNeg (n, Version.Idx 0) a)
               (witnessConjNeg n 1 b))
      | FDisj a b =>
          T.PkgSet.union (witnessSetNeg p a) (witnessSetNeg p b)
      | FNeg a => witnessSet p a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessConjNeg (n : Name.t) (i : nat) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetNeg (n, Version.Idx i) a)
            (witnessConjNeg n (S i) b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetNeg (n, Version.Idx i) a)
            (witnessSetNeg (n, Version.Idx i) b)
      | FNeg a => witnessSet (n, Version.Idx i) a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end.

    Fixpoint fnames (f : Formula) : NSet.t :=
      match f with
      | FDep m _ => NSet.singleton m
      | FConj a b => NSet.union (fnames a) (fnames b)
      | FDisj a b => NSet.union (fnames a) (fnames b)
      | FNeg a => fnames a
      | FVarCmp _ _ _ => NSet.empty
      end.

    Module SOen := SetOps DepElt N DepRel NSet.
    Definition depNames (D : DepRel.t) : NSet.t :=
      SOen.unionMap (fun '(_, f) => fnames f) D.

    Module SOpn := SetOps Pkg N PkgSet NSet.
    Definition instNames (R : PkgSet.t) (D : DepRel.t) : NSet.t :=
      NSet.union (SOpn.map fst R) (depNames D).

    Module SOnt := SetOps N T.Pkg NSet T.PkgSet.
    Definition absentPkgs (ns : NSet.t) : T.PkgSet.t :=
      SOnt.map (fun n => (Name.Orig n, Version.Bot)) ns.

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
           (T.PkgSet.union (varBlock Y_x) (absentPkgs (instNames R D)))).

    Module SOed := SetOps DepElt T.DepElt DepRel T.DepRel.
    Definition reduceDepsBy (Y_x : X.t -> YSet.t) (Vq : N.t -> VSet.t)
        (D : DepRel.t) : T.DepRel.t :=
      SOed.unionMap (fun '(p, f) => encodeNNF Y_x Vq (embedPkg p) f) D.

    Definition reduceDeps (Y_x : X.t -> YSet.t) (R : PkgSet.t) (D : DepRel.t)
      : T.DepRel.t :=
      reduceDepsBy Y_x (C.versions R) D.

    Lemma mem_idxSet : forall k w,
        T.VSet.In w (idxSet k) <-> exists i, i < k /\ w = Version.Idx i.
    Proof.
      intros k w; unfold idxSet;
        rewrite T.VSet.mem_ofList, in_map_iff.
      split.
      - intros [i [<- Hi]]; apply in_seq in Hi.
        exists i; split; [lia | reflexivity].
      - intros [i [Hi ->]]; exists i; split; [reflexivity |].
        apply in_seq; lia.
    Qed.

    Lemma mem_idxPkgs : forall n k y,
        T.PkgSet.In y (idxPkgs n k) <->
        exists i, i < k /\ y = (n, Version.Idx i).
    Proof.
      intros n k y; unfold idxPkgs;
        rewrite T.PkgSet.mem_ofList, in_map_iff.
      split.
      - intros [i [<- Hi]]; apply in_seq in Hi.
        exists i; split; [lia | reflexivity].
      - intros [i [Hi ->]]; exists i; split; [reflexivity |].
        apply in_seq; lia.
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

    Lemma mem_complementVS : forall Vq m vs (w : Version.t),
        T.VSet.In w (complementVS Vq m vs) <->
        w = Version.Bot \/
        exists u, VSet.In u (Vq m) /\ ~ VSet.In u vs /\ w = Version.Orig u.
    Proof.
      intros Vq m vs w; unfold complementVS.
      rewrite SOvv.add_in; unfold embedVS; rewrite SOvv.mem_map.
      split.
      - intros [-> | [u [Hu ->]]]; [left; reflexivity | right].
        apply VSet.diff_spec in Hu; destruct Hu as [Hu Hnv].
        exists u; auto.
      - intros [-> | [u [Hu [Hnv ->]]]]; [left; reflexivity | right].
        exists u; split; [| reflexivity].
        apply VSet.diff_spec; split; assumption.
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

    Lemma mem_depNames : forall D (n : N.t),
        NSet.In n (depNames D) <->
        exists p f, DepRel.In (p, f) D /\ NSet.In n (fnames f).
    Proof.
      intros D n; unfold depNames; rewrite SOen.mem_unionMap.
      split.
      - intros [[q g] [He Hn]]; exists q, g; split; [exact He | exact Hn].
      - intros [q [g [Hq Hn]]]; exists (q, g); split; [exact Hq | exact Hn].
    Qed.

    Lemma mem_instNames : forall R D (n : N.t),
        NSet.In n (instNames R D) <->
        (exists v, PkgSet.In (n, v) R) \/ NSet.In n (depNames D).
    Proof.
      intros R D n; unfold instNames.
      rewrite NSet.union_spec, SOpn.mem_map.
      split.
      - intros [[[m v] [HR Hm]] | H]; [simpl in Hm; subst | right; exact H].
        left; exists v; exact HR.
      - intros [[v HR] | H]; [| right; exact H].
        left; exists (n, v); split; [exact HR | reflexivity].
    Qed.

    Lemma mem_absentPkgs : forall ns (y : T.Pkg.t),
        T.PkgSet.In y (absentPkgs ns) <->
        exists n, NSet.In n ns /\ y = (Name.Orig n, Version.Bot).
    Proof. intros ns y; unfold absentPkgs; apply SOnt.mem_map. Qed.

    Lemma mem_reduceReal : forall Y_x R D (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal Y_x R D) <->
        (exists p, PkgSet.In p R /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\
                     T.PkgSet.In y (witnessSet (embedPkg p) f)) \/
        (exists x y',
            YSet.In y' (Y_x x) /\ y = (Name.Var x, Version.VarVal y')) \/
        (exists n, NSet.In n (instNames R D) /\ y = (Name.Orig n, Version.Bot)).
    Proof.
      intros Y_x R D y; unfold reduceReal.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap,
        mem_varBlock, mem_absentPkgs.
      split.
      - intros [H | [[[q g] [He Hy]] | [H | H]]];
          [left; exact H | | right; right; left; exact H
          | right; right; right; exact H].
        right; left; exists q, g; split; [exact He | exact Hy].
      - intros [H | [[q [g [Hd Hy]]] | [H | H]]];
          [left; exact H | | right; right; left; exact H
          | right; right; right; exact H].
        right; left; exists (q, g); split; [exact Hd | exact Hy].
    Qed.

    Lemma mem_reduceDepsBy : forall Y_x Vq D (d : T.DepElt.t),
        T.DepRel.In d (reduceDepsBy Y_x Vq D) <->
        exists p f, DepRel.In (p, f) D /\
                    T.DepRel.In d (encodeNNF Y_x Vq (embedPkg p) f).
    Proof.
      intros Y_x Vq D d; unfold reduceDepsBy; rewrite SOed.mem_unionMap.
      split.
      - intros [[q g] [He Hd]]; exists q, g; split; [exact He | exact Hd].
      - intros [q [g [Hq Hd]]]; exists (q, g); split; [exact Hq | exact Hd].
    Qed.

    Lemma mem_reduceDeps : forall Y_x R D (d : T.DepElt.t),
        T.DepRel.In d (reduceDeps Y_x R D) <->
        exists p f, DepRel.In (p, f) D /\
                    T.DepRel.In d (encodeNNF Y_x (C.versions R) (embedPkg p) f).
    Proof. intros Y_x R D d; apply mem_reduceDepsBy. Qed.

    Definition tryInvPkg (p' : T.Pkg.t) : option Pkg.t :=
      match p' with
      | (Name.Orig m, Version.Orig v) => Some (m, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [m v]; reflexivity. Qed.

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
    Definition assignCand (S : T.PkgSet.t) (x : X.t) : YSet.t :=
      SOty.filterMap (fun p' =>
          match p' with
          | (Name.Var x', Version.VarVal y) =>
              if X.eq_dec x' x then Some y else None
          | _ => None
          end)
        S.

    (* min_elt of the assigned-value candidates keeps the selector
       deterministic and computable; the domain's min is the fallback and y0
       the (unreachable under a nonempty domain) final case. *)
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

    Definition SyntheticName (n : Name.t) : Prop :=
      exists fs, n = Name.Disjunct fs.

    Lemma witnessSet_name_classify_aux : forall f : Formula,
        (forall (p : T.Pkg.t) (o : Name.t) (v : Version.t),
            T.PkgSet.In (o, v) (witnessSet p f) -> SyntheticName o) /\
        (forall (p : T.Pkg.t) (o : Name.t) (v : Version.t),
            T.PkgSet.In (o, v) (witnessSetNeg p f) -> SyntheticName o) /\
        (forall (n : Name.t) (i : nat) (o : Name.t) (v : Version.t),
            T.PkgSet.In (o, v) (witnessDisj n i f) -> SyntheticName o) /\
        (forall (n : Name.t) (i : nat) (o : Name.t) (v : Version.t),
            T.PkgSet.In (o, v) (witnessConjNeg n i f) -> SyntheticName o).
    Proof.
      unfold SyntheticName;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - repeat split; intros; exfalso; eapply SOpt.empty_in; eassumption.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
        + intros p o v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb1 _ _ _ H)].
        + intros p o v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply mem_idxPkgs in H; destruct H as [j [_ E]];
             injection E as -> _; eauto |].
          apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb4 _ _ _ _ H)].
        + intros n i o v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb1 _ _ _ H)].
        + intros n i o v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb4 _ _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
        + intros p o v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply mem_idxPkgs in H; destruct H as [j [_ E]];
             injection E as -> _; eauto |].
          apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb3 _ _ _ _ H)].
        + intros p o v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb2 _ _ _ H)].
        + intros n i o v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb3 _ _ _ _ H)].
        + intros n i o v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb2 _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
        + intros p o v H; exact (IHa2 _ _ _ H).
        + intros p o v H; exact (IHa1 _ _ _ H).
        + intros n i o v H; exact (IHa2 _ _ _ H).
        + intros n i o v H; exact (IHa1 _ _ _ H).
      - repeat split; intros; exfalso; eapply SOpt.empty_in; eassumption.
    Qed.

    Lemma witnessSet_not_orig : forall (p : T.Pkg.t) (f : Formula) m v,
        ~ T.PkgSet.In (Name.Orig m, v) (witnessSet p f).
    Proof.
      intros p f m v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H) as [fs E];
        discriminate.
    Qed.

    Lemma witnessSet_not_var : forall (p : T.Pkg.t) (f : Formula) x v,
        ~ T.PkgSet.In (Name.Var x, v) (witnessSet p f).
    Proof.
      intros p f x v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H) as [fs E];
        discriminate.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall Y_x (p : Pkg.t) R D,
        T.PkgSet.In (embedPkg p) (reduceReal Y_x R D) -> PkgSet.In p R.
    Proof.
      intros Y_x [pn pv] R D H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [[q [g [_ Hy]]] | [[x [y' [_ Hy]]] | [n [_ Hy]]]]].
      - apply embedPkg_injective in Hq as ->; exact HqR.
      - exfalso; exact (witnessSet_not_orig _ _ _ _ Hy).
      - unfold embedPkg in Hy; discriminate.
      - unfold embedPkg in Hy; discriminate.
    Qed.

    Lemma mem_assignCand : forall S x y,
        YSet.In y (assignCand S x) <->
        T.PkgSet.In (Name.Var x, Version.VarVal y) S.
    Proof.
      intros S x y; unfold assignCand; rewrite SOty.mem_filterMap.
      split.
      - intros [[[n' | x' | fs] [v' | i | y' | ]] [Hp' Hin]];
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
        destruct E as [[q [_ Hq]] | [[q [g [_ Hy]]] | [[x' [y'' [Hy'' Hq]]] | [n [_ Hq]]]]].
        + destruct q as [qn qv]; unfold embedPkg in Hq; discriminate.
        + exfalso; exact (witnessSet_not_var _ _ _ _ Hy).
        + injection Hq as Ex Ey; subst; exact Hy''.
        + discriminate Hq.
      - destruct (YSet.min_elt (Y_x x)) as [y1 |] eqn:E2.
        + apply YSet.min_elt_spec1 in E2; exact E2.
        + exfalso; apply YSet.min_elt_spec3 in E2.
          destruct (Hne x) as [y1 Hy1]; exact (E2 y1 Hy1).
    Qed.

    Lemma encodeNNF_satisfies : forall (R : T.PkgSet.t) (D : T.DepRel.t)
                                    (r : T.Pkg.t) (S : T.PkgSet.t),
        T.IsResolution R D r S ->
        forall y0 Y_x (Vq : N.t -> VSet.t),
          (forall x, exists y, YSet.In y (Y_x x)) ->
          forall (q : T.Pkg.t) (f : Formula),
            (forall d, T.DepRel.In d (encodeNNF Y_x Vq q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S ->
            Satisfies (variableFormulaResolution S)
              (extractAssignment y0 Y_x S) f.
    Proof.
      intros R D r S Hres y0 Y_x Vq Hne;
        destruct Hres as [Hsub Hroot Hdep Huniq].
      cut (forall f : Formula,
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNF Y_x Vq q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S ->
            Satisfies (variableFormulaResolution S)
              (extractAssignment y0 Y_x S) f) /\
        (forall q : T.Pkg.t,
            (forall d,
                T.DepRel.In d (encodeNNFneg Y_x Vq q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S ->
            ~ Satisfies (variableFormulaResolution S)
                (extractAssignment y0 Y_x S) f) /\
        (forall (n : Name.t) (i0 i : nat),
            (forall d,
                T.DepRel.In d (encodeDisj Y_x Vq n i0 f) -> T.DepRel.In d D) ->
            T.PkgSet.In (n, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (disjSpine f) ->
            Satisfies (variableFormulaResolution S)
              (extractAssignment y0 Y_x S) f) /\
        (forall (n : Name.t) (i0 i : nat),
            (forall d,
                T.DepRel.In d (encodeConjNeg Y_x Vq n i0 f) -> T.DepRel.In d D) ->
            T.PkgSet.In (n, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (negConjSpine f) ->
            ~ Satisfies (variableFormulaResolution S)
                (extractAssignment y0 Y_x S) f)).
      { intros H q f; exact (proj1 (H f) q). }
      assert (Hpos : forall (q : T.Pkg.t) m vs,
                 T.DepRel.In (q, (Name.Orig m, embedVS vs)) D ->
                 T.PkgSet.In q S ->
                 Satisfies (variableFormulaResolution S)
                   (extractAssignment y0 Y_x S) (FDep m vs)).
      { intros q m vs Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        unfold embedVS in Hw; apply SOvv.mem_map in Hw;
          destruct Hw as [v [Hv ->]].
        exists v; split; [exact Hv |].
        apply mem_variableFormulaResolution; exact HwS. }
      assert (Hneg : forall (q : T.Pkg.t) m vs,
                 T.DepRel.In (q, (Name.Orig m, complementVS Vq m vs)) D ->
                 T.PkgSet.In q S ->
                 ~ Satisfies (variableFormulaResolution S)
                     (extractAssignment y0 Y_x S) (FDep m vs)).
      { intros q m vs Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        intros [v [Hv HvS]].
        apply mem_variableFormulaResolution in HvS.
        assert (E := Huniq _ _ _ HwS HvS); subst w.
        apply mem_complementVS in Hw.
        destruct Hw as [Hw | [u [_ [Hnv E]]]]; [discriminate Hw |].
        injection E as <-; exact (Hnv Hv). }
      assert (Hvar : forall (q : T.Pkg.t) x op y,
                 T.DepRel.In (q, (Name.Var x, cmpVersionSet (Y_x x) op y)) D ->
                 T.PkgSet.In q S ->
                 opEvalY op (extractAssignment y0 Y_x S x) y = true).
      { intros q x op y Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        apply mem_cmpVersionSet in Hw; destruct Hw as [y' [Hy' [HE ->]]].
        rewrite (extractAssignment_var_det y0 Y_x S x y' Huniq HwS); exact HE. }
      induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v.
        + intros q Henc HqS; apply (Hpos q); [| exact HqS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros q Henc HqS; apply (Hneg q m vs); [| exact HqS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          apply (Hpos (n, Version.Idx i0)); [| exact HiS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          apply (Hneg (n, Version.Idx i0) m vs); [| exact HiS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros q Henc HqS; simpl; split.
          * apply (IHa1 q); [| exact HqS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * apply (IHb1 q); [| exact HqS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros q Henc HqS; simpl.
          set (n := Name.Disjunct (FNeg a :: negConjSpine b)).
          assert (Hd : T.DepRel.In
                    (q, (n, idxSet
                           (List.length (FNeg a :: negConjSpine b)))) D).
          { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
          destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
          apply mem_idxSet in Hw; destruct Hw as [i [Hi ->]].
          simpl in Hi; intros [HsatA HsatB].
          destruct i as [| i'].
          * refine (IHa2 (n, Version.Idx 0) _ HwS HsatA).
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; left; exact Hd'.
          * refine (IHb4 n 1 (Datatypes.S i') _ HwS _ _ HsatB);
              [| lia | simpl; lia].
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; right; exact Hd'.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; split.
          * apply (IHa1 (n, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * apply (IHb1 (n, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt; simpl.
          intros [HsatA HsatB].
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne'].
          * refine (IHa2 (n, Version.Idx i0) _ HiS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb4 n (Datatypes.S i0) i _ HiS _ _ HsatB); [| lia | lia].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros q Henc HqS; simpl.
          set (n := Name.Disjunct (a :: disjSpine b)).
          assert (Hd : T.DepRel.In
                    (q, (n, idxSet (List.length (a :: disjSpine b)))) D).
          { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
          destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
          apply mem_idxSet in Hw; destruct Hw as [i [Hi ->]].
          simpl in Hi; destruct i as [| i'].
          * left; apply (IHa1 (n, Version.Idx 0)); [| exact HwS].
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; left; exact Hd'.
          * right; refine (IHb3 n 1 (Datatypes.S i') _ HwS _ _);
              [| lia | simpl; lia].
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; right; exact Hd'.
        + intros q Henc HqS; simpl; intros [HsatA | HsatB].
          * refine (IHa2 q _ HqS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb2 q _ HqS HsatB).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt; simpl.
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne'].
          * left; apply (IHa1 (n, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * right; refine (IHb3 n (Datatypes.S i0) i _ HiS _ _); [| lia | lia].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; intros [HsatA | HsatB].
          * refine (IHa2 (n, Version.Idx i0) _ HiS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb2 (n, Version.Idx i0) _ HiS HsatB).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
        + intros q Henc HqS; exact (IHa2 q Henc HqS).
        + intros q Henc HqS; simpl; intro Hn; exact (Hn (IHa1 q Henc HqS)).
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          exact (IHa2 (n, Version.Idx i0) Henc HiS).
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; intro Hn.
          exact (Hn (IHa1 (n, Version.Idx i0) Henc HiS)).
      - split4v.
        + intros q Henc HqS; simpl; apply (Hvar q x op y); [| exact HqS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros q Henc HqS; simpl.
          assert (E : opEvalY (cmpComplement op)
                        (extractAssignment y0 Y_x S x) y = true).
          { apply (Hvar q x (cmpComplement op) y); [| exact HqS].
            apply Henc; simpl; apply SOed.singleton_in; reflexivity. }
          rewrite opEvalY_complement in E; apply Bool.negb_true_iff in E.
          intro HC; congruence.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl.
          apply (Hvar (n, Version.Idx i0) x op y); [| exact HiS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl.
          assert (E : opEvalY (cmpComplement op)
                        (extractAssignment y0 Y_x S x) y = true).
          { apply (Hvar (n, Version.Idx i0) x (cmpComplement op) y);
              [| exact HiS].
            apply Henc; simpl; apply SOed.singleton_in; reflexivity. }
          rewrite opEvalY_complement in E; apply Bool.negb_true_iff in E.
          intro HC; congruence.
    Qed.

    Theorem variable_formula_soundness :
      forall (y0 : Y.t) (Y_x : X.t -> YSet.t),
        (forall x, exists y, YSet.In y (Y_x x)) ->
        forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : T.PkgSet.t),
          T.IsResolution (reduceReal Y_x R D) (reduceDeps Y_x R D)
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
          apply (encodeNNF_satisfies _ _ _ _ Hres y0 Y_x (C.versions R) Hne
                   (embedPkg p) f);
            [| exact Hp].
          intros d Hd; apply mem_reduceDeps; exists p, f;
            split; [exact Hdf | exact Hd].
        + intros m v v' Hv Hv'.
          apply mem_variableFormulaResolution in Hv, Hv'.
          unfold embedPkg in Hv, Hv'; simpl in Hv, Hv'.
          assert (E := Huniq _ _ _ Hv Hv').
          injection E as E; exact E.
      - exact (extractAssignment_mem y0 Y_x R D S Hne Hsub).
    Qed.

    Fixpoint firstSatIdx (Sv : PkgSet.t) (sigma : X.t -> Y.t)
        (fs : list Formula) : nat :=
      match fs with
      | nil => 0
      | _ :: nil => 0
      | g :: fs' =>
          if satisfiesb Sv sigma g then 0
          else Datatypes.S (firstSatIdx Sv sigma fs')
      end.

    Fixpoint witnessSetTaken (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
        T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetTaken S sigma a) (witnessSetTaken S sigma b)
      | FDisj a b =>
          T.PkgSet.add
            (Name.Disjunct (a :: disjSpine b),
             Version.Idx (firstSatIdx S sigma (a :: disjSpine b)))
            (if satisfiesb S sigma a then witnessSetTaken S sigma a
             else takenDisj S sigma b)
      | FNeg a => witnessSetTakenNeg S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with takenDisj (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
        T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetTaken S sigma a) (witnessSetTaken S sigma b)
      | FDisj a b =>
          if satisfiesb S sigma a then witnessSetTaken S sigma a
          else takenDisj S sigma b
      | FNeg a => witnessSetTakenNeg S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessSetTakenNeg (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
        T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.add
            (Name.Disjunct (FNeg a :: negConjSpine b),
             Version.Idx (firstSatIdx S sigma (FNeg a :: negConjSpine b)))
            (if satisfiesb S sigma a then takenConjNeg S sigma b
             else witnessSetTakenNeg S sigma a)
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S sigma a)
            (witnessSetTakenNeg S sigma b)
      | FNeg a => witnessSetTaken S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with takenConjNeg (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
        T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          if satisfiesb S sigma a then takenConjNeg S sigma b
          else witnessSetTakenNeg S sigma a
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S sigma a)
            (witnessSetTakenNeg S sigma b)
      | FNeg a => witnessSetTaken S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end.

    Lemma witnessSetTaken_disj_eq : forall S sigma a b,
        witnessSetTaken S sigma (FDisj a b) =
        T.PkgSet.add
          (Name.Disjunct (a :: disjSpine b),
           Version.Idx (firstSatIdx S sigma (a :: disjSpine b)))
          (takenDisj S sigma (FDisj a b)).
    Proof. reflexivity. Qed.

    Lemma witnessSetTakenNeg_conj_eq : forall S sigma a b,
        witnessSetTakenNeg S sigma (FConj a b) =
        T.PkgSet.add
          (Name.Disjunct (FNeg a :: negConjSpine b),
           Version.Idx (firstSatIdx S sigma (FNeg a :: negConjSpine b)))
          (takenConjNeg S sigma (FConj a b)).
    Proof. reflexivity. Qed.

    Lemma takenDisj_disj_eq : forall S sigma a b,
        takenDisj S sigma (FDisj a b) =
        (if satisfiesb S sigma a then witnessSetTaken S sigma a
         else takenDisj S sigma b).
    Proof. reflexivity. Qed.

    Lemma takenConjNeg_conj_eq : forall S sigma a b,
        takenConjNeg S sigma (FConj a b) =
        (if satisfiesb S sigma a then takenConjNeg S sigma b
         else witnessSetTakenNeg S sigma a).
    Proof. reflexivity. Qed.

    Lemma firstSatIdx_lt : forall S sigma fs,
        fs <> nil -> firstSatIdx S sigma fs < List.length fs.
    Proof.
      intros S sigma fs; induction fs as [| g fs IH]; intro Hne.
      - contradiction Hne; reflexivity.
      - destruct fs as [| h t]; [simpl; lia |].
        change (firstSatIdx S sigma (g :: h :: t))
          with (if satisfiesb S sigma g then 0
                else Datatypes.S (firstSatIdx S sigma (h :: t))).
        assert (Hlt : firstSatIdx S sigma (h :: t) < List.length (h :: t))
          by (apply IH; discriminate).
        destruct (satisfiesb S sigma g); simpl List.length in *; lia.
    Qed.

    Lemma disjSpine_nonnil : forall f, disjSpine f <> nil.
    Proof. intro f; destruct f; simpl; discriminate. Qed.

    Lemma negConjSpine_nonnil : forall f, negConjSpine f <> nil.
    Proof. intro f; destruct f; simpl; discriminate. Qed.

    Lemma firstSatIdx_cons : forall S sigma g fs,
        fs <> nil ->
        firstSatIdx S sigma (g :: fs) =
        (if satisfiesb S sigma g then 0
         else Datatypes.S (firstSatIdx S sigma fs)).
    Proof.
      intros S sigma g [| h t] Hne;
        [contradiction Hne; reflexivity | reflexivity].
    Qed.

    Lemma takenDisj_firstSat : forall S sigma f,
        Satisfies S sigma f ->
        exists g,
          List.nth_error (disjSpine f) (firstSatIdx S sigma (disjSpine f))
          = Some g /\
          Satisfies S sigma g /\
          T.PkgSet.Subset (witnessSetTaken S sigma g) (takenDisj S sigma f).
    Proof.
      intros S sigma f;
        induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros y' Hy'; exact Hy']).
      cbn [disjSpine];
        rewrite (firstSatIdx_cons S sigma a (disjSpine b) (disjSpine_nonnil b)).
      destruct (satisfiesb S sigma a) eqn:Ea.
      - exists a; split; [reflexivity |]; split;
          [apply satisfiesb_iff; exact Ea |].
        intros y' Hy'; simpl; rewrite Ea; exact Hy'.
      - assert (Hb : Satisfies S sigma b).
        { destruct Hsat as [Ha | Hb]; [| exact Hb].
          exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
        destruct (IHb Hb) as [g [Hg [Hsg Hsub]]].
        exists g; split; [exact Hg |]; split; [exact Hsg |].
        intros y' Hy'; simpl; rewrite Ea; exact (Hsub y' Hy').
    Qed.

    Lemma takenConjNeg_firstSat : forall S sigma f,
        ~ Satisfies S sigma f ->
        exists g,
          List.nth_error (negConjSpine f)
            (firstSatIdx S sigma (negConjSpine f)) = Some g /\
          Satisfies S sigma g /\
          T.PkgSet.Subset (witnessSetTaken S sigma g) (takenConjNeg S sigma f).
    Proof.
      intros S sigma f;
        induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros y' Hy'; exact Hy']).
      cbn [negConjSpine];
        rewrite (firstSatIdx_cons S sigma (FNeg a) (negConjSpine b)
                   (negConjSpine_nonnil b)).
      destruct (satisfiesb S sigma a) eqn:Ea.
      - assert (Hb : ~ Satisfies S sigma b).
        { intro Hb; apply Hsat; split;
            [apply satisfiesb_iff; exact Ea | exact Hb]. }
        destruct (IHb Hb) as [g [Hg [Hsg Hsub]]].
        exists g; split;
          [change (satisfiesb S sigma (FNeg a))
             with (negb (satisfiesb S sigma a));
           rewrite Ea; exact Hg |]; split; [exact Hsg |].
        intros y' Hy'; simpl; rewrite Ea; exact (Hsub y' Hy').
      - exists (FNeg a); split;
          [change (satisfiesb S sigma (FNeg a))
             with (negb (satisfiesb S sigma a));
           rewrite Ea; reflexivity |]; split;
          [apply satisfiesb_false_iff; exact Ea |].
        intros y' Hy'; simpl; rewrite Ea; exact Hy'.
    Qed.

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
        cbn [fst]; destruct (N.eq_dec n n) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
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

    Definition sigmaBlock (sigma : X.t -> Y.t) : T.PkgSet.t :=
      List.fold_right (fun x acc =>
          T.PkgSet.add (Name.Var x, Version.VarVal (sigma x)) acc)
        T.PkgSet.empty X.enum.

    Definition coreResolution (S : PkgSet.t) (R : PkgSet.t) (D : DepRel.t)
        (sigma : X.t -> Y.t) : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg S)
        (T.PkgSet.union
           (SOet.unionMap (fun '(p, f) =>
                if PkgSet.mem p S then witnessSetTaken S sigma f
                else T.PkgSet.empty)
              D)
           (T.PkgSet.union (sigmaBlock sigma)
              (absentPkgs (absentIn S (instNames R D))))).

    Lemma witnessSetTaken_subset_witnessSet_aux : forall S sigma f,
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTaken S sigma f) (witnessSet p f)) /\
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTakenNeg S sigma f) (witnessSetNeg p f)) /\
        (forall (n : Name.t) (i : nat),
            T.PkgSet.Subset (takenDisj S sigma f) (witnessDisj n i f)) /\
        (forall (n : Name.t) (i : nat),
            T.PkgSet.Subset (takenConjNeg S sigma f) (witnessConjNeg n i f)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v; intros; intros y H; exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 p _ H) | right; exact (IHb1 p _ H)].
        + intros p y; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; simpl witnessSetNeg;
            apply T.PkgSet.union_spec.
          destruct H as [-> | H].
          * left; apply mem_idxPkgs;
              exists (firstSatIdx S sigma (FNeg a :: negConjSpine b));
              split; [apply firstSatIdx_lt; discriminate | reflexivity].
          * right; revert H; rewrite takenConjNeg_conj_eq;
              destruct (satisfiesb S sigma a); intro H;
              apply T.PkgSet.union_spec;
              [right; exact (IHb4 _ _ _ H) | left; exact (IHa2 _ _ H)].
        + intros n i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb1 _ _ H)].
        + intros n i y; rewrite takenConjNeg_conj_eq; simpl witnessConjNeg;
            destruct (satisfiesb S sigma a); intro H;
            apply T.PkgSet.union_spec;
            [right; exact (IHb4 _ _ _ H) | left; exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros p y; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; simpl witnessSet;
            apply T.PkgSet.union_spec.
          destruct H as [-> | H].
          * left; apply mem_idxPkgs;
              exists (firstSatIdx S sigma (a :: disjSpine b));
              split; [apply firstSatIdx_lt; discriminate | reflexivity].
          * right; revert H; rewrite takenDisj_disj_eq;
              destruct (satisfiesb S sigma a); intro H;
              apply T.PkgSet.union_spec;
              [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 p _ H) | right; exact (IHb2 p _ H)].
        + intros n i y; rewrite takenDisj_disj_eq; simpl witnessDisj;
            destruct (satisfiesb S sigma a); intro H;
            apply T.PkgSet.union_spec;
            [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros n i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
        + intros p y; exact (IHa2 p y).
        + intros p y; exact (IHa1 p y).
        + intros n i y; exact (IHa2 _ y).
        + intros n i y; exact (IHa1 _ y).
      - split4v; intros; intros y' H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_subset_witnessSet : forall S sigma (p : T.Pkg.t) f,
        T.PkgSet.Subset (witnessSetTaken S sigma f) (witnessSet p f).
    Proof.
      intros S sigma p f;
        exact (proj1 (witnessSetTaken_subset_witnessSet_aux S sigma f) p).
    Qed.

    Lemma witnessSetTaken_disjunct_det_aux : forall S sigma f,
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (witnessSetTaken S sigma f) ->
            v = Version.Idx (firstSatIdx S sigma fs)) /\
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (witnessSetTakenNeg S sigma f) ->
            v = Version.Idx (firstSatIdx S sigma fs)) /\
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (takenDisj S sigma f) ->
            v = Version.Idx (firstSatIdx S sigma fs)) /\
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (takenConjNeg S sigma f) ->
            v = Version.Idx (firstSatIdx S sigma fs)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v; intros fs v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros fs v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; rewrite takenConjNeg_conj_eq; destruct (satisfiesb S sigma a);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros fs v; rewrite takenConjNeg_conj_eq;
            destruct (satisfiesb S sigma a);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros fs v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; rewrite takenDisj_disj_eq; destruct (satisfiesb S sigma a);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros fs v; rewrite takenDisj_disj_eq; destruct (satisfiesb S sigma a);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v;
          intros fs v; [exact (IHa2 fs v) | exact (IHa1 fs v)
                       | exact (IHa2 fs v) | exact (IHa1 fs v)].
      - split4v; intros fs v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_disjunct_det : forall S sigma f fs v,
        T.PkgSet.In (Name.Disjunct fs, v) (witnessSetTaken S sigma f) ->
        v = Version.Idx (firstSatIdx S sigma fs).
    Proof.
      intros S sigma f;
        exact (proj1 (witnessSetTaken_disjunct_det_aux S sigma f)).
    Qed.

    Lemma witnessSetTaken_name_classify_aux : forall S sigma f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTaken S sigma f) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTakenNeg S sigma f) ->
            SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (takenDisj S sigma f) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (takenConjNeg S sigma f) -> SyntheticName n).
    Proof.
      unfold SyntheticName; intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v; intros n v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; eauto |].
          revert H; rewrite takenConjNeg_conj_eq; destruct (satisfiesb S sigma a);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; rewrite takenConjNeg_conj_eq;
            destruct (satisfiesb S sigma a);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros n v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; eauto |].
          revert H; rewrite takenDisj_disj_eq; destruct (satisfiesb S sigma a);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros n v; rewrite takenDisj_disj_eq; destruct (satisfiesb S sigma a);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v; intros n v;
          [exact (IHa2 n v) | exact (IHa1 n v)
          | exact (IHa2 n v) | exact (IHa1 n v)].
      - split4v; intros n v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_not_orig : forall S sigma f m v,
        ~ T.PkgSet.In (Name.Orig m, v) (witnessSetTaken S sigma f).
    Proof.
      intros S sigma f m v H.
      destruct (proj1 (witnessSetTaken_name_classify_aux S sigma f) _ _ H)
        as [fs E]; discriminate.
    Qed.

    Lemma witnessSetTaken_not_var : forall S sigma f x v,
        ~ T.PkgSet.In (Name.Var x, v) (witnessSetTaken S sigma f).
    Proof.
      intros S sigma f x v H.
      destruct (proj1 (witnessSetTaken_name_classify_aux S sigma f) _ _ H)
        as [fs E]; discriminate.
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

    Lemma mem_coreResolution : forall S R D sigma (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution S R D sigma) <->
        (exists p, PkgSet.In p S /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\ PkgSet.In p S /\
                     T.PkgSet.In y (witnessSetTaken S sigma f)) \/
        (exists x, y = (Name.Var x, Version.VarVal (sigma x))) \/
        (exists n, NSet.In n (instNames R D) /\
                   (forall v, ~ PkgSet.In (n, v) S) /\
                   y = (Name.Orig n, Version.Bot)).
    Proof.
      intros S R D sigma y; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap,
        mem_sigmaBlock, mem_absentPkgs.
      split.
      - intros [H | [[[q g] [He Hy]] | [H | [n [Hn ->]]]]];
          [left; exact H | | right; right; left; exact H |].
        + right; left; cbn beta iota in Hy.
          destruct (PkgSet.mem q S) eqn:E;
            [| exfalso; exact (SOpt.empty_in _ Hy)].
          exists q, g; split; [exact He |];
            split; [apply PkgSet.mem_spec; exact E | exact Hy].
        + right; right; right; apply mem_absentIn in Hn;
            destruct Hn as [Hn Hnone].
          exists n; auto.
      - intros [H | [[q [g [Hd [HqS Hy]]]] | [H | [n [Hn [Hnone ->]]]]]];
          [left; exact H | | right; right; left; exact H |].
        + right; left; exists (q, g); split; [exact Hd |].
          apply PkgSet.mem_spec in HqS; cbn beta iota; rewrite HqS; exact Hy.
        + right; right; right; exists n; split; [| reflexivity].
          apply mem_absentIn; auto.
    Qed.

    Lemma witnessSetTaken_subset_coreResolution : forall S R D sigma p f,
        DepRel.In (p, f) D -> PkgSet.In p S ->
        T.PkgSet.Subset (witnessSetTaken S sigma f) (coreResolution S R D sigma).
    Proof.
      intros S R D sigma p f Hd HpS y Hy; apply mem_coreResolution; right; left.
      exists p, f; auto.
    Qed.

    Ltac pick_alt H nav :=
      let g0 := fresh "g0" in let Hg0 := fresh "Hg0" in
      let Hs0 := fresh "Hs0" in let Hu0 := fresh "Hu0" in
      destruct H as [g0 [Hg0 [Hs0 Hu0]]];
      exists g0; split; [exact Hg0 |]; split; [exact Hs0 |];
      let y0 := fresh "y0" in let Hy0 := fresh "Hy0" in
      intros y0 Hy0; nav; exact (Hu0 y0 Hy0).

    Lemma witnessSetTaken_disj_mono_aux : forall S sigma f,
        (Satisfies S sigma f ->
         forall fs i,
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i)
             (witnessSetTaken S sigma f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
             T.PkgSet.Subset (witnessSetTaken S sigma g)
               (witnessSetTaken S sigma f)) /\
        (~ Satisfies S sigma f ->
         forall fs i,
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i)
             (witnessSetTakenNeg S sigma f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
             T.PkgSet.Subset (witnessSetTaken S sigma g)
               (witnessSetTakenNeg S sigma f)) /\
        (Satisfies S sigma f ->
         forall fs i,
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i) (takenDisj S sigma f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
             T.PkgSet.Subset (witnessSetTaken S sigma g) (takenDisj S sigma f)) /\
        (~ Satisfies S sigma f ->
         forall fs i,
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i)
             (takenConjNeg S sigma f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
             T.PkgSet.Subset (witnessSetTaken S sigma g)
               (takenConjNeg S sigma f)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v; intros Hyp fs i; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [pick_alt (IHa1 (proj1 Hyp) _ _ H)
               ltac:(apply T.PkgSet.union_spec; left)
            | pick_alt (IHb1 (proj2 Hyp) _ _ H)
                ltac:(apply T.PkgSet.union_spec; right)].
        + intros Hyp fs i; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H].
          * injection H as -> ->;
              pick_alt (takenConjNeg_firstSat S sigma (FConj a b) Hyp)
                ltac:(apply SOpt.add_in; right).
          * revert H; rewrite takenConjNeg_conj_eq;
              destruct (satisfiesb S sigma a) eqn:Ea; intro H.
            -- assert (Hb : ~ Satisfies S sigma b).
               { intro Hb; apply Hyp; split;
                   [apply satisfiesb_iff; exact Ea | exact Hb]. }
               pick_alt (IHb4 Hb _ _ H) ltac:(apply SOpt.add_in; right).
            -- pick_alt (IHa2 (proj1 (satisfiesb_false_iff S sigma a) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [pick_alt (IHa1 (proj1 Hyp) _ _ H)
               ltac:(apply T.PkgSet.union_spec; left)
            | pick_alt (IHb1 (proj2 Hyp) _ _ H)
                ltac:(apply T.PkgSet.union_spec; right)].
        + intros Hyp fs i; rewrite takenConjNeg_conj_eq;
            destruct (satisfiesb S sigma a) eqn:Ea; intro H.
          * assert (Hb : ~ Satisfies S sigma b).
            { intro Hb; apply Hyp; split;
                [apply satisfiesb_iff; exact Ea | exact Hb]. }
            pick_alt (IHb4 Hb _ _ H) ltac:(idtac).
          * pick_alt (IHa2 (proj1 (satisfiesb_false_iff S sigma a) Ea) _ _ H)
              ltac:(idtac).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros Hyp fs i; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H].
          * injection H as -> ->;
              pick_alt (takenDisj_firstSat S sigma (FDisj a b) Hyp)
                ltac:(apply SOpt.add_in; right).
          * revert H; rewrite takenDisj_disj_eq;
              destruct (satisfiesb S sigma a) eqn:Ea; intro H.
            -- pick_alt (IHa1 (proj1 (satisfiesb_iff S sigma a) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right).
            -- assert (Hb : Satisfies S sigma b).
               { destruct Hyp as [Ha | Hb]; [| exact Hb].
                 exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
               pick_alt (IHb3 Hb _ _ H) ltac:(apply SOpt.add_in; right).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa2 (fun Ha => Hyp (or_introl Ha)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * pick_alt (IHb2 (fun Hb => Hyp (or_intror Hb)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
        + intros Hyp fs i; rewrite takenDisj_disj_eq;
            destruct (satisfiesb S sigma a) eqn:Ea; intro H.
          * pick_alt (IHa1 (proj1 (satisfiesb_iff S sigma a) Ea) _ _ H)
              ltac:(idtac).
          * assert (Hb : Satisfies S sigma b).
            { destruct Hyp as [Ha | Hb]; [| exact Hb].
              exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
            pick_alt (IHb3 Hb _ _ H) ltac:(idtac).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa2 (fun Ha => Hyp (or_introl Ha)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * pick_alt (IHb2 (fun Hb => Hyp (or_intror Hb)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v; intros Hyp fs i.
        + exact (IHa2 Hyp fs i).
        + exact (IHa1 (satisfies_double_neg S sigma a Hyp) fs i).
        + exact (IHa2 Hyp fs i).
        + exact (IHa1 (satisfies_double_neg S sigma a Hyp) fs i).
      - split4v; intros Hyp fs i; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma coreResolution_disj : forall S R D sigma fs i,
        (forall p, PkgSet.In p S ->
         forall f, DepRel.In (p, f) D -> Satisfies S sigma f) ->
        T.PkgSet.In (Name.Disjunct fs, Version.Idx i)
          (coreResolution S R D sigma) ->
        exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
          T.PkgSet.Subset (witnessSetTaken S sigma g) (coreResolution S R D sigma).
    Proof.
      intros S R D sigma fs i Hclo H; apply mem_coreResolution in H.
      destruct H as [[p [_ Hp]] | [[p [g [Hd [HpS Hw]]]] | [[x Hx] | [n [_ [_ Hn]]]]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - assert (Hsat : Satisfies S sigma g) by exact (Hclo p HpS g Hd).
        destruct (proj1 (witnessSetTaken_disj_mono_aux S sigma g) Hsat fs i Hw)
          as [h [Hh [Hsh Hsubh]]].
        exists h; split; [exact Hh |]; split; [exact Hsh |].
        intros y Hy;
          apply (witnessSetTaken_subset_coreResolution S R D sigma p g Hd HpS),
            Hsubh; exact Hy.
      - discriminate Hx.
      - discriminate Hn.
    Qed.

    Lemma encodeNNF_dep_closure_aux :
      forall (S : PkgSet.t) (sigma : X.t -> Y.t) (Y_x : X.t -> YSet.t)
             (Vq : N.t -> VSet.t) (Ns : NSet.t) (w : T.PkgSet.t),
        (forall x, YSet.In (sigma x) (Y_x x)) ->
        (forall p, PkgSet.In p S -> T.PkgSet.In (embedPkg p) w) ->
        (forall m u, PkgSet.In (m, u) S -> VSet.In u (Vq m)) ->
        (forall m, NSet.In m Ns -> (forall u, ~ PkgSet.In (m, u) S) ->
           T.PkgSet.In (Name.Orig m, Version.Bot) w) ->
        (forall fs i, T.PkgSet.In (Name.Disjunct fs, Version.Idx i) w ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
             T.PkgSet.Subset (witnessSetTaken S sigma g) w) ->
        (forall x, T.PkgSet.In (Name.Var x, Version.VarVal (sigma x)) w) ->
        forall f : Formula,
          NSet.Subset (fnames f) Ns ->
          (forall q0 : T.Pkg.t,
              ~ T.PkgSet.In q0 w \/
              (Satisfies S sigma f /\
               T.PkgSet.Subset (witnessSetTaken S sigma f) w) ->
              forall (q : T.Pkg.t) (o : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (o, ws)) (encodeNNF Y_x Vq q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (o, v) w) /\
          (forall q0 : T.Pkg.t,
              ~ T.PkgSet.In q0 w \/
              (~ Satisfies S sigma f /\
               T.PkgSet.Subset (witnessSetTakenNeg S sigma f) w) ->
              forall (q : T.Pkg.t) (o : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (o, ws)) (encodeNNFneg Y_x Vq q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (o, v) w) /\
          (forall (n : Name.t) (i0 : nat),
              (forall k g, List.nth_error (disjSpine f) k = Some g ->
                 ~ T.PkgSet.In (n, Version.Idx (i0 + k)) w \/
                 (Satisfies S sigma g /\
                  T.PkgSet.Subset (witnessSetTaken S sigma g) w)) ->
              forall (q : T.Pkg.t) (o : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (o, ws)) (encodeDisj Y_x Vq n i0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (o, v) w) /\
          (forall (n : Name.t) (i0 : nat),
              (forall k g, List.nth_error (negConjSpine f) k = Some g ->
                 ~ T.PkgSet.In (n, Version.Idx (i0 + k)) w \/
                 (Satisfies S sigma g /\
                  T.PkgSet.Subset (witnessSetTaken S sigma g) w)) ->
              forall (q : T.Pkg.t) (o : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (o, ws)) (encodeConjNeg Y_x Vq n i0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (o, v) w).
    Proof.
      intros S sigma Y_x Vq Ns w Hins Hemb HVq Hbot Hdisj Hvar f.
      assert (Hneg : forall m vs,
                 NSet.In m Ns ->
                 ~ Satisfies S sigma (FDep m vs) ->
                 exists v, T.VSet.In v (complementVS Vq m vs) /\
                           T.PkgSet.In (Name.Orig m, v) w).
      { intros m vs Hm Hns.
        destruct (hasNameb S m) eqn:E.
        - apply hasNameb_true in E; destruct E as [u Hu].
          exists (Version.Orig u); split; [| exact (Hemb (m, u) Hu)].
          apply mem_complementVS; right; exists u.
          split; [exact (HVq m u Hu) | split; [| reflexivity]].
          intro Huv; apply Hns; exists u; auto.
        - assert (Hnone := proj1 (hasNameb_false S m) E).
          exists Version.Bot; split; [apply mem_complementVS; left; reflexivity |].
          exact (Hbot m Hm Hnone). }
      assert (Hcmp : forall x op y,
                 Satisfies S sigma (FVarCmp x op y) ->
                 exists v, T.VSet.In v (cmpVersionSet (Y_x x) op y) /\
                           T.PkgSet.In (Name.Var x, v) w).
      { intros x op y Hs; cbn [Satisfies] in Hs.
        exists (Version.VarVal (sigma x)); split; [| exact (Hvar x)].
        apply mem_cmpVersionSet; exists (sigma x); auto. }
      assert (Hcmpn : forall x op y,
                 ~ Satisfies S sigma (FVarCmp x op y) ->
                 exists v, T.VSet.In v (cmpVersionSet (Y_x x) (cmpComplement op) y)
                           /\ T.PkgSet.In (Name.Var x, v) w).
      { intros x op y Hs; cbn [Satisfies] in Hs.
        exists (Version.VarVal (sigma x)); split; [| exact (Hvar x)].
        apply mem_cmpVersionSet; exists (sigma x); split; [apply Hins |].
        split; [| reflexivity].
        rewrite opEvalY_complement; apply Bool.negb_true_iff.
        destruct (opEvalY op (sigma x) y); [exfalso; apply Hs; reflexivity
                                            | reflexivity]. }
      induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intro Hsub.
      - assert (Hm : NSet.In m Ns)
          by (apply Hsub; simpl; apply NSet.singleton_spec; reflexivity).
        split4v.
        + intros q0 Hwit q o ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hsat _]]; [exfalso; exact (Hq0 Hqw) |].
          destruct Hsat as [u [Hu HuS]].
          exists (Version.Orig u); split;
            [unfold embedVS; apply SOvv.mem_map;
             exists u; split; [exact Hu | reflexivity]
            | exact (Hemb (m, u) HuS)].
        + intros q0 Hwit q o ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hns _]]; [exfalso; exact (Hq0 Hqw) |].
          exact (Hneg m vs Hm Hns).
        + intros n i0 Hspine q o ws Henc Hqw.
          assert (Hwit := Hspine 0 (FDep m vs) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hsat _]]; [exfalso; exact (Hq0 Hqw) |].
          destruct Hsat as [u [Hu HuS]].
          exists (Version.Orig u); split;
            [unfold embedVS; apply SOvv.mem_map;
             exists u; split; [exact Hu | reflexivity]
            | exact (Hemb (m, u) HuS)].
        + intros n i0 Hspine q o ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FDep m vs)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hns _]]; [exfalso; exact (Hq0 Hqw) |].
          exact (Hneg m vs Hm Hns).
      - assert (Hsa : NSet.Subset (fnames a) Ns)
          by (intros z Hz; apply Hsub; simpl; apply NSet.union_spec; left;
              exact Hz).
        assert (Hsb : NSet.Subset (fnames b) Ns)
          by (intros z Hz; apply Hsub; simpl; apply NSet.union_spec; right;
              exact Hz).
        destruct (IHa Hsa) as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct (IHb Hsb) as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros q0 Hwit q o ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 q0 _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj1 Hsat) |]];
              intros z Hz; apply Hsub', T.PkgSet.union_spec; left; exact Hz.
          * refine (IHb1 q0 _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj2 Hsat) |]];
              intros z Hz; apply Hsub', T.PkgSet.union_spec; right; exact Hz.
        + intros q0 Hwit q o ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [Hq0 | [_ Hsub']]; [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx
                      (firstSatIdx S sigma (FNeg a :: negConjSpine b))); split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S sigma (FNeg a :: negConjSpine b)); split;
                 [apply firstSatIdx_lt; discriminate | reflexivity].
            -- apply Hsub'; rewrite witnessSetTakenNeg_conj_eq;
                 apply SOpt.add_in; left; reflexivity.
          * apply T.DepRel.union_spec in He; destruct He as [He | He].
            -- refine (IHa2 (Name.Disjunct (FNeg a :: negConjSpine b),
                             Version.Idx 0) _ q o ws He Hqw).
               destruct (T.PkgSet.mem
                           (Name.Disjunct (FNeg a :: negConjSpine b),
                            Version.Idx 0) w) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [g [Hg [Hsg Hsub']]].
                  cbn [List.nth_error] in Hg; injection Hg as <-.
                  right; split; [exact Hsg | exact Hsub'].
               ++ left; intro Hin; apply T.PkgSet.mem_spec in Hin;
                    discriminate (eq_trans (eq_sym Hin) EM).
            -- refine (IHb4 (Name.Disjunct (FNeg a :: negConjSpine b)) 1
                         _ q o ws He Hqw).
               intros k g Hg.
               assert (Hg' : List.nth_error (FNeg a :: negConjSpine b) (1 + k)
                             = Some g) by exact Hg.
               destruct (T.PkgSet.mem
                           (Name.Disjunct (FNeg a :: negConjSpine b),
                            Version.Idx (1 + k)) w) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [g' [Hg2 [Hsg Hsub']]].
                  rewrite Hg' in Hg2; injection Hg2 as <-.
                  right; split; [exact Hsg | exact Hsub'].
               ++ left; intro Hin; apply T.PkgSet.mem_spec in Hin;
                    discriminate (eq_trans (eq_sym Hin) EM).
        + intros n i0 Hspine q o ws Henc Hqw.
          assert (Hwit := Hspine 0 (FConj a b) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 (n, Version.Idx i0) _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj1 Hsat) |]];
              intros z Hz; apply Hsub', T.PkgSet.union_spec; left; exact Hz.
          * refine (IHb1 (n, Version.Idx i0) _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj2 Hsat) |]];
              intros z Hz; apply Hsub', T.PkgSet.union_spec; right; exact Hz.
        + intros n i0 Hspine q o ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 (n, Version.Idx i0) _ q o ws He Hqw).
            assert (Hwit := Hspine 0 (FNeg a) eq_refl);
              replace (i0 + 0) with i0 in Hwit by lia.
            exact Hwit.
          * refine (IHb4 n (Datatypes.S i0) _ q o ws He Hqw).
            intros k g Hg.
            assert (H := Hspine (Datatypes.S k) g Hg).
            replace (Datatypes.S i0 + k) with (i0 + Datatypes.S k) by lia.
            exact H.
      - assert (Hsa : NSet.Subset (fnames a) Ns)
          by (intros z Hz; apply Hsub; simpl; apply NSet.union_spec; left;
              exact Hz).
        assert (Hsb : NSet.Subset (fnames b) Ns)
          by (intros z Hz; apply Hsub; simpl; apply NSet.union_spec; right;
              exact Hz).
        destruct (IHa Hsa) as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct (IHb Hsb) as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros q0 Hwit q o ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [Hq0 | [_ Hsub']]; [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx (firstSatIdx S sigma (a :: disjSpine b))); split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S sigma (a :: disjSpine b)); split;
                 [apply firstSatIdx_lt; discriminate | reflexivity].
            -- apply Hsub'; rewrite witnessSetTaken_disj_eq;
                 apply SOpt.add_in; left; reflexivity.
          * apply T.DepRel.union_spec in He; destruct He as [He | He].
            -- refine (IHa1 (Name.Disjunct (a :: disjSpine b),
                             Version.Idx 0) _ q o ws He Hqw).
               destruct (T.PkgSet.mem (Name.Disjunct (a :: disjSpine b),
                                       Version.Idx 0) w) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [g [Hg [Hsg Hsub']]].
                  cbn [List.nth_error] in Hg; injection Hg as <-.
                  right; split; [exact Hsg | exact Hsub'].
               ++ left; intro Hin; apply T.PkgSet.mem_spec in Hin;
                    discriminate (eq_trans (eq_sym Hin) EM).
            -- refine (IHb3 (Name.Disjunct (a :: disjSpine b)) 1
                         _ q o ws He Hqw).
               intros k g Hg.
               assert (Hg' : List.nth_error (a :: disjSpine b) (1 + k)
                             = Some g) by exact Hg.
               destruct (T.PkgSet.mem (Name.Disjunct (a :: disjSpine b),
                                       Version.Idx (1 + k)) w) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [g' [Hg2 [Hsg Hsub']]].
                  rewrite Hg' in Hg2; injection Hg2 as <-.
                  right; split; [exact Hsg | exact Hsub'].
               ++ left; intro Hin; apply T.PkgSet.mem_spec in Hin;
                    discriminate (eq_trans (eq_sym Hin) EM).
        + intros q0 Hwit q o ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 q0 _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Ha; exact (Hns (or_introl Ha)) |]];
              intros z Hz; apply Hsub', T.PkgSet.union_spec; left; exact Hz.
          * refine (IHb2 q0 _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros z Hz; apply Hsub', T.PkgSet.union_spec; right; exact Hz.
        + intros n i0 Hspine q o ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 (n, Version.Idx i0) _ q o ws He Hqw).
            assert (Hwit := Hspine 0 a eq_refl);
              replace (i0 + 0) with i0 in Hwit by lia.
            exact Hwit.
          * refine (IHb3 n (Datatypes.S i0) _ q o ws He Hqw).
            intros k g Hg.
            assert (H := Hspine (Datatypes.S k) g Hg).
            replace (Datatypes.S i0 + k) with (i0 + Datatypes.S k) by lia.
            exact H.
        + intros n i0 Hspine q o ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FDisj a b)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 (n, Version.Idx i0) _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Ha; exact (Hns (or_introl Ha)) |]];
              intros z Hz; apply Hsub', T.PkgSet.union_spec; left; exact Hz.
          * refine (IHb2 (n, Version.Idx i0) _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros z Hz; apply Hsub', T.PkgSet.union_spec; right; exact Hz.
      - destruct (IHa Hsub) as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
        + intros q0 Hwit q o ws Henc Hqw.
          exact (IHa2 q0 Hwit q o ws Henc Hqw).
        + intros q0 Hwit q o ws Henc Hqw.
          destruct Hwit as [Hq0 | [Hnn Hsub']];
            [exact (IHa1 q0 (or_introl Hq0) q o ws Henc Hqw)
            | exact (IHa1 q0
                       (or_intror (conj (satisfies_double_neg S sigma a Hnn)
                                        Hsub'))
                       q o ws Henc Hqw)].
        + intros n i0 Hspine q o ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg a) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          exact (IHa2 (n, Version.Idx i0) Hwit q o ws Henc Hqw).
        + intros n i0 Hspine q o ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FNeg a)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          destruct Hwit as [Hq0 | [Hnn Hsub']];
            [exact (IHa1 (n, Version.Idx i0) (or_introl Hq0) q o ws Henc Hqw)
            | exact (IHa1 (n, Version.Idx i0)
                       (or_intror (conj (satisfies_double_neg S sigma a Hnn)
                                        Hsub'))
                       q o ws Henc Hqw)].
      - split4v.
        + intros q0 Hwit q o ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hsat _]]; [exfalso; exact (Hq0 Hqw) |].
          exact (Hcmp x op y Hsat).
        + intros q0 Hwit q o ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hns _]]; [exfalso; exact (Hq0 Hqw) |].
          exact (Hcmpn x op y Hns).
        + intros n i0 Hspine q o ws Henc Hqw.
          assert (Hwit := Hspine 0 (FVarCmp x op y) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hsat _]]; [exfalso; exact (Hq0 Hqw) |].
          exact (Hcmp x op y Hsat).
        + intros n i0 Hspine q o ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FVarCmp x op y)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [Hq0 | [Hns _]]; [exfalso; exact (Hq0 Hqw) |].
          exact (Hcmpn x op y Hns).
    Qed.

    Theorem variable_formula_completeness :
      forall (Y_x : X.t -> YSet.t) (R : PkgSet.t) (D : DepRel.t)
             (r : Pkg.t) (sigma : X.t -> Y.t),
        (forall x, YSet.In (sigma x) (Y_x x)) ->
        forall (S : PkgSet.t),
          IsResolution R D r S sigma ->
          T.IsResolution (reduceReal Y_x R D) (reduceDeps Y_x R D) (embedPkg r)
            (coreResolution S R D sigma).
    Proof.
      intros Y_x R D r sigma Hins S Hres;
        destruct Hres as [Hsub Hroot Hclo Huniq].
      assert (Hemb : forall p, PkgSet.In p S ->
          T.PkgSet.In (embedPkg p) (coreResolution S R D sigma)).
      { intros p Hp; apply mem_coreResolution; left.
        exists p; split; [exact Hp | reflexivity]. }
      assert (HVq : forall m u, PkgSet.In (m, u) S ->
          VSet.In u (C.versions R m)).
      { intros m u Hu; apply C.mem_versions; apply Hsub; exact Hu. }
      assert (Hbot : forall m, NSet.In m (instNames R D) ->
          (forall u, ~ PkgSet.In (m, u) S) ->
          T.PkgSet.In (Name.Orig m, Version.Bot) (coreResolution S R D sigma)).
      { intros m Hm Hnone; apply mem_coreResolution; right; right; right.
        exists m; auto. }
      assert (Horig : forall m v,
          T.PkgSet.In (Name.Orig m, Version.Orig v) (coreResolution S R D sigma) ->
          PkgSet.In (m, v) S).
      { intros m v Hv; apply mem_coreResolution in Hv.
        destruct Hv as [[[pn pv] [Hp Hpe]] | [[p [g [_ [_ Hw]]]]
                       | [[x Hx] | [n [_ [_ Hn]]]]]].
        - unfold embedPkg in Hpe; injection Hpe as -> ->; exact Hp.
        - exfalso; exact (witnessSetTaken_not_orig _ _ _ _ _ Hw).
        - discriminate Hx.
        - discriminate Hn. }
      assert (Hvar : forall x,
          T.PkgSet.In (Name.Var x, Version.VarVal (sigma x))
            (coreResolution S R D sigma)).
      { intro x; apply mem_coreResolution; right; right; left;
          exists x; reflexivity. }
      assert (Hdisj := fun fs i => coreResolution_disj S R D sigma fs i Hclo).
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy.
        apply mem_reduceReal.
        destruct Hy as [[p [Hp ->]] | [[p [g [Hd [_ Hw]]]]
                       | [[x ->] | [n [Hn [_ ->]]]]]].
        + left; exists p; split; [apply Hsub; exact Hp | reflexivity].
        + right; left; exists p, g; split; [exact Hd |].
          exact (witnessSetTaken_subset_witnessSet S sigma (embedPkg p) g _ Hw).
        + right; right; left; exists x, (sigma x);
            split; [apply Hins | reflexivity].
        + right; right; right; exists n; auto.
      - exact (Hemb r Hroot).
      - intros q Hq m vs Hd.
        apply mem_reduceDeps in Hd; destruct Hd as [p [g [Hpg Henc]]].
        assert (Hfn : NSet.Subset (fnames g) (instNames R D)).
        { intros z Hz; apply mem_instNames; right; apply mem_depNames.
          exists p, g; auto. }
        refine (proj1 (encodeNNF_dep_closure_aux S sigma Y_x (C.versions R)
                         (instNames R D) _ Hins Hemb HVq Hbot Hdisj Hvar g Hfn)
                  (embedPkg p) _ q m vs Henc Hq).
        destruct (PkgSet.mem p S) eqn:Ep.
        + apply PkgSet.mem_spec in Ep.
          right; split; [exact (Hclo p Ep g Hpg) |].
          exact (witnessSetTaken_subset_coreResolution S R D sigma p g Hpg Ep).
        + left; intro Hin; destruct p as [pn pv].
          apply Horig, PkgSet.mem_spec in Hin; congruence.
      - intros n v v' Hv Hv'.
        apply mem_coreResolution in Hv, Hv'.
        destruct Hv as [[[n1 w1] [Hp1 He1]] | [[p1 [g1 [Hd1 [Hp1 Hw1]]]]
                       | [[x1 Hq1] | [m1 [_ [Hn1 He1]]]]]];
          destruct Hv' as [[[n2 w2] [Hp2 He2]] | [[p2 [g2 [Hd2 [Hp2 Hw2]]]]
                          | [[x2 Hq2] | [m2 [_ [Hn2 He2]]]]]];
          unfold embedPkg in *.
        + injection He1 as -> ->; injection He2 as -> ->.
          f_equal; exact (Huniq _ _ _ Hp1 Hp2).
        + injection He1 as -> ->.
          exfalso; exact (witnessSetTaken_not_orig _ _ _ _ _ Hw2).
        + injection He1 as -> ->; discriminate Hq2.
        + injection He1 as -> ->; injection He2 as -> ->.
          exfalso; exact (Hn2 _ Hp1).
        + injection He2 as -> ->.
          exfalso; exact (witnessSetTaken_not_orig _ _ _ _ _ Hw1).
        + destruct n as [n0 | x | fs].
          * exfalso; exact (witnessSetTaken_not_orig _ _ _ _ _ Hw1).
          * exfalso; exact (witnessSetTaken_not_var _ _ _ _ _ Hw1).
          * rewrite (witnessSetTaken_disjunct_det _ _ _ _ _ Hw1),
              (witnessSetTaken_disjunct_det _ _ _ _ _ Hw2); reflexivity.
        + injection Hq2 as -> ->.
          exfalso; exact (witnessSetTaken_not_var _ _ _ _ _ Hw1).
        + injection He2 as -> ->.
          exfalso; exact (witnessSetTaken_not_orig _ _ _ _ _ Hw1).
        + injection Hq1 as -> ->; discriminate He2.
        + injection Hq1 as -> ->.
          exfalso; exact (witnessSetTaken_not_var _ _ _ _ _ Hw2).
        + injection Hq1 as -> ->; injection Hq2 as -> ->; reflexivity.
        + injection Hq1 as -> ->; discriminate He2.
        + injection He1 as -> ->; injection He2 as -> ->.
          exfalso; exact (Hn1 _ Hp2).
        + injection He1 as -> ->.
          exfalso; exact (witnessSetTaken_not_orig _ _ _ _ _ Hw2).
        + injection He1 as -> ->; discriminate Hq2.
        + injection He1 as -> ->; injection He2 as _ ->; reflexivity.
    Qed.

    Module Lookup.
      Definition disjAlt (fs : list Formula) (i : Version.t) :
          option Formula :=
        match i with
        | Version.Idx k => List.nth_error fs k
        | _ => None
        end.

      Definition notIdx (w : Version.t) : Prop :=
        forall i, w <> Version.Idx i.

      Lemma notIdx_orig : forall v, notIdx (Version.Orig v).
      Proof. intros v i E; discriminate E. Qed.

      Lemma notIdx_bot : notIdx Version.Bot.
      Proof. intros i E; discriminate E. Qed.

      Lemma notIdx_varval : forall y, notIdx (Version.VarVal y).
      Proof. intros y i E; discriminate E. Qed.

      Lemma encodeNNF_src_aux : forall Y_x Vq f,
          (forall (q q' : T.Pkg.t) (d : T.Dependees.t),
              notIdx (snd q') ->
              T.DepRel.In (q', d) (encodeNNF Y_x Vq q f) -> q = q') /\
          (forall (q q' : T.Pkg.t) (d : T.Dependees.t),
              notIdx (snd q') ->
              T.DepRel.In (q', d) (encodeNNFneg Y_x Vq q f) -> q = q') /\
          (forall (n : Name.t) (i0 : nat) (q' : T.Pkg.t) (d : T.Dependees.t),
              notIdx (snd q') ->
              T.DepRel.In (q', d) (encodeDisj Y_x Vq n i0 f) -> False) /\
          (forall (n : Name.t) (i0 : nat) (q' : T.Pkg.t) (d : T.Dependees.t),
              notIdx (snd q') ->
              T.DepRel.In (q', d) (encodeConjNeg Y_x Vq n i0 f) -> False).
      Proof.
        intros Y_x Vq f;
          induction f as [o ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - split4v.
          + intros q q' d Hw H; apply SOed.singleton_in in H; congruence.
          + intros q q' d Hw H; apply SOed.singleton_in in H; congruence.
          + intros n i0 q' d Hw H; apply SOed.singleton_in in H;
              injection H as E _; subst q'; exact (Hw i0 eq_refl).
          + intros n i0 q' d Hw H; apply SOed.singleton_in in H;
              injection H as E _; subst q'; exact (Hw i0 eq_refl).
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q q' d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa1 _ _ _ Hw H) | exact (IHb1 _ _ _ Hw H)].
          + intros q q' d Hw H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ Hw H); subst q'; destruct (Hw 0 eq_refl)
              | destruct (IHb4 _ _ _ _ Hw H)].
          + intros n i0 q' d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ Hw H) | assert (E := IHb1 _ _ _ Hw H)];
              subst q'; destruct (Hw i0 eq_refl).
          + intros n i0 q' d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ Hw H); subst q'; destruct (Hw i0 eq_refl)
              | destruct (IHb4 _ _ _ _ Hw H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q q' d Hw H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ Hw H); subst q'; destruct (Hw 0 eq_refl)
              | destruct (IHb3 _ _ _ _ Hw H)].
          + intros q q' d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa2 _ _ _ Hw H) | exact (IHb2 _ _ _ Hw H)].
          + intros n i0 q' d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ Hw H); subst q'; destruct (Hw i0 eq_refl)
              | destruct (IHb3 _ _ _ _ Hw H)].
          + intros n i0 q' d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ Hw H) | assert (E := IHb2 _ _ _ Hw H)];
              subst q'; destruct (Hw i0 eq_refl).
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros q q' d Hw H; exact (IHa2 _ _ _ Hw H).
          + intros q q' d Hw H; exact (IHa1 _ _ _ Hw H).
          + intros n i0 q' d Hw H; assert (E := IHa2 _ _ _ Hw H); subst q';
              destruct (Hw i0 eq_refl).
          + intros n i0 q' d Hw H; assert (E := IHa1 _ _ _ Hw H); subst q';
              destruct (Hw i0 eq_refl).
        - split4v.
          + intros q q' d Hw H; apply SOed.singleton_in in H; congruence.
          + intros q q' d Hw H; apply SOed.singleton_in in H; congruence.
          + intros n i0 q' d Hw H; apply SOed.singleton_in in H;
              injection H as E _; subst q'; exact (Hw i0 eq_refl).
          + intros n i0 q' d Hw H; apply SOed.singleton_in in H;
              injection H as E _; subst q'; exact (Hw i0 eq_refl).
      Qed.

      Lemma encodeNNF_tgt_aux : forall Y_x Vq f,
          (forall (q q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeNNF Y_x Vq q f) ->
              NSet.In m (fnames f)) /\
          (forall (q q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeNNFneg Y_x Vq q f) ->
              NSet.In m (fnames f)) /\
          (forall (n : Name.t) (i0 : nat) (q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeDisj Y_x Vq n i0 f) ->
              NSet.In m (fnames f)) /\
          (forall (n : Name.t) (i0 : nat) (q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeConjNeg Y_x Vq n i0 f) ->
              NSet.In m (fnames f)).
      Proof.
        intros Y_x Vq f;
          induction f as [o vs | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - split4v; intros; apply SOed.singleton_in in H; injection H as _ <- _;
            simpl; apply NSet.singleton_spec; reflexivity.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ H) | right; exact (IHb1 _ _ _ _ H)].
          + intros q q' m ws H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [discriminate |].
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ H) | right; exact (IHb4 _ _ _ _ _ H)].
          + intros n i0 q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ H) | right; exact (IHb1 _ _ _ _ H)].
          + intros n i0 q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ H) | right; exact (IHb4 _ _ _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q q' m ws H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [discriminate |].
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ H) | right; exact (IHb3 _ _ _ _ _ H)].
          + intros q q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ H) | right; exact (IHb2 _ _ _ _ H)].
          + intros n i0 q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ H) | right; exact (IHb3 _ _ _ _ _ H)].
          + intros n i0 q' m ws H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; apply NSet.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ H) | right; exact (IHb2 _ _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros q q' m ws H; exact (IHa2 _ _ _ _ H).
          + intros q q' m ws H; exact (IHa1 _ _ _ _ H).
          + intros n i0 q' m ws H; exact (IHa2 _ _ _ _ H).
          + intros n i0 q' m ws H; exact (IHa1 _ _ _ _ H).
        - split4v; intros; apply SOed.singleton_in in H; discriminate H.
      Qed.

      Lemma encodeNNF_agree_aux : forall Y_x Vq Vq' f,
          (forall m, NSet.In m (fnames f) -> Vq m = Vq' m) ->
          (forall p, encodeNNF Y_x Vq p f = encodeNNF Y_x Vq' p f) /\
          (forall p, encodeNNFneg Y_x Vq p f = encodeNNFneg Y_x Vq' p f) /\
          (forall n i, encodeDisj Y_x Vq n i f = encodeDisj Y_x Vq' n i f) /\
          (forall n i, encodeConjNeg Y_x Vq n i f = encodeConjNeg Y_x Vq' n i f).
      Proof.
        intros Y_x Vq Vq' f;
          induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          intro Hag.
        - assert (E : Vq m = Vq' m)
            by (apply Hag; simpl; apply NSet.singleton_spec; reflexivity).
          split4v; intros; simpl; unfold complementVS; try rewrite E; reflexivity.
        - assert (Ha : forall m, NSet.In m (fnames a) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; left;
                exact Hm).
          assert (Hb : forall m, NSet.In m (fnames b) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; right;
                exact Hm).
          destruct (IHa Ha) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Hb) as (IHb1 & IHb2 & IHb3 & IHb4); split4v;
            intros; simpl.
          + rewrite IHa1, IHb1; reflexivity.
          + rewrite IHa2, IHb4; reflexivity.
          + rewrite IHa1, IHb1; reflexivity.
          + rewrite IHa2, IHb4; reflexivity.
        - assert (Ha : forall m, NSet.In m (fnames a) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; left;
                exact Hm).
          assert (Hb : forall m, NSet.In m (fnames b) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; right;
                exact Hm).
          destruct (IHa Ha) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Hb) as (IHb1 & IHb2 & IHb3 & IHb4); split4v;
            intros; simpl.
          + rewrite IHa1, IHb3; reflexivity.
          + rewrite IHa2, IHb2; reflexivity.
          + rewrite IHa1, IHb3; reflexivity.
          + rewrite IHa2, IHb2; reflexivity.
        - destruct (IHa Hag) as (IHa1 & IHa2 & IHa3 & IHa4); split4v;
            intros; simpl; [apply IHa2 | apply IHa1 | apply IHa2 | apply IHa1].
        - split4v; intros; reflexivity.
      Qed.

      Lemma reduceDepsBy_agree : forall Y_x Vq Vq' D,
          (forall m, NSet.In m (depNames D) -> Vq m = Vq' m) ->
          reduceDepsBy Y_x Vq D = reduceDepsBy Y_x Vq' D.
      Proof.
        intros Y_x Vq Vq' D Hag; apply T.DepRel.ext; intro d.
        rewrite !mem_reduceDepsBy.
        split; intros [p [f [Hd He]]]; exists p, f; split; try exact Hd;
          assert (Hf : forall m, NSet.In m (fnames f) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag, mem_depNames; exists p, f; auto);
          [rewrite <- (proj1 (encodeNNF_agree_aux Y_x Vq Vq' f Hf))
          | rewrite (proj1 (encodeNNF_agree_aux Y_x Vq Vq' f Hf))]; exact He.
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Module DepRelFibred := FibredRel Pkg Dependees DepElt DepRel.
      Module RKeys := PreimageOfKeys N Pkg NSet PkgSet.

      Definition nameRestrict (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
        RKeys.ofKeys fst ns R.

      Lemma versions_nameRestrict : forall R ns n,
          NSet.In n ns -> C.versions (nameRestrict R ns) n = C.versions R n.
      Proof.
        intros R ns n Hn; apply C.versions_ext; intro v.
        unfold nameRestrict; rewrite RKeys.mem_ofKeys; cbn [fst]; tauto.
      Qed.

      (* the variable domain arrives as a function, so the fibre that keeps
         one variable's values has to be written out rather than filtered. *)
      Definition varFibre (Y_x : X.t -> YSet.t) (x : X.t) : X.t -> YSet.t :=
        fun x' => if X.eq_dec x' x then Y_x x' else YSet.empty.

      Definition syntheticPkgs (n : Name.t) : T.PkgSet.t :=
        match n with
        | Name.Orig _ => T.PkgSet.empty
        | Name.Var _ => T.PkgSet.empty
        | Name.Disjunct fs => idxPkgs (Name.Disjunct fs) (List.length fs)
        end.

      Lemma witnessSet_synthetic_aux : forall f : Formula,
          (forall (p q : T.Pkg.t),
              T.PkgSet.In q (witnessSet p f) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (p q : T.Pkg.t),
              T.PkgSet.In q (witnessSetNeg p f) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (n : Name.t) (i : nat) (q : T.Pkg.t),
              T.PkgSet.In q (witnessDisj n i f) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (n : Name.t) (i : nat) (q : T.Pkg.t),
              T.PkgSet.In q (witnessConjNeg n i f) ->
              T.PkgSet.In q (syntheticPkgs (fst q))).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - repeat split; intros; exfalso; eapply SOpt.empty_in; eassumption.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H].
            * apply mem_idxPkgs in H; destruct H as [i [Hi ->]];
                cbn [fst syntheticPkgs]; apply mem_idxPkgs; exists i;
                split; [exact Hi | reflexivity].
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [exact (IHa2 _ _ H) | exact (IHb4 _ _ _ H)].
          + intros n i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
          + intros n i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [exact (IHa2 _ _ H) | exact (IHb4 _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H].
            * apply mem_idxPkgs in H; destruct H as [i [Hi ->]];
                cbn [fst syntheticPkgs]; apply mem_idxPkgs; exists i;
                split; [exact Hi | reflexivity].
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [exact (IHa1 _ _ H) | exact (IHb3 _ _ _ H)].
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
          + intros n i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [exact (IHa1 _ _ H) | exact (IHb3 _ _ _ H)].
          + intros n i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
          + intros p q H; simpl in H; exact (IHa2 _ _ H).
          + intros p q H; simpl in H; exact (IHa1 _ _ H).
          + intros n i q H; simpl in H; exact (IHa2 _ _ H).
          + intros n i q H; simpl in H; exact (IHa1 _ _ H).
        - repeat split; intros; exfalso; eapply SOpt.empty_in; eassumption.
      Qed.

      Lemma encodeNNF_target_synthetic_aux : forall Y_x Vq (f : Formula),
          (forall (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNF Y_x Vq p f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d))) (witnessSet p f)) /\
          (forall (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNFneg Y_x Vq p f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessSetNeg p f)) /\
          (forall (n : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeDisj Y_x Vq n i f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessDisj n i f)) /\
          (forall (n : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeConjNeg Y_x Vq n i f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessConjNeg n i f)).
      Proof.
        intros Y_x Vq f;
          induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - repeat split; intros; apply SOed.singleton_in in H; subst d;
            cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz) | right; exact (IHb1 _ d H z Hz)].
          + intros p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H].
            * intros z Hz; cbn [fst snd syntheticPkgs] in Hz;
                apply T.PkgSet.union_spec; left; exact Hz.
            * apply T.DepRel.union_spec in H; intros z Hz;
                apply T.PkgSet.union_spec; right;
                apply T.PkgSet.union_spec; destruct H as [H | H];
                [left; exact (IHa2 _ d H z Hz)
                | right; exact (IHb4 _ _ d H z Hz)].
          + intros n i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz) | right; exact (IHb1 _ d H z Hz)].
          + intros n i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz)
              | right; exact (IHb4 _ _ d H z Hz)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H].
            * intros z Hz; cbn [fst snd syntheticPkgs] in Hz;
                apply T.PkgSet.union_spec; left; exact Hz.
            * apply T.DepRel.union_spec in H; intros z Hz;
                apply T.PkgSet.union_spec; right;
                apply T.PkgSet.union_spec; destruct H as [H | H];
                [left; exact (IHa1 _ d H z Hz)
                | right; exact (IHb3 _ _ d H z Hz)].
          + intros p d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz) | right; exact (IHb2 _ d H z Hz)].
          + intros n i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz)
              | right; exact (IHb3 _ _ d H z Hz)].
          + intros n i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz) | right; exact (IHb2 _ d H z Hz)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
          + intros p d H; simpl in H; exact (IHa2 _ d H).
          + intros p d H; simpl in H; exact (IHa1 _ d H).
          + intros n i d H; simpl in H; exact (IHa2 _ d H).
          + intros n i d H; simpl in H; exact (IHa1 _ d H).
        - repeat split; intros; apply SOed.singleton_in in H; subst d;
            cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
      Qed.

      Lemma reachable_instNames : forall Y_x R D (m : N.t),
          (exists p h, T.DepRel.In (p, (Name.Orig m, h)) (reduceDeps Y_x R D)) ->
          NSet.In m (instNames R D).
      Proof.
        intros Y_x R D m [p [h Hd]]; apply mem_reduceDeps in Hd.
        destruct Hd as [q [f [Hq He]]].
        apply mem_instNames; right; apply mem_depNames; exists q, f.
        split; [exact Hq |].
        exact (proj1 (encodeNNF_tgt_aux Y_x (C.versions R) f) _ _ _ _ He).
      Qed.

      Theorem versions_lookupOrig : forall Y_x R D (r : Pkg.t) (m : N.t),
          PkgSet.In r R ->
          (exists p h,
              T.DepRel.In (p, (Name.Orig m, h)) (reduceDeps Y_x R D)) \/
          Name.Orig m = Name.Orig (fst r) ->
          T.versions (reduceReal Y_x R D) (Name.Orig m) =
          T.VSet.add Version.Bot
            (embedVS (C.versions (PkgFibred.tailFibre R m) m)).
      Proof.
        intros Y_x R D r m Hr Hreach.
        assert (Hm : NSet.In m (instNames R D)).
        { destruct Hreach as [Hreach | E];
            [exact (reachable_instNames Y_x R D m Hreach) |].
          injection E as ->; apply mem_instNames; left.
          destruct r as [rn rv]; exists rv; exact Hr. }
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal, SOvv.add_in.
        unfold embedVS; rewrite SOvv.mem_map.
        split.
        - intros [[[qn qv] [HR Hq]] | [[p [f [_ Hw]]] | [[x [y' [_ Hq]]] | [n [_ Hy]]]]].
          + unfold embedPkg in Hq; injection Hq as -> ->.
            right; exists qv; split; [| reflexivity].
            apply C.mem_versions, PkgFibred.mem_tailFibre; auto.
          + exfalso; exact (witnessSet_not_orig _ _ _ _ Hw).
          + discriminate Hq.
          + injection Hy as -> ->; left; reflexivity.
        - intros [-> | [v [Hv ->]]].
          + right; right; right; exists m; auto.
          + apply C.mem_versions, PkgFibred.mem_tailFibre in Hv.
            destruct Hv as [Hv _].
            left; exists (m, v); split; [exact Hv | reflexivity].
      Qed.

      Theorem dependees_lookupOrig : forall Y_x R D m v,
          T.dependees (reduceDeps Y_x R D) (Name.Orig m, Version.Orig v) =
          T.dependees
            (reduceDeps Y_x
               (nameRestrict R (depNames (DepRelFibred.tailFibre D (m, v))))
               (DepRelFibred.tailFibre D (m, v)))
            (Name.Orig m, Version.Orig v).
      Proof.
        intros Y_x R D m v; apply T.dependees_ext; intro h.
        rewrite !mem_reduceDeps.
        assert (Hag : forall f,
                   DepRel.In ((m, v), f) (DepRelFibred.tailFibre D (m, v)) ->
                   encodeNNF Y_x (C.versions R) (embedPkg (m, v)) f =
                   encodeNNF Y_x
                     (C.versions (nameRestrict R
                                    (depNames (DepRelFibred.tailFibre D (m, v)))))
                     (embedPkg (m, v)) f).
        { intros f Hf.
          assert (Hag' : forall x, NSet.In x (fnames f) ->
                     C.versions R x =
                     C.versions (nameRestrict R
                                   (depNames (DepRelFibred.tailFibre D (m, v)))) x).
          { intros x Hx; symmetry; apply versions_nameRestrict.
            apply mem_depNames; exists (m, v), f; auto. }
          exact (proj1 (encodeNNF_agree_aux Y_x _ _ f Hag') (embedPkg (m, v))). }
        split.
        - intros [p [f [Hd He]]].
          assert (E := proj1 (encodeNNF_src_aux Y_x (C.versions R) f)
                         _ (Name.Orig m, Version.Orig v) _ (notIdx_orig v) He).
          destruct p as [pn pv]; unfold embedPkg in E; injection E as -> ->.
          assert (Hf : DepRel.In ((m, v), f) (DepRelFibred.tailFibre D (m, v)))
            by (apply DepRelFibred.mem_tailFibre; auto).
          exists (m, v), f; split; [exact Hf |].
          rewrite <- (Hag f Hf); exact He.
        - intros [p [f [Hd He]]].
          assert (Hd' := Hd); apply DepRelFibred.mem_tailFibre in Hd';
            destruct Hd' as [HD ->].
          exists (m, v), f; split; [exact HD |].
          rewrite (Hag f Hd); exact He.
      Qed.

      Theorem dependees_lookupOrigBy : forall Y_x R D Vq m v,
          (forall n, NSet.In n (depNames (DepRelFibred.tailFibre D (m, v))) ->
                     Vq n = C.versions R n) ->
          T.dependees (reduceDeps Y_x R D) (Name.Orig m, Version.Orig v) =
          T.dependees (reduceDepsBy Y_x Vq (DepRelFibred.tailFibre D (m, v)))
            (Name.Orig m, Version.Orig v).
      Proof.
        intros Y_x R D Vq m v HVq; rewrite dependees_lookupOrig; unfold reduceDeps.
        f_equal; apply reduceDepsBy_agree; intros n Hn.
        rewrite versions_nameRestrict by exact Hn; symmetry; apply HVq; exact Hn.
      Qed.

      Theorem dependees_lookupAbsent : forall Y_x R D m,
          T.dependees (reduceDeps Y_x R D) (Name.Orig m, Version.Bot) =
          T.DependeesSet.empty.
      Proof.
        intros Y_x R D m; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [f [_ He]]].
        assert (E := proj1 (encodeNNF_src_aux Y_x (C.versions R) f)
                       _ (Name.Orig m, Version.Bot) _ notIdx_bot He).
        unfold embedPkg in E; discriminate.
      Qed.

      Theorem versions_lookupVar : forall Y_x R D (x : X.t),
          (exists p h,
              T.DepRel.In (p, (Name.Var x, h)) (reduceDeps Y_x R D)) ->
          T.versions (reduceReal Y_x R D) (Name.Var x) =
          T.versions (reduceReal (varFibre Y_x x) PkgSet.empty DepRel.empty)
            (Name.Var x).
      Proof.
        intros Y_x R D x _; apply T.versions_ext; intro w.
        rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [[p [f [_ Hw]]] | [[x' [y [Hy Hq]]] | [n [_ Hq]]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + exfalso; exact (witnessSet_not_var _ _ _ _ Hw).
          + injection Hq as -> ->.
            right; right; left; exists x', y; split; [| reflexivity].
            unfold varFibre; destruct (X.eq_dec x' x') as [_ | NE];
              [exact Hy | contradiction NE; reflexivity].
          + discriminate Hq.
        - intros [[p [Hp _]] | [[p [f [Hd _]]] | [[x' [y [Hy Hq]]] | [n [Hn _]]]]].
          + destruct (PkgSet.empty_spec Hp).
          + destruct (DepRel.empty_spec Hd).
          + right; right; left; exists x', y; split; [| exact Hq].
            unfold varFibre in Hy; destruct (X.eq_dec x' x) as [_ | NE];
              [exact Hy | destruct (YSet.empty_spec Hy)].
          + apply mem_instNames in Hn.
            destruct Hn as [[v Hv] | Hn]; [destruct (PkgSet.empty_spec Hv) |].
            apply mem_depNames in Hn; destruct Hn as [p [f [Hd _]]].
            destruct (DepRel.empty_spec Hd).
      Qed.

      Theorem dependees_lookupVar : forall Y_x R D x (y : Version.t),
          T.PkgSet.In (Name.Var x, y) (reduceReal Y_x R D) ->
          T.dependees (reduceDeps Y_x R D) (Name.Var x, y) = T.DependeesSet.empty.
      Proof.
        intros Y_x R D x y Hin; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [f [_ He]]].
        assert (Hw : notIdx y).
        { apply mem_reduceReal in Hin.
          destruct Hin as [[[qn qv] [_ Hq]] | [[p [g [_ Hw]]] | [[x' [y' [_ Hq]]] | [n [_ Hq]]]]];
            [unfold embedPkg in Hq; discriminate Hq
            | exfalso; exact (witnessSet_not_var _ _ _ _ Hw)
            | injection Hq as _ ->; apply notIdx_varval
            | discriminate Hq]. }
        assert (E := proj1 (encodeNNF_src_aux Y_x (C.versions R) f)
                       _ (Name.Var x, y) _ Hw He).
        unfold embedPkg in E; discriminate.
      Qed.

      Theorem versions_lookupDisjunct : forall Y_x R D (fs : list Formula),
          (exists p h, T.DepRel.In (p, (Name.Disjunct fs, h))
                         (reduceDeps Y_x R D)) ->
          T.versions (reduceReal Y_x R D) (Name.Disjunct fs) =
          idxSet (List.length fs).
      Proof.
        intros Y_x R D fs [p [h Hd]].
        apply mem_reduceDeps in Hd; destruct Hd as [r [g [HD He]]].
        pose proof (proj1 (encodeNNF_target_synthetic_aux Y_x (C.versions R) g)
                      (embedPkg r) (p, (Name.Disjunct fs, h)) He) as Hsub.
        cbn [fst snd] in Hsub.
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_idxSet, mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [[r1 [g1 [_ Hw]]] | [[x1 [y1 [_ Hq]]] | [n [_ Hq]]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + pose proof (proj1 (witnessSet_synthetic_aux g1) _ _ Hw) as Hg.
            cbn [fst syntheticPkgs] in Hg; apply mem_idxPkgs in Hg.
            destruct Hg as [i [Hi Hq]]; exists i;
              split; [exact Hi | congruence].
          + discriminate Hq.
          + discriminate Hq.
        - intros [i [Hi ->]]; right; left; exists r, g; split; [exact HD |].
          apply Hsub; cbn [syntheticPkgs]; apply mem_idxPkgs;
            exists i; split; [exact Hi | reflexivity].
      Qed.

      Lemma encodeDisj_alt : forall (f : Formula) (Y_x : X.t -> YSet.t)
                                    (Vq : N.t -> VSet.t)
                                    (n : Name.t) (i0 j : nat)
                                    (g : Formula) (d : T.Dependees.t),
          List.nth_error (disjSpine f) j = Some g ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d)
            (encodeNNF Y_x Vq (n, Version.Idx (i0 + j)) g) ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d) (encodeDisj Y_x Vq n i0 f).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          intros Y_x Vq n i0 j g d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb Y_x Vq n (S i0) j g d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma encodeConjNeg_alt : forall (f : Formula) (Y_x : X.t -> YSet.t)
                                       (Vq : N.t -> VSet.t)
                                       (n : Name.t) (i0 j : nat)
                                       (g : Formula) (d : T.Dependees.t),
          List.nth_error (negConjSpine f) j = Some g ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d)
            (encodeNNF Y_x Vq (n, Version.Idx (i0 + j)) g) ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d)
            (encodeConjNeg Y_x Vq n i0 f).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          intros Y_x Vq n i0 j g d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb Y_x Vq n (S i0) j g d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma witnessSet_alt_aux : forall (f : Formula) (Y_x : X.t -> YSet.t)
                                        (Vq : N.t -> VSet.t),
          (forall (p : T.Pkg.t) (gs : list Formula) (k : nat) (g : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k) (witnessSet p f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x Vq p f)) /\
          (forall (p : T.Pkg.t) (gs : list Formula) (k : nat) (g : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessSetNeg p f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNFneg Y_x Vq p f)) /\
          (forall (n : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (g : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessDisj n i0 f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeDisj Y_x Vq n i0 f)) /\
          (forall (n : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (g : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessConjNeg n i0 f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeConjNeg Y_x Vq n i0 f)).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          intros Y_x Vq.
        - split4v; intros; exfalso; eapply SOpt.empty_in; eassumption.
        - destruct (IHa Y_x Vq) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Y_x Vq) as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros p gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb1 _ _ _ _ _ H Hg Hd)].
          + intros p gs k g d H Hg Hd; simpl in H; simpl.
            apply T.PkgSet.union_spec in H; apply SOed.add_in;
              destruct H as [H | H]; [| right; apply T.DepRel.union_spec].
            * apply mem_idxPkgs in H; destruct H as [i [_ H]];
                injection H as H1 H2; subst gs; subst k; right;
                apply T.DepRel.union_spec; destruct i as [| i];
                simpl in Hg; [left | right].
              -- injection Hg as <-; exact Hd.
              -- exact (encodeConjNeg_alt b Y_x Vq
                          (Name.Disjunct (FNeg a :: negConjSpine b))
                          1 i g d Hg Hd).
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
                | right; exact (IHb4 _ _ _ _ _ _ H Hg Hd)].
          + intros n i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb1 _ _ _ _ _ H Hg Hd)].
          + intros n i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb4 _ _ _ _ _ _ H Hg Hd)].
        - destruct (IHa Y_x Vq) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Y_x Vq) as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros p gs k g d H Hg Hd; simpl in H; simpl.
            apply T.PkgSet.union_spec in H; apply SOed.add_in;
              destruct H as [H | H]; [| right; apply T.DepRel.union_spec].
            * apply mem_idxPkgs in H; destruct H as [i [_ H]];
                injection H as H1 H2; subst gs; subst k; right;
                apply T.DepRel.union_spec; destruct i as [| i];
                simpl in Hg; [left | right].
              -- injection Hg as <-; exact Hd.
              -- exact (encodeDisj_alt b Y_x Vq (Name.Disjunct (a :: disjSpine b))
                          1 i g d Hg Hd).
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
                | right; exact (IHb3 _ _ _ _ _ _ H Hg Hd)].
          + intros p gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb2 _ _ _ _ _ H Hg Hd)].
          + intros n i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb3 _ _ _ _ _ _ H Hg Hd)].
          + intros n i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb2 _ _ _ _ _ H Hg Hd)].
        - destruct (IHa Y_x Vq) as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros p gs k g d H Hg Hd; exact (IHa2 _ _ _ _ _ H Hg Hd).
          + intros p gs k g d H Hg Hd; exact (IHa1 _ _ _ _ _ H Hg Hd).
          + intros n i0 gs k g d H Hg Hd; exact (IHa2 _ _ _ _ _ H Hg Hd).
          + intros n i0 gs k g d H Hg Hd; exact (IHa1 _ _ _ _ _ H Hg Hd).
        - split4v; intros; exfalso; eapply SOpt.empty_in; eassumption.
      Qed.

      Lemma encodeNNF_alt_aux : forall (f : Formula) (Y_x : X.t -> YSet.t)
                                       (Vq : N.t -> VSet.t),
          (forall (q : T.Pkg.t) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x Vq q f) ->
              q = (Name.Disjunct gs, Version.Idx k) \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (q : T.Pkg.t) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNFneg Y_x Vq q f) ->
              q = (Name.Disjunct gs, Version.Idx k) \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (n : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeDisj Y_x Vq n i0 f) ->
              (n = Name.Disjunct gs /\
               exists j g, k = i0 + j /\
                           List.nth_error (disjSpine f) j = Some g /\
                           T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                             (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g))
              \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (n : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeConjNeg Y_x Vq n i0 f) ->
              (n = Name.Disjunct gs /\
               exists j g, k = i0 + j /\
                           List.nth_error (negConjSpine f) j = Some g /\
                           T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                             (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g))
              \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Y_x Vq (Name.Disjunct gs, Version.Idx k) g))).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          intros Y_x Vq.
        - split4v.
          + intros q gs k d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros q gs k d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros n i0 gs k d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FDep m ws); subst k;
              split; [lia | split; [reflexivity |]].
            apply SOed.singleton_in; subst d; reflexivity.
          + intros n i0 gs k d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FNeg (FDep m ws)); subst k;
              split; [lia | split; [reflexivity |]].
            simpl; apply SOed.singleton_in; subst d; reflexivity.
        - destruct (IHa Y_x Vq) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Y_x Vq) as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q gs k d H; simpl in H; apply T.DepRel.union_spec in H;
              destruct H as [H | H];
              [exact (IHa1 _ _ _ _ H) | exact (IHb1 _ _ _ _ H)].
          + intros q gs k d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; right; exists (FNeg a);
                subst gs; subst k; split; [reflexivity | exact H].
            * destruct (IHb4 _ _ _ _ _ H) as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              injection Eq as Eq; right; exists g; subst gs; subst k;
                split; [| exact Hin].
              simpl; exact Hg.
          + intros n i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FConj a b); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; left;
                exact H.
            * destruct (IHb1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FConj a b); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; right;
                exact H.
          + intros n i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FNeg a); subst k;
                split; [lia | split; [reflexivity |]].
              exact H.
            * destruct (IHb4 _ _ _ _ _ H) as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              left; split; [exact Eq |]; exists (S j), g;
                split; [lia | split; [exact Hg | exact Hin]].
        - destruct (IHa Y_x Vq) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Y_x Vq) as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q gs k d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; right; exists a;
                subst gs; subst k; split; [reflexivity | exact H].
            * destruct (IHb3 _ _ _ _ _ H) as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              injection Eq as Eq; right; exists g; subst gs; subst k;
                split; [| exact Hin].
              simpl; exact Hg.
          + intros q gs k d H; simpl in H; apply T.DepRel.union_spec in H;
              destruct H as [H | H];
              [exact (IHa2 _ _ _ _ H) | exact (IHb2 _ _ _ _ H)].
          + intros n i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, a; subst k; split; [lia | split; [reflexivity |]].
              exact H.
            * destruct (IHb3 _ _ _ _ _ H) as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              left; split; [exact Eq |]; exists (S j), g;
                split; [lia | split; [exact Hg | exact Hin]].
          + intros n i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FNeg (FDisj a b)); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; left;
                exact H.
            * destruct (IHb2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst n; left;
                split; [reflexivity |].
              exists 0, (FNeg (FDisj a b)); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; right;
                exact H.
        - destruct (IHa Y_x Vq) as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros q gs k d H; exact (IHa2 _ _ _ _ H).
          + intros q gs k d H; exact (IHa1 _ _ _ _ H).
          + intros n i0 gs k d H; simpl in H.
            destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
            injection Eq as Eq1 Eq2; subst n; left;
              split; [reflexivity |].
            exists 0, (FNeg a); subst k;
              split; [lia | split; [reflexivity |]].
            exact H.
          + intros n i0 gs k d H; simpl in H.
            destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
            injection Eq as Eq1 Eq2; subst n; left;
              split; [reflexivity |].
            exists 0, (FNeg (FNeg a)); subst k;
              split; [lia | split; [reflexivity |]].
            exact H.
        - split4v.
          + intros q gs k d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros q gs k d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros n i0 gs k d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FVarCmp x op y); subst k;
              split; [lia | split; [reflexivity |]].
            apply SOed.singleton_in; subst d; reflexivity.
          + intros n i0 gs k d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FNeg (FVarCmp x op y)); subst k;
              split; [lia | split; [reflexivity |]].
            simpl; apply SOed.singleton_in; subst d; reflexivity.
      Qed.

      Theorem dependees_lookupDisjunct : forall Y_x R D fs (i : Version.t),
          T.PkgSet.In (Name.Disjunct fs, i) (reduceReal Y_x R D) ->
          T.dependees (reduceDeps Y_x R D) (Name.Disjunct fs, i) =
          match disjAlt fs i with
          | Some g =>
              T.dependees
                (encodeNNF Y_x (C.versions R) (Name.Disjunct fs, i) g)
                (Name.Disjunct fs, i)
          | None => T.DependeesSet.empty
          end.
      Proof.
        intros Y_x R D fs i H; apply mem_reduceReal in H.
        destruct H as [[[pn pv] [_ Hq]] | [[p [f [HD Hw]]] | [[x [y [_ Hq]]] | [n [_ Hq]]]]];
          [unfold embedPkg in Hq; discriminate Hq | | discriminate Hq
           | discriminate Hq].
        pose proof (proj1 (witnessSet_synthetic_aux f) _ _ Hw) as Hgd.
        cbn [fst syntheticPkgs] in Hgd; apply mem_idxPkgs in Hgd.
        destruct Hgd as [k [Hk Hi]].
        assert (Hv : i = Version.Idx k) by congruence; subst i.
        cbn [disjAlt].
        destruct (List.nth_error fs k) as [g |] eqn:E;
          [| apply List.nth_error_None in E; lia].
        apply T.dependees_ext; intro h; rewrite mem_reduceDeps.
        split.
        - intros [q [f' [_ He]]].
          destruct (proj1 (encodeNNF_alt_aux f' Y_x (C.versions R)) _ _ _ _ He)
            as [Eq | [g' [Hg' Hin]]].
          + destruct q as [qn qv]; unfold embedPkg in Eq; simpl in Eq;
              discriminate.
          + rewrite E in Hg'; injection Hg' as <-; exact Hin.
        - intro Hin; exists p, f; split; [exact HD |].
          exact (proj1 (witnessSet_alt_aux f Y_x (C.versions R)) _ _ _ _ _ Hw E Hin).
      Qed.

    End Lookup.
  End Reduction.
End VariableFormula.
