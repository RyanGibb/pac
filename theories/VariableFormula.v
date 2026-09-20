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

    (* One disjunct package per disjunction, named by all of its
       alternatives: a chain of two-alternative disjuncts would introduce an
       inner name for every proper suffix of the same disjunction. *)
    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Var (x : X.t)
      | Disjunct (fs : list Formula)
      | NegDep (n : N.t) (vs : VSet.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, _ => Lt
        | Var _, Orig _ => Gt
        | Var x1, Var x2 => X.compare x1 x2
        | Var _, _ => Lt
        | Disjunct fs1, Disjunct fs2 => FListOT.compare fs1 fs2
        | Disjunct _, NegDep _ _ => Lt
        | Disjunct _, _ => Gt
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
    Module NatF := UOTCompareFacts Nat_as_OT.
    #[local] Hint Rewrite VF.compare_eq_iff YF.compare_eq_iff
      NatF.compare_eq_iff : cmp_varf.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by YF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by NatF.compare_antisym : cmp_varf.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by YF.compare_lt_trans : cmp_varf.
    #[local] Hint Extern 1 => cmp_by NatF.compare_lt_trans : cmp_varf.

    (* A synthetic version is the position of the alternative it selects, so
       a disjunction of any width is one node. *)
    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Idx (i : nat)
      | VarVal (y : Y.t).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, _ => Lt
        | Idx _, Orig _ => Gt
        | Idx i, Idx j => Nat.compare i j
        | Idx _, _ => Lt
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

    Module YSet := FSetUOT Y.
    Module SOyv := SetOps Y VersionOT YSet T.VSet.
    Definition cmpVersionSet (Y_x : YSet.t) (op : CmpOp) (y : Y.t) : T.VSet.t :=
      SOyv.filterMap (fun y' =>
          if opEvalY op y' y then Some (Version.VarVal y') else None)
        Y_x.

    (* The alternatives a disjunction offers, and the alternatives De
       Morgan reads off a negated conjunction: the disjunct package's own
       name, and the list its versions index. *)
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

    Definition idxPkgs (nm : Name.t) (k : nat) : T.PkgSet.t :=
      T.PkgSet.ofList (List.map (fun i => (nm, Version.Idx i)) (List.seq 0 k)).

    Module SOvd := SetOps V T.DepElt VSet T.DepRel.
    (* Mutual structural pairs avoid well-founded recursion on a measure; the
       De Morgan, double-negation, and complemented-comparison cases are
       inlined.  The spine walkers carry the position of the alternative
       they are encoding, and repeat their sibling's non-spine cases for
       the same reason: calling the sibling on the matched term itself
       would leave the guard condition. *)
    Fixpoint encodeNNF (Y_x : X.t -> YSet.t) (p : T.Pkg.t) (f : Formula) :
        T.DepRel.t :=
      match f with
      | FDep n vs => T.DepRel.singleton (p, (Name.Orig n, embedVS vs))
      | FConj a b => T.DepRel.union (encodeNNF Y_x p a) (encodeNNF Y_x p b)
      | FDisj a b =>
          let nm := Name.Disjunct (a :: disjSpine b) in
          T.DepRel.add (p, (nm, idxSet (List.length (a :: disjSpine b))))
            (T.DepRel.union (encodeNNF Y_x (nm, Version.Idx 0) a)
               (encodeDisj Y_x nm 1 b))
      | FNeg a => encodeNNFneg Y_x p a
      | FVarCmp x op y =>
          T.DepRel.singleton (p, (Name.Var x, cmpVersionSet (Y_x x) op y))
      end
    with encodeDisj (Y_x : X.t -> YSet.t) (nm : Name.t) (i : nat)
        (f : Formula) : T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.singleton ((nm, Version.Idx i), (Name.Orig n, embedVS vs))
      | FConj a b =>
          T.DepRel.union (encodeNNF Y_x (nm, Version.Idx i) a)
            (encodeNNF Y_x (nm, Version.Idx i) b)
      | FDisj a b =>
          T.DepRel.union (encodeNNF Y_x (nm, Version.Idx i) a)
            (encodeDisj Y_x nm (S i) b)
      | FNeg a => encodeNNFneg Y_x (nm, Version.Idx i) a
      | FVarCmp x op y =>
          T.DepRel.singleton
            ((nm, Version.Idx i), (Name.Var x, cmpVersionSet (Y_x x) op y))
      end
    with encodeNNFneg (Y_x : X.t -> YSet.t) (p : T.Pkg.t) (f : Formula) :
        T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.add (p, (Name.NegDep n vs,
                            T.VSet.singleton (Version.Idx 1)))
            (SOvd.map (fun u =>
                 ((Name.Orig n, Version.Orig u),
                  (Name.NegDep n vs, T.VSet.singleton (Version.Idx 0))))
               vs)
      | FConj a b =>
          let nm := Name.Disjunct (FNeg a :: negConjSpine b) in
          T.DepRel.add
            (p, (nm, idxSet (List.length (FNeg a :: negConjSpine b))))
            (T.DepRel.union (encodeNNFneg Y_x (nm, Version.Idx 0) a)
               (encodeConjNeg Y_x nm 1 b))
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg Y_x p a) (encodeNNFneg Y_x p b)
      | FNeg a => encodeNNF Y_x p a
      | FVarCmp x op y =>
          T.DepRel.singleton
            (p, (Name.Var x, cmpVersionSet (Y_x x) (cmpComplement op) y))
      end
    with encodeConjNeg (Y_x : X.t -> YSet.t) (nm : Name.t) (i : nat)
        (f : Formula) : T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.add
            ((nm, Version.Idx i),
             (Name.NegDep n vs, T.VSet.singleton (Version.Idx 1)))
            (SOvd.map (fun u =>
                 ((Name.Orig n, Version.Orig u),
                  (Name.NegDep n vs, T.VSet.singleton (Version.Idx 0))))
               vs)
      | FConj a b =>
          T.DepRel.union (encodeNNFneg Y_x (nm, Version.Idx i) a)
            (encodeConjNeg Y_x nm (S i) b)
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg Y_x (nm, Version.Idx i) a)
            (encodeNNFneg Y_x (nm, Version.Idx i) b)
      | FNeg a => encodeNNF Y_x (nm, Version.Idx i) a
      | FVarCmp x op y =>
          T.DepRel.singleton
            ((nm, Version.Idx i),
             (Name.Var x, cmpVersionSet (Y_x x) (cmpComplement op) y))
      end.

    Fixpoint witnessSet (p : T.Pkg.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b => T.PkgSet.union (witnessSet p a) (witnessSet p b)
      | FDisj a b =>
          let nm := Name.Disjunct (a :: disjSpine b) in
          T.PkgSet.union (idxPkgs nm (List.length (a :: disjSpine b)))
            (T.PkgSet.union (witnessSet (nm, Version.Idx 0) a)
               (witnessDisj nm 1 b))
      | FNeg a => witnessSetNeg p a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessDisj (nm : Name.t) (i : nat) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSet (nm, Version.Idx i) a)
            (witnessSet (nm, Version.Idx i) b)
      | FDisj a b =>
          T.PkgSet.union (witnessSet (nm, Version.Idx i) a)
            (witnessDisj nm (S i) b)
      | FNeg a => witnessSetNeg (nm, Version.Idx i) a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessSetNeg (p : T.Pkg.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs =>
          T.PkgSet.add (Name.NegDep n vs, Version.Idx 0)
            (T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 1))
      | FConj a b =>
          let nm := Name.Disjunct (FNeg a :: negConjSpine b) in
          T.PkgSet.union (idxPkgs nm (List.length (FNeg a :: negConjSpine b)))
            (T.PkgSet.union (witnessSetNeg (nm, Version.Idx 0) a)
               (witnessConjNeg nm 1 b))
      | FDisj a b =>
          T.PkgSet.union (witnessSetNeg p a) (witnessSetNeg p b)
      | FNeg a => witnessSet p a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessConjNeg (nm : Name.t) (i : nat) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs =>
          T.PkgSet.add (Name.NegDep n vs, Version.Idx 0)
            (T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 1))
      | FConj a b =>
          T.PkgSet.union (witnessSetNeg (nm, Version.Idx i) a)
            (witnessConjNeg nm (S i) b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetNeg (nm, Version.Idx i) a)
            (witnessSetNeg (nm, Version.Idx i) b)
      | FNeg a => witnessSet (nm, Version.Idx i) a
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

    Lemma mem_idxPkgs : forall nm k y,
        T.PkgSet.In y (idxPkgs nm k) <->
        exists i, i < k /\ y = (nm, Version.Idx i).
    Proof.
      intros nm k y; unfold idxPkgs;
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

    Definition SyntheticName (n : Name.t) : Prop :=
      (exists n' vs, n = Name.NegDep n' vs) \/ (exists fs, n = Name.Disjunct fs).

    Lemma witnessSet_name_classify_aux : forall f : Formula,
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSet p f) -> SyntheticName n) /\
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetNeg p f) -> SyntheticName n) /\
        (forall (nm : Name.t) (i : nat) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessDisj nm i f) -> SyntheticName n) /\
        (forall (nm : Name.t) (i : nat) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessConjNeg nm i f) -> SyntheticName n).
    Proof.
      unfold SyntheticName;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - repeat split.
        + intros p n v H; exfalso; exact (SOpt.empty_in _ H).
        + intros p n v H; simpl in H;
            rewrite SOpt.add_in, SOpt.singleton_in in H;
            destruct H as [H | H]; injection H as -> _; left; eauto.
        + intros nm i n v H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i n v H; simpl in H;
            rewrite SOpt.add_in, SOpt.singleton_in in H;
            destruct H as [H | H]; injection H as -> _; left; eauto.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
        + intros p n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb1 _ _ _ H)].
        + intros p n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply mem_idxPkgs in H; destruct H as [j [_ E]];
             injection E as -> _; right; eauto |].
          apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb4 _ _ _ _ H)].
        + intros nm i n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb1 _ _ _ H)].
        + intros nm i n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb4 _ _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
        + intros p n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply mem_idxPkgs in H; destruct H as [j [_ E]];
             injection E as -> _; right; eauto |].
          apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb3 _ _ _ _ H)].
        + intros p n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb2 _ _ _ H)].
        + intros nm i n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ _ H) | exact (IHb3 _ _ _ _ H)].
        + intros nm i n v H; simpl in H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ _ H) | exact (IHb2 _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
        + intros p n v H; exact (IHa2 _ _ _ H).
        + intros p n v H; exact (IHa1 _ _ _ H).
        + intros nm i n v H; exact (IHa2 _ _ _ H).
        + intros nm i n v H; exact (IHa1 _ _ _ H).
      - repeat split.
        + intros p n v H; exfalso; exact (SOpt.empty_in _ H).
        + intros p n v H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i n v H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i n v H; exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSet_not_orig : forall (p : T.Pkg.t) (f : Formula) n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSet p f).
    Proof.
      intros p f n v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
    Qed.

    Lemma witnessSet_not_var : forall (p : T.Pkg.t) (f : Formula) x v,
        ~ T.PkgSet.In (Name.Var x, v) (witnessSet p f).
    Proof.
      intros p f x v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
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
      - intros [[[n' | x' | fs | n' vs'] [v' | i | y']] [Hp' Hin]];
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
                (extractAssignment y0 Y_x S) f) /\
        (forall (nm : Name.t) (i0 i : nat),
            (forall d,
                T.DepRel.In d (encodeDisj Y_x nm i0 f) -> T.DepRel.In d D) ->
            T.PkgSet.In (nm, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (disjSpine f) ->
            Satisfies (variableFormulaResolution S)
              (extractAssignment y0 Y_x S) f) /\
        (forall (nm : Name.t) (i0 i : nat),
            (forall d,
                T.DepRel.In d (encodeConjNeg Y_x nm i0 f) -> T.DepRel.In d D) ->
            T.PkgSet.In (nm, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (negConjSpine f) ->
            ~ Satisfies (variableFormulaResolution S)
                (extractAssignment y0 Y_x S) f)).
      { intros H q f; exact (proj1 (H f) q). }
      (* the FDep dependency edge, read back through the resolution *)
      assert (Hpos : forall (q : T.Pkg.t) n vs,
                 T.DepRel.In (q, (Name.Orig n, embedVS vs)) D ->
                 T.PkgSet.In q S ->
                 Satisfies (variableFormulaResolution S)
                   (extractAssignment y0 Y_x S) (FDep n vs)).
      { intros q n vs Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        unfold embedVS in Hw; apply SOvv.mem_map in Hw;
          destruct Hw as [v [Hv ->]].
        exists v; split; [exact Hv |].
        apply mem_variableFormulaResolution; exact HwS. }
      (* the negated atom's package: version 1 says the dependency is not
         taken, and every taker of it is pinned to version 0 *)
      assert (Hneg : forall (q : T.Pkg.t) n vs,
                 (forall d,
                     T.DepRel.In d (encodeNNFneg Y_x q (FDep n vs)) ->
                     T.DepRel.In d D) ->
                 T.PkgSet.In q S ->
                 ~ Satisfies (variableFormulaResolution S)
                     (extractAssignment y0 Y_x S) (FDep n vs)).
      { intros q n vs Henc HqS.
        assert (Hd1 : T.DepRel.In
                  (q, (Name.NegDep n vs, T.VSet.singleton (Version.Idx 1))) D).
        { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
        destruct (Hdep q HqS _ _ Hd1) as [w [Hw HwS]].
        apply SOvv.singleton_in in Hw; subst w.
        intros [v [Hv HvS]].
        apply mem_variableFormulaResolution in HvS.
        assert (Hd2 : T.DepRel.In ((Name.Orig n, Version.Orig v),
                        (Name.NegDep n vs,
                         T.VSet.singleton (Version.Idx 0))) D).
        { apply Henc; simpl; apply SOed.add_in; right.
          apply SOvd.mem_map; exists v; split; [exact Hv | reflexivity]. }
        destruct (Hdep _ HvS _ _ Hd2) as [w2 [Hw2 Hw2S]].
        apply SOvv.singleton_in in Hw2; subst w2.
        assert (E := Huniq _ _ _ HwS Hw2S); discriminate. }
      (* the comparison edge: the variable block pins one value per
         variable, and the resolution's choice of it is the assignment *)
      assert (Hvar : forall (q : T.Pkg.t) x op y,
                 T.DepRel.In (q, (Name.Var x, cmpVersionSet (Y_x x) op y)) D ->
                 T.PkgSet.In q S ->
                 opEvalY op (extractAssignment y0 Y_x S x) y = true).
      { intros q x op y Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        apply mem_cmpVersionSet in Hw; destruct Hw as [y' [Hy' [HE ->]]].
        rewrite (extractAssignment_var_det y0 Y_x S x y' Huniq HwS); exact HE. }
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v.
        + intros q Henc HqS; apply (Hpos q); [| exact HqS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros q Henc HqS; exact (Hneg q n vs Henc HqS).
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          apply (Hpos (nm, Version.Idx i0)); [| exact HiS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          exact (Hneg (nm, Version.Idx i0) n vs Henc HiS).
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
          set (nm := Name.Disjunct (FNeg a :: negConjSpine b)).
          assert (Hd : T.DepRel.In
                    (q, (nm, idxSet
                           (List.length (FNeg a :: negConjSpine b)))) D).
          { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
          destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
          apply mem_idxSet in Hw; destruct Hw as [i [Hi ->]].
          simpl in Hi; intros [HsatA HsatB].
          destruct i as [| i'].
          * refine (IHa2 (nm, Version.Idx 0) _ HwS HsatA).
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; left; exact Hd'.
          * refine (IHb4 nm 1 (Datatypes.S i') _ HwS _ _ HsatB);
              [| lia | simpl; lia].
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; right; exact Hd'.
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; split.
          * apply (IHa1 (nm, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * apply (IHb1 (nm, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt; simpl.
          intros [HsatA HsatB].
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne'].
          * refine (IHa2 (nm, Version.Idx i0) _ HiS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb4 nm (Datatypes.S i0) i _ HiS _ _ HsatB); [| lia | lia].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros q Henc HqS; simpl.
          set (nm := Name.Disjunct (a :: disjSpine b)).
          assert (Hd : T.DepRel.In
                    (q, (nm, idxSet (List.length (a :: disjSpine b)))) D).
          { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
          destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
          apply mem_idxSet in Hw; destruct Hw as [i [Hi ->]].
          simpl in Hi; destruct i as [| i'].
          * left; apply (IHa1 (nm, Version.Idx 0)); [| exact HwS].
            intros d Hd'; apply Henc; simpl; apply SOed.add_in; right;
              apply T.DepRel.union_spec; left; exact Hd'.
          * right; refine (IHb3 nm 1 (Datatypes.S i') _ HwS _ _);
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
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt; simpl.
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne'].
          * left; apply (IHa1 (nm, Version.Idx i0)); [| exact HiS].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * right; refine (IHb3 nm (Datatypes.S i0) i _ HiS _ _); [| lia | lia].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; intros [HsatA | HsatB].
          * refine (IHa2 (nm, Version.Idx i0) _ HiS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb2 (nm, Version.Idx i0) _ HiS HsatB).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
        + intros q Henc HqS; exact (IHa2 q Henc HqS).
        + intros q Henc HqS; simpl; intro Hn; exact (Hn (IHa1 q Henc HqS)).
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          exact (IHa2 (nm, Version.Idx i0) Henc HiS).
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; intro Hn.
          exact (Hn (IHa1 (nm, Version.Idx i0) Henc HiS)).
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
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl.
          apply (Hvar (nm, Version.Idx i0) x op y); [| exact HiS].
          apply Henc; simpl; apply SOed.singleton_in; reflexivity.
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl.
          assert (E : opEvalY (cmpComplement op)
                        (extractAssignment y0 Y_x S x) y = true).
          { apply (Hvar (nm, Version.Idx i0) x (cmpComplement op) y);
              [| exact HiS].
            apply Henc; simpl; apply SOed.singleton_in; reflexivity. }
          rewrite opEvalY_complement in E; apply Bool.negb_true_iff in E.
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
          then T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 0)
          else T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetUntakenNeg S a) (witnessSetUntakenNeg S b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetUntakenNeg S a) (witnessSetUntakenNeg S b)
      | FNeg a => witnessSetUntaken S a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end.

    (* The alternative a disjunct package takes: the first satisfied one,
       and the last one when none is -- which is what the two-alternative
       chain this replaces settled on, and keeps the index inside idxSet. *)
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
            (if satisfiesb S sigma a
             then T.PkgSet.union (witnessSetTaken S sigma a)
                    (witnessSetUntaken S b)
             else T.PkgSet.union (witnessSetUntaken S a) (takenDisj S sigma b))
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
          if satisfiesb S sigma a
          then T.PkgSet.union (witnessSetTaken S sigma a)
                 (witnessSetUntaken S b)
          else T.PkgSet.union (witnessSetUntaken S a) (takenDisj S sigma b)
      | FNeg a => witnessSetTakenNeg S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with witnessSetTakenNeg (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
        T.PkgSet.t :=
      match f with
      | FDep n vs => T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 1)
      | FConj a b =>
          T.PkgSet.add
            (Name.Disjunct (FNeg a :: negConjSpine b),
             Version.Idx (firstSatIdx S sigma (FNeg a :: negConjSpine b)))
            (if satisfiesb S sigma a
             then T.PkgSet.union (witnessSetUntakenNeg S a)
                    (takenConjNeg S sigma b)
             else T.PkgSet.union (witnessSetTakenNeg S sigma a)
                    (witnessSetUntakenNeg S b))
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S sigma a)
            (witnessSetTakenNeg S sigma b)
      | FNeg a => witnessSetTaken S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end
    with takenConjNeg (S : PkgSet.t) (sigma : X.t -> Y.t) (f : Formula) :
        T.PkgSet.t :=
      match f with
      | FDep n vs => T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 1)
      | FConj a b =>
          if satisfiesb S sigma a
          then T.PkgSet.union (witnessSetUntakenNeg S a)
                 (takenConjNeg S sigma b)
          else T.PkgSet.union (witnessSetTakenNeg S sigma a)
                 (witnessSetUntakenNeg S b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S sigma a)
            (witnessSetTakenNeg S sigma b)
      | FNeg a => witnessSetTaken S sigma a
      | FVarCmp _ _ _ => T.PkgSet.empty
      end.

    (* The walkers and their hosts agree everywhere but the spine, so the
       host's own case is the walker's plus the synthetic version it takes. *)
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
        (if satisfiesb S sigma a
         then T.PkgSet.union (witnessSetTaken S sigma a)
                (witnessSetUntaken S b)
         else T.PkgSet.union (witnessSetUntaken S a) (takenDisj S sigma b)).
    Proof. reflexivity. Qed.

    Lemma takenConjNeg_conj_eq : forall S sigma a b,
        takenConjNeg S sigma (FConj a b) =
        (if satisfiesb S sigma a
         then T.PkgSet.union (witnessSetUntakenNeg S a)
                (takenConjNeg S sigma b)
         else T.PkgSet.union (witnessSetTakenNeg S sigma a)
                (witnessSetUntakenNeg S b)).
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

    (* Which alternative a disjunct package's taken version stands for: the
       witness of that alternative is the one the walker actually laid
       down. *)
    Lemma takenDisj_firstSat : forall S sigma f,
        Satisfies S sigma f ->
        exists g,
          List.nth_error (disjSpine f) (firstSatIdx S sigma (disjSpine f))
          = Some g /\
          Satisfies S sigma g /\
          T.PkgSet.Subset (witnessSetTaken S sigma g) (takenDisj S sigma f).
    Proof.
      intros S sigma f;
        induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros z Hz; exact Hz]).
      cbn [disjSpine];
        rewrite (firstSatIdx_cons S sigma a (disjSpine b)
                   (disjSpine_nonnil b)).
      destruct (satisfiesb S sigma a) eqn:Ea.
      - exists a; split; [reflexivity |]; split;
          [apply satisfiesb_iff; exact Ea |].
        intros z Hz; simpl; rewrite Ea;
          apply T.PkgSet.union_spec; left; exact Hz.
      - assert (Hb : Satisfies S sigma b).
        { destruct Hsat as [Ha | Hb]; [| exact Hb].
          exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
        destruct (IHb Hb) as [g [Hg [Hsg Hsub]]].
        exists g; split; [exact Hg |]; split; [exact Hsg |].
        intros z Hz; simpl; rewrite Ea;
          apply T.PkgSet.union_spec; right; exact (Hsub z Hz).
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
        induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros z Hz; exact Hz]).
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
        intros z Hz; simpl; rewrite Ea;
          apply T.PkgSet.union_spec; right; exact (Hsub z Hz).
      - exists (FNeg a); split;
          [change (satisfiesb S sigma (FNeg a))
             with (negb (satisfiesb S sigma a));
           rewrite Ea; reflexivity |]; split;
          [apply satisfiesb_false_iff; exact Ea |].
        intros z Hz; simpl; rewrite Ea;
          apply T.PkgSet.union_spec; left; exact Hz.
    Qed.

    Lemma nth_error_single : forall (x g : Formula) k,
        List.nth_error (x :: nil) k = Some g -> k = 0 /\ x = g.
    Proof.
      intros x g [| k'] H;
        [split; [reflexivity | injection H as ->; reflexivity]
        | destruct k'; discriminate H].
    Qed.

    Lemma disjSpine_untaken_sub : forall S f g,
        List.In g (disjSpine f) ->
        T.PkgSet.Subset (witnessSetUntaken S g) (witnessSetUntaken S f).
    Proof.
      intros S f;
        induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intros g Hg; simpl in Hg.
      - destruct Hg as [<- | []]; intros z Hz; exact Hz.
      - destruct Hg as [<- | []]; intros z Hz; exact Hz.
      - destruct Hg as [<- | Hg]; intros z Hz; simpl;
          apply T.PkgSet.union_spec;
          [left; exact Hz | right; exact (IHb g Hg z Hz)].
      - destruct Hg as [<- | []]; intros z Hz; exact Hz.
      - destruct Hg as [<- | []]; intros z Hz; exact Hz.
    Qed.

    Lemma negConjSpine_untaken_sub : forall S f g,
        List.In g (negConjSpine f) ->
        T.PkgSet.Subset (witnessSetUntaken S g) (witnessSetUntakenNeg S f).
    Proof.
      intros S f;
        induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intros g Hg; simpl in Hg.
      - destruct Hg as [<- | []]; intros z Hz; exact Hz.
      - destruct Hg as [<- | Hg]; intros z Hz; simpl;
          apply T.PkgSet.union_spec;
          [left; exact Hz | right; exact (IHb g Hg z Hz)].
      - destruct Hg as [<- | []]; intros z Hz; exact Hz.
      - destruct Hg as [<- | []]; intros z Hz; exact Hz.
      - destruct Hg as [<- | []]; intros z Hz; exact Hz.
    Qed.

    (* Every alternative but the taken one contributes its untaken witness,
       so a synthetic version that the resolution does not carry still has the
       shape the encoding's recursive call demands. *)
    Lemma takenDisj_untaken_others : forall S sigma f,
        Satisfies S sigma f ->
        forall k g, List.nth_error (disjSpine f) k = Some g ->
          k <> firstSatIdx S sigma (disjSpine f) ->
          T.PkgSet.Subset (witnessSetUntaken S g) (takenDisj S sigma f).
    Proof.
      intros S sigma f;
        induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intros Hsat k g Hg Hne.
      1, 2, 4, 5:
        cbn [disjSpine] in Hg, Hne;
        apply nth_error_single in Hg; destruct Hg as [-> _];
        exfalso; apply Hne; reflexivity.
      cbn [disjSpine] in Hg, Hne;
        rewrite (firstSatIdx_cons S sigma a (disjSpine b)
                   (disjSpine_nonnil b)) in Hne.
      rewrite takenDisj_disj_eq; destruct (satisfiesb S sigma a) eqn:Ea;
        simpl in Hne.
      - destruct k as [| k']; [contradiction Hne; reflexivity |].
        cbn [List.nth_error] in Hg.
        intros z Hz; apply T.PkgSet.union_spec; right.
        exact (disjSpine_untaken_sub S b g (List.nth_error_In _ _ Hg) z Hz).
      - destruct k as [| k'].
        + cbn [List.nth_error] in Hg; injection Hg as <-.
          intros z Hz; apply T.PkgSet.union_spec; left; exact Hz.
        + cbn [List.nth_error] in Hg.
          assert (Hb : Satisfies S sigma b).
          { destruct Hsat as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
          assert (Hne' : k' <> firstSatIdx S sigma (disjSpine b))
            by (intro E; apply Hne; f_equal; exact E).
          intros z Hz; apply T.PkgSet.union_spec; right.
          exact (IHb Hb k' g Hg Hne' z Hz).
    Qed.

    Lemma takenConjNeg_untaken_others : forall S sigma f,
        ~ Satisfies S sigma f ->
        forall k g, List.nth_error (negConjSpine f) k = Some g ->
          k <> firstSatIdx S sigma (negConjSpine f) ->
          T.PkgSet.Subset (witnessSetUntaken S g) (takenConjNeg S sigma f).
    Proof.
      intros S sigma f;
        induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        intros Hsat k g Hg Hne.
      1, 3, 4, 5:
        cbn [negConjSpine] in Hg, Hne;
        apply nth_error_single in Hg; destruct Hg as [-> _];
        exfalso; apply Hne; reflexivity.
      cbn [negConjSpine] in Hg, Hne;
        rewrite (firstSatIdx_cons S sigma (FNeg a) (negConjSpine b)
                   (negConjSpine_nonnil b)) in Hne.
      rewrite takenConjNeg_conj_eq;
        change (satisfiesb S sigma (FNeg a))
          with (negb (satisfiesb S sigma a)) in Hne;
        destruct (satisfiesb S sigma a) eqn:Ea; simpl in Hne.
      - destruct k as [| k'].
        + cbn [List.nth_error] in Hg; injection Hg as <-.
          intros z Hz; apply T.PkgSet.union_spec; left; exact Hz.
        + cbn [List.nth_error] in Hg.
          assert (Hb : ~ Satisfies S sigma b).
          { intro Hb; apply Hsat; split;
              [apply satisfiesb_iff; exact Ea | exact Hb]. }
          assert (Hne' : k' <> firstSatIdx S sigma (negConjSpine b))
            by (intro E; apply Hne; f_equal; exact E).
          intros z Hz; apply T.PkgSet.union_spec; right.
          exact (IHb Hb k' g Hg Hne' z Hz).
      - destruct k as [| k']; [contradiction Hne; reflexivity |].
        cbn [List.nth_error] in Hg.
        intros z Hz; apply T.PkgSet.union_spec; right.
        exact (negConjSpine_untaken_sub S b g (List.nth_error_In _ _ Hg) z Hz).
    Qed.

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
            T.PkgSet.Subset (witnessSetUntakenNeg S f) (witnessSetNeg p f)) /\
        (forall (nm : Name.t) (i : nat),
            T.PkgSet.Subset (witnessSetUntaken S f) (witnessDisj nm i f)) /\
        (forall (nm : Name.t) (i : nat),
            T.PkgSet.Subset (witnessSetUntakenNeg S f)
              (witnessConjNeg nm i f)).
    Proof.
      intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v.
        + intros p z H; exfalso; exact (SOpt.empty_in _ H).
        + intros p z; simpl; destruct (depTakenb S m ws); intro H;
            [apply SOpt.singleton_in in H; subst z;
             apply SOpt.add_in; left; reflexivity
            | exfalso; exact (SOpt.empty_in _ H)].
        + intros nm i z H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i z; simpl; destruct (depTakenb S m ws); intro H;
            [apply SOpt.singleton_in in H; subst z;
             apply SOpt.add_in; left; reflexivity
            | exfalso; exact (SOpt.empty_in _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros p z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 p _ H) | right; exact (IHb1 p _ H)].
        + intros p z; simpl; intro H;
            apply T.PkgSet.union_spec in H;
            apply T.PkgSet.union_spec; right; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb4 _ _ _ H)].
        + intros nm i z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb1 _ _ H)].
        + intros nm i z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb4 _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros p z; simpl; intro H;
            apply T.PkgSet.union_spec in H;
            apply T.PkgSet.union_spec; right; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros p z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 p _ H) | right; exact (IHb2 p _ H)].
        + intros nm i z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros nm i z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
        + intros p z; exact (IHa2 p z).
        + intros p z; exact (IHa1 p z).
        + intros nm i z; exact (IHa2 _ z).
        + intros nm i z; exact (IHa1 _ z).
      - split4v.
        + intros p z H; exfalso; exact (SOpt.empty_in _ H).
        + intros p z H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i z H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i z H; exfalso; exact (SOpt.empty_in _ H).
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
              (witnessSetNeg p f)) /\
        (forall (nm : Name.t) (i : nat),
            T.PkgSet.Subset (takenDisj S sigma f) (witnessDisj nm i f)) /\
        (forall (nm : Name.t) (i : nat),
            T.PkgSet.Subset (takenConjNeg S sigma f) (witnessConjNeg nm i f)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v.
        + intros p z H; exfalso; exact (SOpt.empty_in _ H).
        + intros p z; simpl; intro H; apply SOpt.singleton_in in H; subst z;
            apply SOpt.add_in; right; apply SOpt.singleton_in; reflexivity.
        + intros nm i z H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i z; simpl; intro H; apply SOpt.singleton_in in H; subst z;
            apply SOpt.add_in; right; apply SOpt.singleton_in; reflexivity.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_subset_witnessSet_aux S a)
            as (Ua1 & Ua2 & Ua3 & Ua4);
          pose proof (witnessSetUntaken_subset_witnessSet_aux S b)
            as (Ub1 & Ub2 & Ub3 & Ub4); split4v.
        + intros p z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 p _ H) | right; exact (IHb1 p _ H)].
        + intros p z; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; simpl witnessSetNeg;
            apply T.PkgSet.union_spec.
          * destruct H as [-> | H].
            -- left; apply mem_idxPkgs;
                 exists (firstSatIdx S sigma (FNeg a :: negConjSpine b));
                 split; [apply firstSatIdx_lt; discriminate | reflexivity].
            -- right; revert H; simpl takenConjNeg;
                 destruct (satisfiesb S sigma a); intro H;
                 apply T.PkgSet.union_spec in H;
                 apply T.PkgSet.union_spec; destruct H as [H | H];
                 [left; exact (Ua2 _ _ H) | right; exact (IHb4 _ _ _ H)
                 | left; exact (IHa2 _ _ H) | right; exact (Ub4 _ _ _ H)].
        + intros nm i z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb1 _ _ H)].
        + intros nm i z; simpl;
            destruct (satisfiesb S sigma a); intro H;
            apply T.PkgSet.union_spec in H;
            apply T.PkgSet.union_spec; destruct H as [H | H];
            [left; exact (Ua2 _ _ H) | right; exact (IHb4 _ _ _ H)
            | left; exact (IHa2 _ _ H) | right; exact (Ub4 _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_subset_witnessSet_aux S a)
            as (Ua1 & Ua2 & Ua3 & Ua4);
          pose proof (witnessSetUntaken_subset_witnessSet_aux S b)
            as (Ub1 & Ub2 & Ub3 & Ub4); split4v.
        + intros p z; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; simpl witnessSet;
            apply T.PkgSet.union_spec.
          * destruct H as [-> | H].
            -- left; apply mem_idxPkgs;
                 exists (firstSatIdx S sigma (a :: disjSpine b));
                 split; [apply firstSatIdx_lt; discriminate | reflexivity].
            -- right; revert H; simpl takenDisj;
                 destruct (satisfiesb S sigma a); intro H;
                 apply T.PkgSet.union_spec in H;
                 apply T.PkgSet.union_spec; destruct H as [H | H];
                 [left; exact (IHa1 _ _ H) | right; exact (Ub3 _ _ _ H)
                 | left; exact (Ua1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros p z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 p _ H) | right; exact (IHb2 p _ H)].
        + intros nm i z; simpl;
            destruct (satisfiesb S sigma a); intro H;
            apply T.PkgSet.union_spec in H;
            apply T.PkgSet.union_spec; destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (Ub3 _ _ _ H)
            | left; exact (Ua1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros nm i z; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
        + intros p z; exact (IHa2 p z).
        + intros p z; exact (IHa1 p z).
        + intros nm i z; exact (IHa2 _ z).
        + intros nm i z; exact (IHa1 _ z).
      - split4v.
        + intros p z H; exfalso; exact (SOpt.empty_in _ H).
        + intros p z H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i z H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i z H; exfalso; exact (SOpt.empty_in _ H).
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
            v = Version.Idx 0) /\
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntakenNeg S f) ->
            v = Version.Idx 0).
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
        v = Version.Idx 0.
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

    (* An untaken witness only ever names a NegDep whose dependency is
       taken, so it pins the same version the taken witness would. *)
    Lemma witnessSetUntaken_negDep_val_aux : forall S f,
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
            v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)) /\
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntakenNeg S f) ->
            v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)).
    Proof.
      intros S f; split; intros n vs v H;
        [assert (E : depTakenb S n vs = true)
          by (apply depTakenb_iff;
              exact (proj1 (witnessSetUntaken_negDep_exists_aux S f) _ _ _ H));
         rewrite E;
         exact (proj1 (witnessSetUntaken_negDep_det_aux S f) _ _ _ H)
        | assert (E : depTakenb S n vs = true)
          by (apply depTakenb_iff;
              exact (proj2 (witnessSetUntaken_negDep_exists_aux S f) _ _ _ H));
         rewrite E;
         exact (proj2 (witnessSetUntaken_negDep_det_aux S f) _ _ _ H)].
    Qed.

    Lemma witnessSetUntaken_disjunct_det_aux : forall S f,
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (witnessSetUntaken S f) ->
            False) /\
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (witnessSetUntakenNeg S f) ->
            False).
    Proof.
      intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
        split; intros fs v; simpl.
      - intro H; exact (SOpt.empty_in _ H).
      - destruct (depTakenb S m ws); intro H.
        + apply SOpt.singleton_in in H; congruence.
        + exact (SOpt.empty_in _ H).
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ H) | exact (proj1 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ H) | exact (proj2 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj1 IHa _ _ H) | exact (proj1 IHb _ _ H)].
      - intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
          [exact (proj2 IHa _ _ H) | exact (proj2 IHb _ _ H)].
      - exact (proj2 IHa fs v).
      - exact (proj1 IHa fs v).
      - intro H; exact (SOpt.empty_in _ H).
      - intro H; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetUntaken_disjunct_det : forall S f fs v,
        T.PkgSet.In (Name.Disjunct fs, v) (witnessSetUntaken S f) -> False.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_disjunct_det_aux S f)).
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
          solve [exfalso; exact (SOpt.empty_in _ H)
                | apply SOpt.singleton_in in H; congruence].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_disjunct_det_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_disjunct_det_aux S b) as (Ub1 & Ub2);
          split4v.
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros fs v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; simpl takenConjNeg; destruct (satisfiesb S sigma a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exfalso; exact (Ua2 _ _ H) | exact (IHb4 _ _ H)
            | exact (IHa2 _ _ H) | exfalso; exact (Ub2 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros fs v; simpl; destruct (satisfiesb S sigma a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exfalso; exact (Ua2 _ _ H) | exact (IHb4 _ _ H)
            | exact (IHa2 _ _ H) | exfalso; exact (Ub2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_disjunct_det_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_disjunct_det_aux S b) as (Ub1 & Ub2);
          split4v.
        + intros fs v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; simpl takenDisj; destruct (satisfiesb S sigma a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exfalso; exact (Ub1 _ _ H)
            | exfalso; exact (Ua1 _ _ H) | exact (IHb3 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros fs v; simpl; destruct (satisfiesb S sigma a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exfalso; exact (Ub1 _ _ H)
            | exfalso; exact (Ua1 _ _ H) | exact (IHb3 _ _ H)].
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

    Lemma witnessSetTaken_negDep_det_aux : forall S sigma f,
        (Satisfies S sigma f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTaken S sigma f) ->
           v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)) /\
        (~ Satisfies S sigma f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTakenNeg S sigma f) ->
           v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)) /\
        (Satisfies S sigma f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (takenDisj S sigma f) ->
           v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)) /\
        (~ Satisfies S sigma f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (takenConjNeg S sigma f) ->
           v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)).
    Proof.
      intros S sigma f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v; intros Hyp n vs v; simpl; intro H;
          solve
            [exfalso; exact (SOpt.empty_in _ H)
            | apply SOpt.singleton_in in H; injection H as -> -> ->;
              destruct (depTakenb S m ws) eqn:E; [| reflexivity];
              exfalso; apply Hyp, depTakenb_iff; exact E].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_negDep_val_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_negDep_val_aux S b) as (Ub1 & Ub2);
          split4v.
        + intros Hyp n vs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 (proj1 Hyp) _ _ _ H)
            | exact (IHb1 (proj2 Hyp) _ _ _ H)].
        + intros Hyp n vs v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H]; [congruence |].
          revert H; simpl takenConjNeg; destruct (satisfiesb S sigma a) eqn:Ea;
            intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * exact (Ua2 _ _ _ H).
          * apply (IHb4); [| exact H].
            intro Hb'; apply Hyp; split;
              [apply satisfiesb_iff; exact Ea | exact Hb'].
          * apply (IHa2); [apply satisfiesb_false_iff; exact Ea | exact H].
          * exact (Ub2 _ _ _ H).
        + intros Hyp n vs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 (proj1 Hyp) _ _ _ H)
            | exact (IHb1 (proj2 Hyp) _ _ _ H)].
        + intros Hyp n vs v; simpl; destruct (satisfiesb S sigma a) eqn:Ea;
            intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * exact (Ua2 _ _ _ H).
          * apply (IHb4); [| exact H].
            intro Hb'; apply Hyp; split;
              [apply satisfiesb_iff; exact Ea | exact Hb'].
          * apply (IHa2); [apply satisfiesb_false_iff; exact Ea | exact H].
          * exact (Ub2 _ _ _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_negDep_val_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_negDep_val_aux S b) as (Ub1 & Ub2);
          split4v.
        + intros Hyp n vs v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H]; [congruence |].
          revert H; simpl takenDisj; destruct (satisfiesb S sigma a) eqn:Ea;
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * apply (IHa1); [apply satisfiesb_iff; exact Ea | exact H].
          * exact (Ub1 _ _ _ H).
          * exact (Ua1 _ _ _ H).
          * apply (IHb3); [| exact H].
            destruct Hyp as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha).
        + intros Hyp n vs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply (IHa2); [intro Ha; exact (Hyp (or_introl Ha)) | exact H]
            | apply (IHb2); [intro Hb; exact (Hyp (or_intror Hb)) | exact H]].
        + intros Hyp n vs v; simpl; destruct (satisfiesb S sigma a) eqn:Ea;
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * apply (IHa1); [apply satisfiesb_iff; exact Ea | exact H].
          * exact (Ub1 _ _ _ H).
          * exact (Ua1 _ _ _ H).
          * apply (IHb3); [| exact H].
            destruct Hyp as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha).
        + intros Hyp n vs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply (IHa2); [intro Ha; exact (Hyp (or_introl Ha)) | exact H]
            | apply (IHb2); [intro Hb; exact (Hyp (or_intror Hb)) | exact H]].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v;
          intros Hyp n vs v.
        + exact (IHa2 Hyp n vs v).
        + exact (IHa1 (satisfies_double_neg S sigma a Hyp) n vs v).
        + exact (IHa2 Hyp n vs v).
        + exact (IHa1 (satisfies_double_neg S sigma a Hyp) n vs v).
      - split4v; intros Hyp n vs v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_negDep_det : forall S sigma f,
        Satisfies S sigma f ->
        forall n vs v,
          T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTaken S sigma f) ->
          v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1).
    Proof.
      intros S sigma f;
        exact (proj1 (witnessSetTaken_negDep_det_aux S sigma f)).
    Qed.

    Lemma witnessSetUntaken_name_classify_aux : forall S f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetUntaken S f) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetUntakenNeg S f) -> SyntheticName n).
    Proof.
      unfold SyntheticName; intros S f;
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
        T.PkgSet.In (n, v) (witnessSetUntaken S f) -> SyntheticName n.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_name_classify_aux S f)).
    Qed.

    Lemma witnessSetTaken_name_classify_aux : forall S sigma f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTaken S sigma f) ->
            SyntheticName n) /\
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
          solve [exfalso; exact (SOpt.empty_in _ H)
                | apply SOpt.singleton_in in H; injection H as -> _;
                  left; exists m, ws; reflexivity].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_name_classify_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_name_classify_aux S b) as (Ub1 & Ub2);
          unfold SyntheticName in Ua1, Ua2, Ub1, Ub2; split4v.
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; right; eauto |].
          revert H; simpl takenConjNeg; destruct (satisfiesb S sigma a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (Ua2 _ _ H) | exact (IHb4 _ _ H)
            | exact (IHa2 _ _ H) | exact (Ub2 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; simpl; destruct (satisfiesb S sigma a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (Ua2 _ _ H) | exact (IHb4 _ _ H)
            | exact (IHa2 _ _ H) | exact (Ub2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_name_classify_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_name_classify_aux S b) as (Ub1 & Ub2);
          unfold SyntheticName in Ua1, Ua2, Ub1, Ub2; split4v.
        + intros n v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; right; eauto |].
          revert H; simpl takenDisj; destruct (satisfiesb S sigma a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (Ub1 _ _ H)
            | exact (Ua1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros n v; simpl; destruct (satisfiesb S sigma a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (Ub1 _ _ H)
            | exact (Ua1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v; intros n v;
          [exact (IHa2 n v) | exact (IHa1 n v)
          | exact (IHa2 n v) | exact (IHa1 n v)].
      - split4v; intros n v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma witnessSetTaken_name_classify :
      forall S sigma f (n : Name.t) (v : Version.t),
        T.PkgSet.In (n, v) (witnessSetTaken S sigma f) -> SyntheticName n.
    Proof.
      intros S sigma f;
        exact (proj1 (witnessSetTaken_name_classify_aux S sigma f)).
    Qed.

    Lemma witnessSetUntaken_not_orig : forall S f n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSetUntaken S f).
    Proof.
      intros S f n v H.
      destruct (witnessSetUntaken_name_classify S f _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
    Qed.

    Lemma witnessSetTaken_not_orig : forall S sigma f n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSetTaken S sigma f).
    Proof.
      intros S sigma f n v H.
      destruct (witnessSetTaken_name_classify S sigma f _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
    Qed.

    Lemma witnessSetUntaken_not_var : forall S f x v,
        ~ T.PkgSet.In (Name.Var x, v) (witnessSetUntaken S f).
    Proof.
      intros S f x v H.
      destruct (witnessSetUntaken_name_classify S f _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
    Qed.

    Lemma witnessSetTaken_not_var : forall S sigma f x v,
        ~ T.PkgSet.In (Name.Var x, v) (witnessSetTaken S sigma f).
    Proof.
      intros S sigma f x v H.
      destruct (witnessSetTaken_name_classify S sigma f _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
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

    (* Passing an alternative up through one set constructor: nav is the
       step from the inner witness set to the outer one, which is all that
       differs between the sixteen places this conclusion is rebuilt. *)
    Ltac pick_alt H nav :=
      let g0 := fresh "g0" in let Hg0 := fresh "Hg0" in
      let Hs0 := fresh "Hs0" in let Hu0 := fresh "Hu0" in
      destruct H as [g0 [Hg0 [Hs0 Hu0]]];
      exists g0; split; [exact Hg0 |]; split; [exact Hs0 |];
      let y0 := fresh "y0" in let Hy0 := fresh "Hy0" in
      intros y0 Hy0; nav; exact (Hu0 y0 Hy0).

    (* Reading a synthetic version out of a taken witness: it names an
       alternative that holds, and that alternative's own taken witness is
       already part of the same set. *)
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
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i)
             (takenDisj S sigma f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
             T.PkgSet.Subset (witnessSetTaken S sigma g)
               (takenDisj S sigma f)) /\
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
          solve [exfalso; exact (SOpt.empty_in _ H)
                | apply SOpt.singleton_in in H; discriminate H].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_disjunct_det_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_disjunct_det_aux S b) as (Ub1 & Ub2);
          split4v.
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
              destruct (satisfiesb S sigma a) eqn:Ea; intro H;
              apply T.PkgSet.union_spec in H; destruct H as [H | H].
            -- exfalso; exact (Ua2 _ _ H).
            -- assert (Hb : ~ Satisfies S sigma b).
               { intro Hb; apply Hyp; split;
                   [apply satisfiesb_iff; exact Ea | exact Hb]. }
               pick_alt (IHb4 Hb _ _ H)
                 ltac:(apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; right).
            -- pick_alt (IHa2 (proj1 (satisfiesb_false_iff S sigma a) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; left).
            -- exfalso; exact (Ub2 _ _ H).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [pick_alt (IHa1 (proj1 Hyp) _ _ H)
               ltac:(apply T.PkgSet.union_spec; left)
            | pick_alt (IHb1 (proj2 Hyp) _ _ H)
                ltac:(apply T.PkgSet.union_spec; right)].
        + intros Hyp fs i; rewrite takenConjNeg_conj_eq;
            destruct (satisfiesb S sigma a) eqn:Ea; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * exfalso; exact (Ua2 _ _ H).
          * assert (Hb : ~ Satisfies S sigma b).
            { intro Hb; apply Hyp; split;
                [apply satisfiesb_iff; exact Ea | exact Hb]. }
            pick_alt (IHb4 Hb _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
          * pick_alt (IHa2 (proj1 (satisfiesb_false_iff S sigma a) Ea) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * exfalso; exact (Ub2 _ _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_disjunct_det_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_disjunct_det_aux S b) as (Ub1 & Ub2);
          split4v.
        + intros Hyp fs i; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H].
          * injection H as -> ->;
              pick_alt (takenDisj_firstSat S sigma (FDisj a b) Hyp)
                ltac:(apply SOpt.add_in; right).
          * revert H; rewrite takenDisj_disj_eq;
              destruct (satisfiesb S sigma a) eqn:Ea; intro H;
              apply T.PkgSet.union_spec in H; destruct H as [H | H].
            -- pick_alt (IHa1 (proj1 (satisfiesb_iff S sigma a) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; left).
            -- exfalso; exact (Ub1 _ _ H).
            -- exfalso; exact (Ua1 _ _ H).
            -- assert (Hb : Satisfies S sigma b).
               { destruct Hyp as [Ha | Hb]; [| exact Hb].
                 exfalso;
                   exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
               pick_alt (IHb3 Hb _ _ H)
                 ltac:(apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; right).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa2 (fun Ha => Hyp (or_introl Ha)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * pick_alt (IHb2 (fun Hb => Hyp (or_intror Hb)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
        + intros Hyp fs i; rewrite takenDisj_disj_eq;
            destruct (satisfiesb S sigma a) eqn:Ea; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa1 (proj1 (satisfiesb_iff S sigma a) Ea) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * exfalso; exact (Ub1 _ _ H).
          * exfalso; exact (Ua1 _ _ H).
          * assert (Hb : Satisfies S sigma b).
            { destruct Hyp as [Ha | Hb]; [| exact Hb].
              exfalso; exact (proj1 (satisfiesb_false_iff S sigma a) Ea Ha). }
            pick_alt (IHb3 Hb _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa2 (fun Ha => Hyp (or_introl Ha)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * pick_alt (IHb2 (fun Hb => Hyp (or_intror Hb)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v;
          intros Hyp fs i.
        + exact (IHa2 Hyp fs i).
        + exact (IHa1 (satisfies_double_neg S sigma a Hyp) fs i).
        + exact (IHa2 Hyp fs i).
        + exact (IHa1 (satisfies_double_neg S sigma a Hyp) fs i).
      - split4v; intros Hyp fs i; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
    Qed.

    Lemma coreResolution_disj : forall S D sigma fs i,
        (forall p, PkgSet.In p S ->
         forall f, DepRel.In (p, f) D -> Satisfies S sigma f) ->
        T.PkgSet.In (Name.Disjunct fs, Version.Idx i)
          (coreResolution S D sigma) ->
        exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
          T.PkgSet.Subset (witnessSetTaken S sigma g)
            (coreResolution S D sigma).
    Proof.
      intros S D sigma fs i Hclo H; apply mem_coreResolution in H.
      destruct H as [[p [_ Hp]] | [[p [g [Hd Hw]]] | [x Hq]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - pose proof (witnessSet_subset_coreResolution S D sigma p g Hd) as Hsub.
        revert Hw Hsub; destruct (PkgSet.mem p S) eqn:Ep; intros Hw Hsub.
        + assert (Hsat : Satisfies S sigma g).
          { apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hd]. }
          destruct (proj1 (witnessSetTaken_disj_mono_aux S sigma g)
                      Hsat fs i Hw) as [h [Hh [Hsh Hsubh]]].
          exists h; split; [exact Hh |]; split; [exact Hsh |].
          intros z Hz; apply Hsub, Hsubh; exact Hz.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ Hw).
      - discriminate.
    Qed.

    Lemma encodeNNF_dep_closure_aux :
      forall (S : PkgSet.t) (sigma : X.t -> Y.t) (Y_x : X.t -> YSet.t)
             (w : T.PkgSet.t),
        (forall x, YSet.In (sigma x) (Y_x x)) ->
        (forall p, PkgSet.In p S -> T.PkgSet.In (embedPkg p) w) ->
        (forall n v, T.PkgSet.In (Name.Orig n, v) w ->
           exists p, PkgSet.In p S /\ embedPkg p = (Name.Orig n, v)) ->
        (forall fs i, T.PkgSet.In (Name.Disjunct fs, Version.Idx i) w ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S sigma g /\
             T.PkgSet.Subset (witnessSetTaken S sigma g) w) ->
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
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w) /\
          (forall (nm : Name.t) (i0 : nat),
              (forall k g, List.nth_error (disjSpine f) k = Some g ->
                 (~ T.PkgSet.In (nm, Version.Idx (i0 + k)) w /\
                  T.PkgSet.Subset (witnessSetUntaken S g) w) \/
                 (Satisfies S sigma g /\
                  T.PkgSet.Subset (witnessSetTaken S sigma g) w)) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeDisj Y_x nm i0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w) /\
          (forall (nm : Name.t) (i0 : nat),
              (forall k g, List.nth_error (negConjSpine f) k = Some g ->
                 (~ T.PkgSet.In (nm, Version.Idx (i0 + k)) w /\
                  T.PkgSet.Subset (witnessSetUntaken S g) w) \/
                 (Satisfies S sigma g /\
                  T.PkgSet.Subset (witnessSetTaken S sigma g) w)) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeConjNeg Y_x nm i0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w).
    Proof.
      intros S sigma Y_x w Hins Hemb Horig Hdisj Hvar f.
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa | x op y].
      - split4v.
        + intros q0 Hwit q m ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [[Hq0 _] | [Hsat _]];
            [exfalso; exact (Hq0 Hqw) |].
          destruct Hsat as [u [Hu HuS]].
          exists (Version.Orig u); split;
            [unfold embedVS; apply SOvv.mem_map;
             exists u; split; [exact Hu | reflexivity]
            | exact (Hemb (n, u) HuS)].
        + intros q0 Hwit q m ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [[Hq0 _] | [_ Hsub]];
              [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx 1); split;
              [apply SOvv.singleton_in; reflexivity |].
            apply Hsub, SOpt.singleton_in; reflexivity.
          * apply SOvd.mem_map in He; destruct He as [u [Hu He]];
              injection He as -> -> ->.
            destruct (Horig n (Version.Orig u) Hqw) as [[pn pv] [HpS Hpe]].
            unfold embedPkg in Hpe; simpl in Hpe; injection Hpe as -> ->.
            destruct Hwit as [[_ Hsub] | [Hns _]].
            -- assert (E : depTakenb S n vs = true)
                 by (apply depTakenb_iff; exists u; split; assumption).
               exists (Version.Idx 0);
                 split; [apply SOvv.singleton_in; reflexivity |].
               apply Hsub.
               change (T.PkgSet.In (Name.NegDep n vs, Version.Idx 0)
                         (if depTakenb S n vs
                          then T.PkgSet.singleton
                                 (Name.NegDep n vs, Version.Idx 0)
                          else T.PkgSet.empty)).
               rewrite E; apply SOpt.singleton_in; reflexivity.
            -- exfalso; apply Hns; exists u; split; assumption.
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FDep n vs) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [[Hq0 _] | [Hsat _]];
            [exfalso; exact (Hq0 Hqw) |].
          destruct Hsat as [u [Hu HuS]].
          exists (Version.Orig u); split;
            [unfold embedVS; apply SOvv.mem_map;
             exists u; split; [exact Hu | reflexivity]
            | exact (Hemb (n, u) HuS)].
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FDep n vs)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [[Hq0 _] | [_ Hsub]];
              [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx 1); split;
              [apply SOvv.singleton_in; reflexivity |].
            apply Hsub, SOpt.singleton_in; reflexivity.
          * apply SOvd.mem_map in He; destruct He as [u [Hu He]];
              injection He as -> -> ->.
            destruct (Horig n (Version.Orig u) Hqw) as [[pn pv] [HpS Hpe]].
            unfold embedPkg in Hpe; simpl in Hpe; injection Hpe as -> ->.
            destruct Hwit as [[_ Hsub] | [Hns _]].
            -- assert (E : depTakenb S n vs = true)
                 by (apply depTakenb_iff; exists u; split; assumption).
               exists (Version.Idx 0);
                 split; [apply SOvv.singleton_in; reflexivity |].
               apply Hsub.
               change (T.PkgSet.In (Name.NegDep n vs, Version.Idx 0)
                         (if depTakenb S n vs
                          then T.PkgSet.singleton
                                 (Name.NegDep n vs, Version.Idx 0)
                          else T.PkgSet.empty)).
               rewrite E; apply SOpt.singleton_in; reflexivity.
            -- exfalso; apply Hns; exists u; split; assumption.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros q0 Hwit q m ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 q0 _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [exact (proj1 Hsat) |]];
              intros z Hz; apply Hsub, T.PkgSet.union_spec; left; exact Hz.
          * refine (IHb1 q0 _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [exact (proj2 Hsat) |]];
              intros z Hz; apply Hsub, T.PkgSet.union_spec; right; exact Hz.
        + intros q0 Hwit q m ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [[Hq0 _] | [_ Hsub]];
              [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx
                      (firstSatIdx S sigma (FNeg a :: negConjSpine b))); split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S sigma (FNeg a :: negConjSpine b)); split;
                 [apply firstSatIdx_lt; discriminate | reflexivity].
            -- apply Hsub; rewrite witnessSetTakenNeg_conj_eq;
                 apply SOpt.add_in; left; reflexivity.
          * apply T.DepRel.union_spec in He; destruct He as [He | He].
            -- refine (IHa2 (Name.Disjunct (FNeg a :: negConjSpine b),
                             Version.Idx 0) _ q m ws He Hqw).
               destruct (T.PkgSet.mem
                           (Name.Disjunct (FNeg a :: negConjSpine b),
                            Version.Idx 0) w) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [g [Hg [Hsg Hsub]]].
                  cbn [List.nth_error] in Hg; injection Hg as <-.
                  right; split; [exact Hsg | exact Hsub].
               ++ left; split;
                    [intro Hin; apply T.PkgSet.mem_spec in Hin;
                     discriminate (eq_trans (eq_sym Hin) EM) |].
                  destruct Hwit as [[_ Hsub] | [Hsat Hsub]].
                  ** intros z Hz; apply Hsub; simpl;
                       apply T.PkgSet.union_spec; left; exact Hz.
                  ** destruct (Nat_as_OT.eq_dec 0
                                 (firstSatIdx S sigma
                                    (FNeg a :: negConjSpine b)))
                       as [E0 | Hne].
                     --- exfalso.
                         assert (Hin : T.PkgSet.In
                                   (Name.Disjunct (FNeg a :: negConjSpine b),
                                    Version.Idx 0) w).
                         { apply Hsub; rewrite witnessSetTakenNeg_conj_eq,
                             E0; apply SOpt.add_in; left; reflexivity. }
                         apply T.PkgSet.mem_spec in Hin;
                         discriminate (eq_trans (eq_sym Hin) EM).
                     --- intros z Hz; apply Hsub;
                           rewrite witnessSetTakenNeg_conj_eq;
                           apply SOpt.add_in; right;
                           exact (takenConjNeg_untaken_others S sigma
                                    (FConj a b) Hsat 0 (FNeg a) eq_refl Hne
                                    z Hz).
            -- refine (IHb4 (Name.Disjunct (FNeg a :: negConjSpine b)) 1
                         _ q m ws He Hqw).
               intros k g Hg.
               assert (Hg' : List.nth_error (FNeg a :: negConjSpine b) (1 + k)
                             = Some g) by exact Hg.
               destruct (T.PkgSet.mem
                           (Name.Disjunct (FNeg a :: negConjSpine b),
                            Version.Idx (1 + k)) w) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [g' [Hg2 [Hsg Hsub]]].
                  rewrite Hg' in Hg2; injection Hg2 as <-.
                  right; split; [exact Hsg | exact Hsub].
               ++ left; split;
                    [intro Hin; apply T.PkgSet.mem_spec in Hin;
                     discriminate (eq_trans (eq_sym Hin) EM) |].
                  destruct Hwit as [[_ Hsub] | [Hsat Hsub]].
                  ** intros z Hz; apply Hsub; simpl;
                       apply T.PkgSet.union_spec; right;
                       exact (negConjSpine_untaken_sub S b g
                                (List.nth_error_In _ _ Hg) z Hz).
                  ** destruct (Nat_as_OT.eq_dec (1 + k)
                                 (firstSatIdx S sigma
                                    (FNeg a :: negConjSpine b)))
                       as [E0 | Hne].
                     --- exfalso.
                         assert (Hin : T.PkgSet.In
                                   (Name.Disjunct (FNeg a :: negConjSpine b),
                                    Version.Idx (1 + k)) w).
                         { apply Hsub; rewrite witnessSetTakenNeg_conj_eq,
                             E0; apply SOpt.add_in; left; reflexivity. }
                         apply T.PkgSet.mem_spec in Hin;
                         discriminate (eq_trans (eq_sym Hin) EM).
                     --- intros z Hz; apply Hsub;
                           rewrite witnessSetTakenNeg_conj_eq;
                           apply SOpt.add_in; right;
                           exact (takenConjNeg_untaken_others S sigma
                                    (FConj a b) Hsat (1 + k) g Hg' Hne z Hz).
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FConj a b) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 (nm, Version.Idx i0) _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [exact (proj1 Hsat) |]];
              intros z Hz; apply Hsub, T.PkgSet.union_spec; left; exact Hz.
          * refine (IHb1 (nm, Version.Idx i0) _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [exact (proj2 Hsat) |]];
              intros z Hz; apply Hsub, T.PkgSet.union_spec; right; exact Hz.
        + intros nm i0 Hspine q m ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 (nm, Version.Idx i0) _ q m ws He Hqw).
            assert (Hwit := Hspine 0 (FNeg a) eq_refl);
              replace (i0 + 0) with i0 in Hwit by lia.
            exact Hwit.
          * refine (IHb4 nm (Datatypes.S i0) _ q m ws He Hqw).
            intros k g Hg.
            assert (H := Hspine (Datatypes.S k) g Hg).
            replace (Datatypes.S i0 + k) with (i0 + Datatypes.S k) by lia.
            exact H.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
        + intros q0 Hwit q m ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [[Hq0 _] | [_ Hsub]];
              [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx (firstSatIdx S sigma (a :: disjSpine b)));
              split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S sigma (a :: disjSpine b)); split;
                 [apply firstSatIdx_lt; discriminate | reflexivity].
            -- apply Hsub; rewrite witnessSetTaken_disj_eq;
                 apply SOpt.add_in; left; reflexivity.
          * apply T.DepRel.union_spec in He; destruct He as [He | He].
            -- refine (IHa1 (Name.Disjunct (a :: disjSpine b),
                             Version.Idx 0) _ q m ws He Hqw).
               destruct (T.PkgSet.mem (Name.Disjunct (a :: disjSpine b),
                                       Version.Idx 0) w) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [g [Hg [Hsg Hsub]]].
                  cbn [List.nth_error] in Hg; injection Hg as <-.
                  right; split; [exact Hsg | exact Hsub].
               ++ left; split;
                    [intro Hin; apply T.PkgSet.mem_spec in Hin;
                     discriminate (eq_trans (eq_sym Hin) EM) |].
                  destruct Hwit as [[_ Hsub] | [Hsat Hsub]].
                  ** intros z Hz; apply Hsub; simpl;
                       apply T.PkgSet.union_spec; left; exact Hz.
                  ** destruct (Nat_as_OT.eq_dec 0
                                 (firstSatIdx S sigma (a :: disjSpine b)))
                       as [E0 | Hne].
                     --- exfalso.
                         assert (Hin : T.PkgSet.In
                                   (Name.Disjunct (a :: disjSpine b),
                                    Version.Idx 0) w).
                         { apply Hsub; rewrite witnessSetTaken_disj_eq, E0;
                             apply SOpt.add_in; left; reflexivity. }
                         apply T.PkgSet.mem_spec in Hin;
                         discriminate (eq_trans (eq_sym Hin) EM).
                     --- intros z Hz; apply Hsub;
                           rewrite witnessSetTaken_disj_eq;
                           apply SOpt.add_in; right;
                           exact (takenDisj_untaken_others S sigma (FDisj a b)
                                    Hsat 0 a eq_refl Hne z Hz).
            -- refine (IHb3 (Name.Disjunct (a :: disjSpine b)) 1
                         _ q m ws He Hqw).
               intros k g Hg.
               assert (Hg' : List.nth_error (a :: disjSpine b) (1 + k)
                             = Some g) by exact Hg.
               destruct (T.PkgSet.mem (Name.Disjunct (a :: disjSpine b),
                                       Version.Idx (1 + k)) w) eqn:EM.
               ++ apply T.PkgSet.mem_spec in EM.
                  destruct (Hdisj _ _ EM) as [g' [Hg2 [Hsg Hsub]]].
                  rewrite Hg' in Hg2; injection Hg2 as <-.
                  right; split; [exact Hsg | exact Hsub].
               ++ left; split;
                    [intro Hin; apply T.PkgSet.mem_spec in Hin;
                     discriminate (eq_trans (eq_sym Hin) EM) |].
                  destruct Hwit as [[_ Hsub] | [Hsat Hsub]].
                  ** intros z Hz; apply Hsub; simpl;
                       apply T.PkgSet.union_spec; right;
                       exact (disjSpine_untaken_sub S b g
                                (List.nth_error_In _ _ Hg) z Hz).
                  ** destruct (Nat_as_OT.eq_dec (1 + k)
                                 (firstSatIdx S sigma (a :: disjSpine b)))
                       as [E0 | Hne].
                     --- exfalso.
                         assert (Hin : T.PkgSet.In
                                   (Name.Disjunct (a :: disjSpine b),
                                    Version.Idx (1 + k)) w).
                         { apply Hsub; rewrite witnessSetTaken_disj_eq, E0;
                             apply SOpt.add_in; left; reflexivity. }
                         apply T.PkgSet.mem_spec in Hin;
                         discriminate (eq_trans (eq_sym Hin) EM).
                     --- intros z Hz; apply Hsub;
                           rewrite witnessSetTaken_disj_eq;
                           apply SOpt.add_in; right;
                           exact (takenDisj_untaken_others S sigma (FDisj a b)
                                    Hsat (1 + k) g Hg' Hne z Hz).
        + intros q0 Hwit q m ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 q0 _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [intro Ha; exact (Hns (or_introl Ha)) |]];
              intros z Hz; apply Hsub, T.PkgSet.union_spec; left; exact Hz.
          * refine (IHb2 q0 _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros z Hz; apply Hsub, T.PkgSet.union_spec; right; exact Hz.
        + intros nm i0 Hspine q m ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 (nm, Version.Idx i0) _ q m ws He Hqw).
            assert (Hwit := Hspine 0 a eq_refl);
              replace (i0 + 0) with i0 in Hwit by lia.
            exact Hwit.
          * refine (IHb3 nm (Datatypes.S i0) _ q m ws He Hqw).
            intros k g Hg.
            assert (H := Hspine (Datatypes.S k) g Hg).
            replace (Datatypes.S i0 + k) with (i0 + Datatypes.S k) by lia.
            exact H.
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FDisj a b)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 (nm, Version.Idx i0) _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [intro Ha; exact (Hns (or_introl Ha)) |]];
              intros z Hz; apply Hsub, T.PkgSet.union_spec; left; exact Hz.
          * refine (IHb2 (nm, Version.Idx i0) _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros z Hz; apply Hsub, T.PkgSet.union_spec; right; exact Hz.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
        + intros q0 Hwit q m ws Henc Hqw.
          exact (IHa2 q0 Hwit q m ws Henc Hqw).
        + intros q0 Hwit q m ws Henc Hqw.
          destruct Hwit as [[Hq0 Hsub] | [Hnn Hsub]];
            [exact (IHa1 q0 (or_introl (conj Hq0 Hsub)) q m ws Henc Hqw)
            | exact (IHa1 q0
                       (or_intror
                          (conj (satisfies_double_neg S sigma a Hnn) Hsub))
                       q m ws Henc Hqw)].
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg a) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          exact (IHa2 (nm, Version.Idx i0) Hwit q m ws Henc Hqw).
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FNeg a)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          destruct Hwit as [[Hq0 Hsub] | [Hnn Hsub]];
            [exact (IHa1 (nm, Version.Idx i0) (or_introl (conj Hq0 Hsub))
                      q m ws Henc Hqw)
            | exact (IHa1 (nm, Version.Idx i0)
                       (or_intror
                          (conj (satisfies_double_neg S sigma a Hnn) Hsub))
                       q m ws Henc Hqw)].
      - split4v.
        + intros q0 Hwit q m ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [[Hq0 _] | [Hsat _]];
            [exfalso; exact (Hq0 Hqw) |].
          exists (Version.VarVal (sigma x)); split;
            [apply mem_cmpVersionSet; exists (sigma x);
             split; [apply Hins | split; [exact Hsat | reflexivity]]
            | exact (Hvar x)].
        + intros q0 Hwit q m ws Henc Hqw.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [[Hq0 _] | [Hns _]];
            [exfalso; exact (Hq0 Hqw) |].
          exists (Version.VarVal (sigma x)); split; [| exact (Hvar x)].
          apply mem_cmpVersionSet; exists (sigma x);
            split; [apply Hins |].
          split; [| reflexivity].
          rewrite opEvalY_complement; apply Bool.negb_true_iff.
          destruct (opEvalY op (sigma x) y) eqn:E;
            [exfalso; exact (Hns E) | reflexivity].
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FVarCmp x op y) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [[Hq0 _] | [Hsat _]];
            [exfalso; exact (Hq0 Hqw) |].
          exists (Version.VarVal (sigma x)); split;
            [apply mem_cmpVersionSet; exists (sigma x);
             split; [apply Hins | split; [exact Hsat | reflexivity]]
            | exact (Hvar x)].
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FNeg (FVarCmp x op y)) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply SOed.singleton_in in Henc; injection Henc as -> -> ->.
          destruct Hwit as [[Hq0 _] | [Hns _]];
            [exfalso; exact (Hq0 Hqw) |].
          exists (Version.VarVal (sigma x)); split; [| exact (Hvar x)].
          apply mem_cmpVersionSet; exists (sigma x);
            split; [apply Hins |].
          split; [| reflexivity].
          rewrite opEvalY_complement; apply Bool.negb_true_iff.
          destruct (opEvalY op (sigma x) y) eqn:E;
            [exfalso; exact (Hns E) | reflexivity].
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
      assert (Hdisj := fun fs i => coreResolution_disj S D sigma fs i Hclo).
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
            Hins Hemb Horig Hdisj Hvar g) (embedPkg p) _ q m vs Henc Hq).
          right; split.
          * apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hpg].
          * pose proof (witnessSet_subset_coreResolution S D sigma p g Hpg)
              as Hs; rewrite Ep in Hs; exact Hs.
        + refine (proj1 (encodeNNF_dep_closure_aux S sigma Y_x _
            Hins Hemb Horig Hdisj Hvar g) (embedPkg p) _ q m vs Henc Hq).
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
        + destruct n as [n0 | x | fs | n0 vs0].
          * exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
              [exact (witnessSetTaken_not_orig _ _ _ _ _ Hw1)
              | exact (witnessSetUntaken_not_orig _ _ _ _ Hw1)].
          * exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
              [exact (witnessSetTaken_not_var _ _ _ _ _ Hw1)
              | exact (witnessSetUntaken_not_var _ _ _ _ Hw1)].
          * assert (G : forall p g v0, DepRel.In (p, g) D ->
                T.PkgSet.In (Name.Disjunct fs, v0)
                  (if PkgSet.mem p S then witnessSetTaken S sigma g
                   else witnessSetUntaken S g) ->
                v0 = Version.Idx (firstSatIdx S sigma fs)).
            { intros p g v0 _ Hw; revert Hw;
                destruct (PkgSet.mem p S); intro Hw.
              - exact (witnessSetTaken_disjunct_det _ _ _ _ _ Hw).
              - exfalso;
                  exact (witnessSetUntaken_disjunct_det _ _ _ _ Hw). }
            rewrite (G _ _ _ Hd1 Hw1), (G _ _ _ Hd2 Hw2); reflexivity.
          * assert (G : forall p g v0, DepRel.In (p, g) D ->
                T.PkgSet.In (Name.NegDep n0 vs0, v0)
                  (if PkgSet.mem p S then witnessSetTaken S sigma g
                   else witnessSetUntaken S g) ->
                v0 =
                  (if depTakenb S n0 vs0
                   then Version.Idx 0 else Version.Idx 1)).
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
      | ADisj (fs : list Formula)
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
          | ADisj fs1, ADisj fs2 => FListOT.compare fs1 fs2
          | ADisj _, AVar _ _ => Lt
          | ADisj _, _ => Gt
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
            AtomSet.add (ADisj (a :: disjSpine b))
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
            AtomSet.add (ADisj (FNeg a :: negConjSpine b))
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

      Definition disjAlt (fs : list Formula) (i : Version.t) :
          option Formula :=
        match i with
        | Version.Idx k => List.nth_error fs k
        | _ => None
        end.

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
                VSet.In v vs) /\
          (forall (nm : Name.t) (i0 : nat) n v (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig n, Version.Orig v), d)
                (encodeDisj Y_x nm i0 f) ->
              exists vs, AtomSet.In (ANeg n vs) (negAtoms f) /\
                VSet.In v vs) /\
          (forall (nm : Name.t) (i0 : nat) n v (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig n, Version.Orig v), d)
                (encodeConjNeg Y_x nm i0 f) ->
              exists vs, AtomSet.In (ANeg n vs) (negAtomsNeg f) /\
                VSet.In v vs).
      Proof.
        intros Y_x;
          induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - split4v.
          + intros q n v d H; apply SOed.singleton_in in H; left; congruence.
          + intros q n v d H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
            apply SOvd.mem_map in H; destruct H as [u [Hu He]].
            injection He as -> -> ->.
            right; exists ws; split;
              [apply AtomSet.singleton_spec; reflexivity | exact Hu].
          + intros nm i0 n v d H; apply SOed.singleton_in in H; discriminate H.
          + intros nm i0 n v d H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [discriminate H |].
            apply SOvd.mem_map in H; destruct H as [u [Hu He]].
            injection He as -> -> ->.
            exists ws; split;
              [apply AtomSet.singleton_spec; reflexivity | exact Hu].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q n v d H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [left; exact E |].
              right; exists vs; split;
                [apply AtomSet.union_spec; left; exact Ha | exact Hv].
            * destruct (IHb1 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [left; exact E |].
              right; exists vs; split;
                [apply AtomSet.union_spec; right; exact Ha | exact Hv].
          + intros q n v d H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              right; exists vs; split;
                [apply AtomSet.union_spec; left; exact Ha | exact Hv].
            * destruct (IHb4 _ _ _ _ _ H) as [vs [Ha Hv]].
              right; exists vs; split;
                [apply AtomSet.union_spec; right; exact Ha | exact Hv].
          + intros nm i0 n v d H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              exists vs; split;
                [apply AtomSet.union_spec; left; exact Ha | exact Hv].
            * destruct (IHb1 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              exists vs; split;
                [apply AtomSet.union_spec; right; exact Ha | exact Hv].
          + intros nm i0 n v d H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              exists vs; split;
                [apply AtomSet.union_spec; left; exact Ha | exact Hv].
            * destruct (IHb4 _ _ _ _ _ H) as [vs [Ha Hv]].
              exists vs; split;
                [apply AtomSet.union_spec; right; exact Ha | exact Hv].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q n v d H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              right; exists vs; split;
                [apply AtomSet.union_spec; left; exact Ha | exact Hv].
            * destruct (IHb3 _ _ _ _ _ H) as [vs [Ha Hv]].
              right; exists vs; split;
                [apply AtomSet.union_spec; right; exact Ha | exact Hv].
          + intros q n v d H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [left; exact E |].
              right; exists vs; split;
                [apply AtomSet.union_spec; left; exact Ha | exact Hv].
            * destruct (IHb2 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [left; exact E |].
              right; exists vs; split;
                [apply AtomSet.union_spec; right; exact Ha | exact Hv].
          + intros nm i0 n v d H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              exists vs; split;
                [apply AtomSet.union_spec; left; exact Ha | exact Hv].
            * destruct (IHb3 _ _ _ _ _ H) as [vs [Ha Hv]].
              exists vs; split;
                [apply AtomSet.union_spec; right; exact Ha | exact Hv].
          + intros nm i0 n v d H; simpl in H; simpl.
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              exists vs; split;
                [apply AtomSet.union_spec; left; exact Ha | exact Hv].
            * destruct (IHb2 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              exists vs; split;
                [apply AtomSet.union_spec; right; exact Ha | exact Hv].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros q n v d H; exact (IHa2 _ _ _ _ H).
          + intros q n v d H; exact (IHa1 _ _ _ _ H).
          + intros nm i0 n v d H.
            destruct (IHa2 _ _ _ _ H) as [E | Hx]; [discriminate | exact Hx].
          + intros nm i0 n v d H.
            destruct (IHa1 _ _ _ _ H) as [E | Hx]; [discriminate | exact Hx].
        - split4v.
          + intros q n v d H; apply SOed.singleton_in in H; left; congruence.
          + intros q n v d H; apply SOed.singleton_in in H; left; congruence.
          + intros nm i0 n v d H; apply SOed.singleton_in in H; discriminate H.
          + intros nm i0 n v d H; apply SOed.singleton_in in H; discriminate H.
      Qed.

      Lemma occursNegOnb_iff : forall f n v,
          occursNegOnb f n v = true <->
          exists vs, AtomSet.In (ANeg n vs) (negAtoms f) /\ VSet.In v vs.
      Proof.
        intros f n v; unfold occursNegOnb.
        rewrite AtomSet.exists_spec'.
        split.
        - intros [[m ws | m ws | fs | x ys] [Ha Hm]]; simpl in Hm;
            try discriminate.
          apply Bool.andb_true_iff in Hm as [Hn Hv].
          apply NEqb.eqb_true_iff in Hn as ->.
          exists ws; split; [exact Ha | apply VSet.mem_spec; exact Hv].
        - intros [vs [Ha Hv]].
          exists (ANeg n vs); split; [exact Ha |]; simpl.
          rewrite NEqb.eqb_refl; simpl; apply VSet.mem_spec; exact Hv.
      Qed.

      Lemma encodeNNF_src_negDep_aux : forall Y_x f,
          (forall (q : T.Pkg.t) n vs (i : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d) (encodeNNF Y_x q f) ->
              q = (Name.NegDep n vs, i)) /\
          (forall (q : T.Pkg.t) n vs (i : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d) (encodeNNFneg Y_x q f) ->
              q = (Name.NegDep n vs, i)) /\
          (forall (nm : Name.t) (i0 : nat) n vs (i : Version.t)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d)
                (encodeDisj Y_x nm i0 f) ->
              Name.NegDep n vs = nm) /\
          (forall (nm : Name.t) (i0 : nat) n vs (i : Version.t)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d)
                (encodeConjNeg Y_x nm i0 f) ->
              Name.NegDep n vs = nm).
      Proof.
        intros Y_x;
          induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - split4v.
          + intros q n vs i d H; apply SOed.singleton_in in H; congruence.
          + intros q n vs i d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
          + intros nm i0 n vs i d H; apply SOed.singleton_in in H; congruence.
          + intros nm i0 n vs i d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q n vs i d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa1 _ _ _ _ _ H) | exact (IHb1 _ _ _ _ _ H)].
          + intros q n vs i d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ _ H); discriminate
              | assert (E := IHb4 _ _ _ _ _ _ H); discriminate].
          + intros nm i0 n vs i d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ _ H) | assert (E := IHb1 _ _ _ _ _ H)];
              injection E as E1 E2; symmetry; exact E1.
          + intros nm i0 n vs i d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ _ H); injection E as E1 E2;
               symmetry; exact E1
              | exact (IHb4 _ _ _ _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q n vs i d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ _ H); discriminate
              | assert (E := IHb3 _ _ _ _ _ _ H); discriminate].
          + intros q n vs i d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa2 _ _ _ _ _ H) | exact (IHb2 _ _ _ _ _ H)].
          + intros nm i0 n vs i d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ _ H); injection E as E1 E2;
               symmetry; exact E1
              | exact (IHb3 _ _ _ _ _ _ H)].
          + intros nm i0 n vs i d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ _ H) | assert (E := IHb2 _ _ _ _ _ H)];
              injection E as E1 E2; symmetry; exact E1.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros q n vs i d H; exact (IHa2 _ _ _ _ _ H).
          + intros q n vs i d H; exact (IHa1 _ _ _ _ _ H).
          + intros nm i0 n vs i d H.
            assert (E := IHa2 _ _ _ _ _ H); injection E as E1 E2;
              symmetry; exact E1.
          + intros nm i0 n vs i d H.
            assert (E := IHa1 _ _ _ _ _ H); injection E as E1 E2;
              symmetry; exact E1.
        - split4v.
          + intros q n vs i d H; apply SOed.singleton_in in H; congruence.
          + intros q n vs i d H; apply SOed.singleton_in in H; congruence.
          + intros nm i0 n vs i d H; apply SOed.singleton_in in H; congruence.
          + intros nm i0 n vs i d H; apply SOed.singleton_in in H; congruence.
      Qed.

      Lemma encodeNNF_src_var_aux : forall Y_x f,
          (forall (q : T.Pkg.t) x (y : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Var x, y), d) (encodeNNF Y_x q f) ->
              q = (Name.Var x, y)) /\
          (forall (q : T.Pkg.t) x (y : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.Var x, y), d) (encodeNNFneg Y_x q f) ->
              q = (Name.Var x, y)) /\
          (forall (nm : Name.t) (i0 : nat) x (y : Version.t)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Var x, y), d) (encodeDisj Y_x nm i0 f) ->
              Name.Var x = nm) /\
          (forall (nm : Name.t) (i0 : nat) x (y : Version.t)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Var x, y), d) (encodeConjNeg Y_x nm i0 f) ->
              Name.Var x = nm).
      Proof.
        intros Y_x;
          induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa
                         | x0 op y0].
        - split4v.
          + intros q x y d H; apply SOed.singleton_in in H; congruence.
          + intros q x y d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
          + intros nm i0 x y d H; apply SOed.singleton_in in H; congruence.
          + intros nm i0 x y d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q x y d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa1 _ _ _ _ H) | exact (IHb1 _ _ _ _ H)].
          + intros q x y d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ H); discriminate
              | assert (E := IHb4 _ _ _ _ _ H); discriminate].
          + intros nm i0 x y d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ H) | assert (E := IHb1 _ _ _ _ H)];
              injection E as E1 E2; symmetry; exact E1.
          + intros nm i0 x y d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ H); injection E as E1 E2;
               symmetry; exact E1
              | exact (IHb4 _ _ _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros q x y d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ H); discriminate
              | assert (E := IHb3 _ _ _ _ _ H); discriminate].
          + intros q x y d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa2 _ _ _ _ H) | exact (IHb2 _ _ _ _ H)].
          + intros nm i0 x y d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ H); injection E as E1 E2;
               symmetry; exact E1
              | exact (IHb3 _ _ _ _ _ H)].
          + intros nm i0 x y d H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ H) | assert (E := IHb2 _ _ _ _ H)];
              injection E as E1 E2; symmetry; exact E1.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros q x y d H; exact (IHa2 _ _ _ _ H).
          + intros q x y d H; exact (IHa1 _ _ _ _ H).
          + intros nm i0 x y d H.
            assert (E := IHa2 _ _ _ _ H); injection E as E1 E2;
              symmetry; exact E1.
          + intros nm i0 x y d H.
            assert (E := IHa1 _ _ _ _ H); injection E as E1 E2;
              symmetry; exact E1.
        - split4v.
          + intros q x y d H; apply SOed.singleton_in in H; congruence.
          + intros q x y d H; apply SOed.singleton_in in H; congruence.
          + intros nm i0 x y d H; apply SOed.singleton_in in H; congruence.
          + intros nm i0 x y d H; apply SOed.singleton_in in H; congruence.
      Qed.

      (* the witness walkers hand the disjunct package's own name down the
         spine, which is why the spine cases carry the extra alternative. *)
      Definition syntheticAtom (nm : Name.t) : option Atom :=
        match nm with
        | Name.Orig _ => None
        | Name.Var _ => None
        | Name.Disjunct fs => Some (ADisj fs)
        | Name.NegDep n vs => Some (ANeg n vs)
        end.

      Definition IntroducedBy (nm : Name.t) (A : AtomSet.t) : Prop :=
        exists a, syntheticAtom nm = Some a /\ AtomSet.In a A.

      Lemma IntroducedBy_unionL : forall nm A B,
          IntroducedBy nm A -> IntroducedBy nm (AtomSet.union A B).
      Proof.
        intros nm A B [a [Ha HA]]; exists a;
          split; [exact Ha | apply AtomSet.union_spec; left; exact HA].
      Qed.

      Lemma IntroducedBy_unionR : forall nm A B,
          IntroducedBy nm B -> IntroducedBy nm (AtomSet.union A B).
      Proof.
        intros nm A B [a [Ha HB]]; exists a;
          split; [exact Ha | apply AtomSet.union_spec; right; exact HB].
      Qed.

      Lemma IntroducedBy_add : forall nm a A,
          IntroducedBy nm A -> IntroducedBy nm (AtomSet.add a A).
      Proof.
        intros nm a A [b [Hb HA]]; exists b;
          split; [exact Hb | apply AtomSet.add_spec; right; exact HA].
      Qed.

      Lemma witness_atom_aux : forall Y_x (f : Formula),
          (forall (p : T.Pkg.t) (nm : Name.t) (w : Version.t),
              T.PkgSet.In (nm, w) (witnessSet p f) ->
              IntroducedBy nm (deepAtoms Y_x f)) /\
          (forall (p : T.Pkg.t) (nm : Name.t) (w : Version.t),
              T.PkgSet.In (nm, w) (witnessSetNeg p f) ->
              IntroducedBy nm (deepAtomsNeg Y_x f)) /\
          (forall (nm0 : Name.t) (i : nat) (nm : Name.t) (w : Version.t),
              T.PkgSet.In (nm, w) (witnessDisj nm0 i f) ->
              IntroducedBy nm (deepAtoms Y_x f) \/ nm = nm0) /\
          (forall (nm0 : Name.t) (i : nat) (nm : Name.t) (w : Version.t),
              T.PkgSet.In (nm, w) (witnessConjNeg nm0 i f) ->
              IntroducedBy nm (deepAtomsNeg Y_x f) \/ nm = nm0).
      Proof.
        intros Y_x;
          induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - repeat split.
          + intros p nm w H; exfalso; exact (SOpt.empty_in _ H).
          + intros p nm w H; simpl in H |- *.
            rewrite SOpt.add_in, SOpt.singleton_in in H.
            destruct H as [H | H]; injection H as -> _;
              exists (ANeg m ws); split;
              [reflexivity | apply AtomSet.singleton_spec; reflexivity
              | reflexivity | apply AtomSet.singleton_spec; reflexivity].
          + intros nm0 i nm w H; exfalso; exact (SOpt.empty_in _ H).
          + intros nm0 i nm w H; simpl in H |- *.
            rewrite SOpt.add_in, SOpt.singleton_in in H.
            destruct H as [H | H]; injection H as -> _; left;
              exists (ANeg m ws); split;
              [reflexivity | apply AtomSet.singleton_spec; reflexivity
              | reflexivity | apply AtomSet.singleton_spec; reflexivity].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [apply IntroducedBy_unionL; exact (IHa1 _ _ _ H)
              | apply IntroducedBy_unionR; exact (IHb1 _ _ _ H)].
          + intros p nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
            * apply mem_idxPkgs in H; destruct H as [j [_ E]];
                injection E as -> _.
              exists (ADisj (FNeg a :: negConjSpine b)); split;
                [reflexivity | apply AtomSet.add_spec; left; reflexivity].
            * apply T.PkgSet.union_spec in H; destruct H as [H | H].
              -- apply IntroducedBy_add, IntroducedBy_unionL;
                   exact (IHa2 _ _ _ H).
              -- destruct (IHb4 _ _ _ _ H) as [HM | ->];
                   [apply IntroducedBy_add, IntroducedBy_unionR; exact HM |].
                 exists (ADisj (FNeg a :: negConjSpine b)); split;
                   [reflexivity | apply AtomSet.add_spec; left; reflexivity].
          + intros nm0 i nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [left; apply IntroducedBy_unionL; exact (IHa1 _ _ _ H)
              | left; apply IntroducedBy_unionR; exact (IHb1 _ _ _ H)].
          + intros nm0 i nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
            * left; apply IntroducedBy_add, IntroducedBy_unionL;
                exact (IHa2 _ _ _ H).
            * destruct (IHb4 _ _ _ _ H) as [HM | E];
                [left; apply IntroducedBy_add, IntroducedBy_unionR; exact HM
                | right; exact E].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
            * apply mem_idxPkgs in H; destruct H as [j [_ E]];
                injection E as -> _.
              exists (ADisj (a :: disjSpine b)); split;
                [reflexivity | apply AtomSet.add_spec; left; reflexivity].
            * apply T.PkgSet.union_spec in H; destruct H as [H | H].
              -- apply IntroducedBy_add, IntroducedBy_unionL;
                   exact (IHa1 _ _ _ H).
              -- destruct (IHb3 _ _ _ _ H) as [HM | ->];
                   [apply IntroducedBy_add, IntroducedBy_unionR; exact HM |].
                 exists (ADisj (a :: disjSpine b)); split;
                   [reflexivity | apply AtomSet.add_spec; left; reflexivity].
          + intros p nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [apply IntroducedBy_unionL; exact (IHa2 _ _ _ H)
              | apply IntroducedBy_unionR; exact (IHb2 _ _ _ H)].
          + intros nm0 i nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
            * left; apply IntroducedBy_add, IntroducedBy_unionL;
                exact (IHa1 _ _ _ H).
            * destruct (IHb3 _ _ _ _ H) as [HM | E];
                [left; apply IntroducedBy_add, IntroducedBy_unionR; exact HM
                | right; exact E].
          + intros nm0 i nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [left; apply IntroducedBy_unionL; exact (IHa2 _ _ _ H)
              | left; apply IntroducedBy_unionR; exact (IHb2 _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
          + intros p nm w H; exact (IHa2 _ _ _ H).
          + intros p nm w H; exact (IHa1 _ _ _ H).
          + intros nm0 i nm w H; left; exact (IHa2 _ _ _ H).
          + intros nm0 i nm w H; left; exact (IHa1 _ _ _ H).
        - repeat split.
          + intros p nm w H; exfalso; exact (SOpt.empty_in _ H).
          + intros p nm w H; exfalso; exact (SOpt.empty_in _ H).
          + intros nm0 i nm w H; exfalso; exact (SOpt.empty_in _ H).
          + intros nm0 i nm w H; exfalso; exact (SOpt.empty_in _ H).
      Qed.

      Definition withNeg (Y_x : X.t -> YSet.t) (D : DepRel.t)
          (n : N.t) (vs : VSet.t) : DepRel.t :=
        DepRel.filter (fun '(_, f) =>
            AtomSet.mem (ANeg n vs) (deepAtoms Y_x f)) D.

      Lemma mem_withNeg : forall Y_x D n vs (p : Pkg.t) (f : Formula),
          DepRel.In (p, f) (withNeg Y_x D n vs) <->
          DepRel.In (p, f) D /\ AtomSet.In (ANeg n vs) (deepAtoms Y_x f).
      Proof.
        intros Y_x D n vs p f; unfold withNeg.
        rewrite DepRel.filter_spec'.
        cbn beta iota; rewrite AtomSet.mem_spec; reflexivity.
      Qed.

      (* the variable domain arrives as a function, so the fibre that keeps
         one variable's values has to be written out rather than filtered. *)
      Definition varFibre (Y_x : X.t -> YSet.t) (x : X.t) : X.t -> YSet.t :=
        fun x' => if X.eq_dec x' x then Y_x x' else YSet.empty.

      Definition syntheticPkgs (nm : Name.t) : T.PkgSet.t :=
        match nm with
        | Name.Orig _ => T.PkgSet.empty
        | Name.Var _ => T.PkgSet.empty
        | Name.Disjunct fs => idxPkgs (Name.Disjunct fs) (List.length fs)
        | Name.NegDep n vs =>
            T.PkgSet.add (Name.NegDep n vs, Version.Idx 0)
              (T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 1))
        end.

      Lemma witnessSet_synthetic_aux : forall f : Formula,
          (forall (p q : T.Pkg.t),
              T.PkgSet.In q (witnessSet p f) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (p q : T.Pkg.t),
              T.PkgSet.In q (witnessSetNeg p f) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (nm : Name.t) (i : nat) (q : T.Pkg.t),
              T.PkgSet.In q (witnessDisj nm i f) ->
              T.PkgSet.In q (syntheticPkgs (fst q))) /\
          (forall (nm : Name.t) (i : nat) (q : T.Pkg.t),
              T.PkgSet.In q (witnessConjNeg nm i f) ->
              T.PkgSet.In q (syntheticPkgs (fst q))).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - repeat split.
          + intros p q H; simpl in H; exfalso; exact (SOpt.empty_in _ H).
          + intros p q H; simpl in H;
              rewrite SOpt.add_in, SOpt.singleton_in in H;
              destruct H as [-> | ->]; cbn [fst syntheticPkgs];
              rewrite SOpt.add_in, SOpt.singleton_in;
              [left | right]; reflexivity.
          + intros nm i q H; simpl in H; exfalso; exact (SOpt.empty_in _ H).
          + intros nm i q H; simpl in H;
              rewrite SOpt.add_in, SOpt.singleton_in in H;
              destruct H as [-> | ->]; cbn [fst syntheticPkgs];
              rewrite SOpt.add_in, SOpt.singleton_in;
              [left | right]; reflexivity.
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
          + intros nm i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
          + intros nm i q H; simpl in H; apply T.PkgSet.union_spec in H;
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
          + intros nm i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H];
              [exact (IHa1 _ _ H) | exact (IHb3 _ _ _ H)].
          + intros nm i q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
          + intros p q H; simpl in H; exact (IHa2 _ _ H).
          + intros p q H; simpl in H; exact (IHa1 _ _ H).
          + intros nm i q H; simpl in H; exact (IHa2 _ _ H).
          + intros nm i q H; simpl in H; exact (IHa1 _ _ H).
        - repeat split.
          + intros p q H; simpl in H; exfalso; exact (SOpt.empty_in _ H).
          + intros p q H; simpl in H; exfalso; exact (SOpt.empty_in _ H).
          + intros nm i q H; simpl in H; exfalso; exact (SOpt.empty_in _ H).
          + intros nm i q H; simpl in H; exfalso; exact (SOpt.empty_in _ H).
      Qed.

      Lemma encodeNNF_target_synthetic_aux : forall f : Formula,
          (forall Y_x (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNF Y_x p f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d))) (witnessSet p f)) /\
          (forall Y_x (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNFneg Y_x p f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessSetNeg p f)) /\
          (forall Y_x (nm : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeDisj Y_x nm i f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessDisj nm i f)) /\
          (forall Y_x (nm : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeConjNeg Y_x nm i f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessConjNeg nm i f)).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - repeat split.
          + intros Y_x p d H; simpl in H; apply SOed.singleton_in in H; subst d;
              cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
          + intros Y_x p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H];
              [| apply SOvd.mem_map in H; destruct H as [u [_ ->]]];
              intros z Hz; exact Hz.
          + intros Y_x nm i d H; simpl in H; apply SOed.singleton_in in H;
              subst d; cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
          + intros Y_x nm i d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H];
              [| apply SOvd.mem_map in H; destruct H as [u [_ ->]]];
              intros z Hz; exact Hz.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros Y_x p d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ _ d H z Hz)
              | right; exact (IHb1 _ _ d H z Hz)].
          + intros Y_x p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H].
            * intros z Hz; cbn [fst snd syntheticPkgs] in Hz;
                apply T.PkgSet.union_spec; left; exact Hz.
            * apply T.DepRel.union_spec in H; intros z Hz;
                apply T.PkgSet.union_spec; right;
                apply T.PkgSet.union_spec; destruct H as [H | H];
                [left; exact (IHa2 _ _ d H z Hz)
                | right; exact (IHb4 _ _ _ d H z Hz)].
          + intros Y_x nm i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ _ d H z Hz)
              | right; exact (IHb1 _ _ d H z Hz)].
          + intros Y_x nm i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ _ d H z Hz)
              | right; exact (IHb4 _ _ _ d H z Hz)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros Y_x p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H].
            * intros z Hz; cbn [fst snd syntheticPkgs] in Hz;
                apply T.PkgSet.union_spec; left; exact Hz.
            * apply T.DepRel.union_spec in H; intros z Hz;
                apply T.PkgSet.union_spec; right;
                apply T.PkgSet.union_spec; destruct H as [H | H];
                [left; exact (IHa1 _ _ d H z Hz)
                | right; exact (IHb3 _ _ _ d H z Hz)].
          + intros Y_x p d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ _ d H z Hz)
              | right; exact (IHb2 _ _ d H z Hz)].
          + intros Y_x nm i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ _ d H z Hz)
              | right; exact (IHb3 _ _ _ d H z Hz)].
          + intros Y_x nm i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ _ d H z Hz)
              | right; exact (IHb2 _ _ d H z Hz)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
          + intros Y_x p d H; simpl in H; exact (IHa2 _ _ d H).
          + intros Y_x p d H; simpl in H; exact (IHa1 _ _ d H).
          + intros Y_x nm i d H; simpl in H; exact (IHa2 _ _ d H).
          + intros Y_x nm i d H; simpl in H; exact (IHa1 _ _ d H).
        - repeat split.
          + intros Y_x p d H; simpl in H; apply SOed.singleton_in in H; subst d;
              cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
          + intros Y_x p d H; simpl in H; apply SOed.singleton_in in H; subst d;
              cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
          + intros Y_x nm i d H; simpl in H; apply SOed.singleton_in in H;
              subst d; cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
          + intros Y_x nm i d H; simpl in H; apply SOed.singleton_in in H;
              subst d; cbn [fst snd syntheticPkgs]; apply T.PkgSet.empty_subset.
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Theorem versions_lookupOrig : forall Y_x R D (r : Pkg.t) (n : N.t),
          (exists p h,
              T.DepRel.In (p, (Name.Orig n, h)) (reduceDeps Y_x D)) \/
          Name.Orig n = Name.Orig (fst r) ->
          T.versions (reduceReal Y_x R D) (Name.Orig n) =
          T.versions
            (reduceReal (fun _ => YSet.empty) (PkgFibred.tailFibre R n)
               DepRel.empty)
            (Name.Orig n).
      Proof.
        intros Y_x R D r n _; apply T.versions_ext; intro y.
        rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [HR Hq]] | [[p [f [_ Hw]]] | [x [y' [_ Hq]]]]].
          + unfold embedPkg in Hq; injection Hq as -> ->.
            left; exists (qn, qv).
            split; [apply PkgFibred.mem_tailFibre;
                    split; [exact HR | reflexivity]
                   | reflexivity].
          + exfalso; exact (witnessSet_not_orig _ _ _ _ Hw).
          + discriminate Hq.
        - intros [[[qn qv] [HR Hq]] | [[p [f [Hd _]]] | [x [y' [Hy _]]]]].
          + apply PkgFibred.mem_tailFibre in HR; destruct HR as [HR _].
            left; exists (qn, qv); split; [exact HR | exact Hq].
          + destruct (DepRel.empty_spec Hd).
          + destruct (YSet.empty_spec Hy).
      Qed.

      Theorem dependees_lookupOrig : forall Y_x R D n v,
          T.PkgSet.In (Name.Orig n, Version.Orig v) (reduceReal Y_x R D) ->
          T.dependees (reduceDeps Y_x D) (Name.Orig n, Version.Orig v) =
          T.dependees (reduceDeps Y_x (subInstanceOrig D (n, v)))
            (Name.Orig n, Version.Orig v).
      Proof.
        intros Y_x R D n v _; apply T.dependees_ext; intro h.
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

      Theorem versions_lookupVar : forall Y_x R D (x : X.t),
          (exists p h,
              T.DepRel.In (p, (Name.Var x, h)) (reduceDeps Y_x D)) ->
          T.versions (reduceReal Y_x R D) (Name.Var x) =
          T.versions (reduceReal (varFibre Y_x x) PkgSet.empty DepRel.empty)
            (Name.Var x).
      Proof.
        intros Y_x R D x _; apply T.versions_ext; intro w.
        rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [[p [f [_ Hw]]] | [x' [y [Hy Hq]]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + exfalso; exact (witnessSet_not_var _ _ _ _ Hw).
          + injection Hq as -> ->.
            right; right; exists x', y; split; [| reflexivity].
            unfold varFibre; destruct (X.eq_dec x' x') as [_ | NE];
              [exact Hy | contradiction NE; reflexivity].
        - intros [[p [Hp _]] | [[p [f [Hd _]]] | [x' [y [Hy Hq]]]]].
          + destruct (PkgSet.empty_spec Hp).
          + destruct (DepRel.empty_spec Hd).
          + right; right; exists x', y; split; [| exact Hq].
            unfold varFibre in Hy; destruct (X.eq_dec x' x) as [_ | NE];
              [exact Hy | destruct (YSet.empty_spec Hy)].
      Qed.

      Theorem dependees_lookupVar : forall Y_x R D x (y : Version.t),
          T.PkgSet.In (Name.Var x, y) (reduceReal Y_x R D) ->
          T.dependees (reduceDeps Y_x D) (Name.Var x, y) = T.DependeesSet.empty.
      Proof.
        intros Y_x R D x y _; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [f [_ He]]]; unfold encodeNNF in He.
        assert (E := proj1 (encodeNNF_src_var_aux Y_x f) _ _ _ _ He).
        unfold embedPkg in E; simpl in E; discriminate.
      Qed.

      Theorem versions_lookupDisjunct : forall Y_x R D (fs : list Formula),
          (exists p h, T.DepRel.In (p, (Name.Disjunct fs, h))
                         (reduceDeps Y_x D)) ->
          T.versions (reduceReal Y_x R D) (Name.Disjunct fs) =
          idxSet (List.length fs).
      Proof.
        intros Y_x R D fs [p [h Hd]].
        apply mem_reduceDeps in Hd; destruct Hd as [r [g [HD He]]].
        pose proof (proj1 (encodeNNF_target_synthetic_aux g) Y_x (embedPkg r)
                      (p, (Name.Disjunct fs, h)) He) as Hsub.
        cbn [fst snd] in Hsub.
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_idxSet, mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [[r1 [g1 [_ Hw]]] | [x1 [y1 [_ Hq]]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + pose proof (proj1 (witnessSet_synthetic_aux g1) _ _ Hw) as Hg.
            cbn [fst syntheticPkgs] in Hg; apply mem_idxPkgs in Hg.
            destruct Hg as [i [Hi Hq]]; exists i;
              split; [exact Hi | congruence].
          + discriminate Hq.
        - intros [i [Hi ->]]; right; left; exists r, g; split; [exact HD |].
          apply Hsub; cbn [syntheticPkgs]; apply mem_idxPkgs;
            exists i; split; [exact Hi | reflexivity].
      Qed.

      Lemma encodeDisj_alt : forall (f : Formula) (Y_x : X.t -> YSet.t)
                                    (nm : Name.t) (i0 j : nat)
                                    (g : Formula) (d : T.Dependees.t),
          List.nth_error (disjSpine f) j = Some g ->
          T.DepRel.In ((nm, Version.Idx (i0 + j)), d)
            (encodeNNF Y_x (nm, Version.Idx (i0 + j)) g) ->
          T.DepRel.In ((nm, Version.Idx (i0 + j)), d) (encodeDisj Y_x nm i0 f).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          intros Y_x nm i0 j g d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb Y_x nm (S i0) j g d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma encodeConjNeg_alt : forall (f : Formula) (Y_x : X.t -> YSet.t)
                                       (nm : Name.t) (i0 j : nat)
                                       (g : Formula) (d : T.Dependees.t),
          List.nth_error (negConjSpine f) j = Some g ->
          T.DepRel.In ((nm, Version.Idx (i0 + j)), d)
            (encodeNNF Y_x (nm, Version.Idx (i0 + j)) g) ->
          T.DepRel.In ((nm, Version.Idx (i0 + j)), d)
            (encodeConjNeg Y_x nm i0 f).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y];
          intros Y_x nm i0 j g d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb Y_x nm (S i0) j g d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma witnessSet_alt_aux : forall f : Formula,
          (forall (Y_x : X.t -> YSet.t) (p : T.Pkg.t) (gs : list Formula)
                  (k : nat) (g : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k) (witnessSet p f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x p f)) /\
          (forall (Y_x : X.t -> YSet.t) (p : T.Pkg.t) (gs : list Formula)
                  (k : nat) (g : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessSetNeg p f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNFneg Y_x p f)) /\
          (forall (Y_x : X.t -> YSet.t) (nm : Name.t) (i0 : nat)
                  (gs : list Formula) (k : nat) (g : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessDisj nm i0 f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeDisj Y_x nm i0 f)) /\
          (forall (Y_x : X.t -> YSet.t) (nm : Name.t) (i0 : nat)
                  (gs : list Formula) (k : nat) (g : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessConjNeg nm i0 f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeConjNeg Y_x nm i0 f)).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - split4v.
          + intros Y_x p gs k g d H Hg Hd; simpl in H;
              exfalso; exact (SOpt.empty_in _ H).
          + intros Y_x p gs k g d H Hg Hd; simpl in H;
              rewrite SOpt.add_in, SOpt.singleton_in in H;
              destruct H as [H | H]; congruence.
          + intros Y_x nm i0 gs k g d H Hg Hd; simpl in H;
              exfalso; exact (SOpt.empty_in _ H).
          + intros Y_x nm i0 gs k g d H Hg Hd; simpl in H;
              rewrite SOpt.add_in, SOpt.singleton_in in H;
              destruct H as [H | H]; congruence.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros Y_x p gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ _ H Hg Hd)
              | right; exact (IHb1 _ _ _ _ _ _ H Hg Hd)].
          + intros Y_x p gs k g d H Hg Hd; simpl in H; simpl.
            apply T.PkgSet.union_spec in H; apply SOed.add_in;
              destruct H as [H | H]; [| right; apply T.DepRel.union_spec].
            * apply mem_idxPkgs in H; destruct H as [i [_ H]];
                injection H as H1 H2; subst gs; subst k; right;
                apply T.DepRel.union_spec; destruct i as [| i];
                simpl in Hg; [left | right].
              -- injection Hg as <-; exact Hd.
              -- exact (encodeConjNeg_alt b Y_x
                          (Name.Disjunct (FNeg a :: negConjSpine b))
                          1 i g d Hg Hd).
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [left; exact (IHa2 _ _ _ _ _ _ H Hg Hd)
                | right; exact (IHb4 _ _ _ _ _ _ _ H Hg Hd)].
          + intros Y_x nm i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ _ H Hg Hd)
              | right; exact (IHb1 _ _ _ _ _ _ H Hg Hd)].
          + intros Y_x nm i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ _ H Hg Hd)
              | right; exact (IHb4 _ _ _ _ _ _ _ H Hg Hd)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros Y_x p gs k g d H Hg Hd; simpl in H; simpl.
            apply T.PkgSet.union_spec in H; apply SOed.add_in;
              destruct H as [H | H]; [| right; apply T.DepRel.union_spec].
            * apply mem_idxPkgs in H; destruct H as [i [_ H]];
                injection H as H1 H2; subst gs; subst k; right;
                apply T.DepRel.union_spec; destruct i as [| i];
                simpl in Hg; [left | right].
              -- injection Hg as <-; exact Hd.
              -- exact (encodeDisj_alt b Y_x
                          (Name.Disjunct (a :: disjSpine b)) 1 i g d Hg Hd).
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [left; exact (IHa1 _ _ _ _ _ _ H Hg Hd)
                | right; exact (IHb3 _ _ _ _ _ _ _ H Hg Hd)].
          + intros Y_x p gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ _ H Hg Hd)
              | right; exact (IHb2 _ _ _ _ _ _ H Hg Hd)].
          + intros Y_x nm i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ _ H Hg Hd)
              | right; exact (IHb3 _ _ _ _ _ _ _ H Hg Hd)].
          + intros Y_x nm i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ _ H Hg Hd)
              | right; exact (IHb2 _ _ _ _ _ _ H Hg Hd)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros Y_x p gs k g d H Hg Hd; exact (IHa2 _ _ _ _ _ _ H Hg Hd).
          + intros Y_x p gs k g d H Hg Hd; exact (IHa1 _ _ _ _ _ _ H Hg Hd).
          + intros Y_x nm i0 gs k g d H Hg Hd;
              exact (IHa2 _ _ _ _ _ _ H Hg Hd).
          + intros Y_x nm i0 gs k g d H Hg Hd;
              exact (IHa1 _ _ _ _ _ _ H Hg Hd).
        - split4v.
          + intros Y_x p gs k g d H Hg Hd; simpl in H;
              exfalso; exact (SOpt.empty_in _ H).
          + intros Y_x p gs k g d H Hg Hd; simpl in H;
              exfalso; exact (SOpt.empty_in _ H).
          + intros Y_x nm i0 gs k g d H Hg Hd; simpl in H;
              exfalso; exact (SOpt.empty_in _ H).
          + intros Y_x nm i0 gs k g d H Hg Hd; simpl in H;
              exfalso; exact (SOpt.empty_in _ H).
      Qed.

      Lemma encodeNNF_alt_aux : forall f : Formula,
          (forall (Y_x : X.t -> YSet.t) (q : T.Pkg.t) (gs : list Formula)
                  (k : nat) (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Y_x q f) ->
              q = (Name.Disjunct gs, Version.Idx k) \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Y_x
                              (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (Y_x : X.t -> YSet.t) (q : T.Pkg.t) (gs : list Formula)
                  (k : nat) (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNFneg Y_x q f) ->
              q = (Name.Disjunct gs, Version.Idx k) \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Y_x
                              (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (Y_x : X.t -> YSet.t) (nm : Name.t) (i0 : nat)
                  (gs : list Formula) (k : nat) (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeDisj Y_x nm i0 f) ->
              (nm = Name.Disjunct gs /\
               exists j g, k = i0 + j /\
                           List.nth_error (disjSpine f) j = Some g /\
                           T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                             (encodeNNF Y_x
                                (Name.Disjunct gs, Version.Idx k) g))
              \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Y_x
                              (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (Y_x : X.t -> YSet.t) (nm : Name.t) (i0 : nat)
                  (gs : list Formula) (k : nat) (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeConjNeg Y_x nm i0 f) ->
              (nm = Name.Disjunct gs /\
               exists j g, k = i0 + j /\
                           List.nth_error (negConjSpine f) j = Some g /\
                           T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                             (encodeNNF Y_x
                                (Name.Disjunct gs, Version.Idx k) g))
              \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Y_x
                              (Name.Disjunct gs, Version.Idx k) g))).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa | x op y].
        - split4v.
          + intros Y_x q gs k d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros Y_x q gs k d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H]; [left; congruence |].
            apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
          + intros Y_x nm i0 gs k d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FDep m ws); subst k;
              split; [lia | split; [reflexivity |]].
            apply SOed.singleton_in; subst d; reflexivity.
          + intros Y_x nm i0 gs k d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H];
              [| apply SOvd.mem_map in H; destruct H as [u [_ H]];
                 discriminate].
            injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FNeg (FDep m ws)); subst k;
              split; [lia | split; [reflexivity |]].
            simpl; apply SOed.add_in; left; subst d; reflexivity.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros Y_x q gs k d H; simpl in H;
              apply T.DepRel.union_spec in H;
              destruct H as [H | H];
              [exact (IHa1 _ _ _ _ _ H) | exact (IHb1 _ _ _ _ _ H)].
          + intros Y_x q gs k d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; right; exists (FNeg a);
                subst gs; subst k; split; [reflexivity | exact H].
            * destruct (IHb4 _ _ _ _ _ _ H)
                as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex]; [| right; exact Hex].
              injection Eq as Eq; right; exists g; subst gs; subst k;
                split; [| exact Hin].
              simpl; exact Hg.
          + intros Y_x nm i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FConj a b); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; left; exact H.
            * destruct (IHb1 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FConj a b); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; right; exact H.
          + intros Y_x nm i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FNeg a); subst k;
                split; [lia | split; [reflexivity |]].
              exact H.
            * destruct (IHb4 _ _ _ _ _ _ H)
                as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex]; [| right; exact Hex].
              left; split; [exact Eq |]; exists (S j), g;
                split; [lia | split; [exact Hg | exact Hin]].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4v.
          + intros Y_x q gs k d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; right; exists a;
                subst gs; subst k; split; [reflexivity | exact H].
            * destruct (IHb3 _ _ _ _ _ _ H)
                as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex]; [| right; exact Hex].
              injection Eq as Eq; right; exists g; subst gs; subst k;
                split; [| exact Hin].
              simpl; exact Hg.
          + intros Y_x q gs k d H; simpl in H;
              apply T.DepRel.union_spec in H;
              destruct H as [H | H];
              [exact (IHa2 _ _ _ _ _ H) | exact (IHb2 _ _ _ _ _ H)].
          + intros Y_x nm i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, a; subst k; split; [lia | split; [reflexivity |]].
              exact H.
            * destruct (IHb3 _ _ _ _ _ _ H)
                as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex]; [| right; exact Hex].
              left; split; [exact Eq |]; exists (S j), g;
                split; [lia | split; [exact Hg | exact Hin]].
          + intros Y_x nm i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FNeg (FDisj a b)); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; left; exact H.
            * destruct (IHb2 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FNeg (FDisj a b)); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; right; exact H.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4v.
          + intros Y_x q gs k d H; exact (IHa2 _ _ _ _ _ H).
          + intros Y_x q gs k d H; exact (IHa1 _ _ _ _ _ H).
          + intros Y_x nm i0 gs k d H; simpl in H.
            destruct (IHa2 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
            injection Eq as Eq1 Eq2; subst nm; left;
              split; [reflexivity |].
            exists 0, (FNeg a); subst k;
              split; [lia | split; [reflexivity |]].
            exact H.
          + intros Y_x nm i0 gs k d H; simpl in H.
            destruct (IHa1 _ _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
            injection Eq as Eq1 Eq2; subst nm; left;
              split; [reflexivity |].
            exists 0, (FNeg (FNeg a)); subst k;
              split; [lia | split; [reflexivity |]].
            exact H.
        - split4v.
          + intros Y_x q gs k d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros Y_x q gs k d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros Y_x nm i0 gs k d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FVarCmp x op y); subst k;
              split; [lia | split; [reflexivity |]].
            apply SOed.singleton_in; subst d; reflexivity.
          + intros Y_x nm i0 gs k d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FNeg (FVarCmp x op y)); subst k;
              split; [lia | split; [reflexivity |]].
            simpl; apply SOed.singleton_in; subst d; reflexivity.
      Qed.

      Theorem dependees_lookupDisjunct : forall Y_x R D fs (i : Version.t),
          T.PkgSet.In (Name.Disjunct fs, i) (reduceReal Y_x R D) ->
          T.dependees (reduceDeps Y_x D) (Name.Disjunct fs, i) =
          match disjAlt fs i with
          | Some g =>
              T.dependees (encodeNNF Y_x (Name.Disjunct fs, i) g)
                (Name.Disjunct fs, i)
          | None => T.DependeesSet.empty
          end.
      Proof.
        intros Y_x R D fs i H; apply mem_reduceReal in H.
        destruct H as [[[pn pv] [_ Hq]] | [[p [f [HD Hw]]] | [x [y [_ Hq]]]]];
          [unfold embedPkg in Hq; discriminate Hq | | discriminate Hq].
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
          destruct (proj1 (encodeNNF_alt_aux f') _ _ _ _ _ He)
            as [Eq | [g' [Hg' Hin]]].
          + destruct q as [qn qv]; unfold embedPkg in Eq; simpl in Eq;
              discriminate.
          + rewrite E in Hg'; injection Hg' as <-; exact Hin.
        - intro Hin; exists p, f; split; [exact HD |].
          exact (proj1 (witnessSet_alt_aux f) _ _ _ _ _ _ Hw E Hin).
      Qed.

      Theorem versions_lookupNegDep : forall Y_x R D (n : N.t) (vs : VSet.t),
          (exists p h, T.DepRel.In (p, (Name.NegDep n vs, h))
                         (reduceDeps Y_x D)) ->
          T.versions (reduceReal Y_x R D) (Name.NegDep n vs) =
          T.VSet.add (Version.Idx 0) (T.VSet.singleton (Version.Idx 1)).
      Proof.
        intros Y_x R D n vs [p [h Hd]].
        apply mem_reduceDeps in Hd; destruct Hd as [r [g [HD He]]].
        pose proof (proj1 (encodeNNF_target_synthetic_aux g) Y_x (embedPkg r)
                      (p, (Name.NegDep n vs, h)) He) as Hsub.
        cbn [fst snd] in Hsub.
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal, SOvv.add_in,
          SOvv.singleton_in.
        split.
        - intros [[[qn qv] [_ Hq]] | [[r1 [g1 [_ Hw]]] | [x1 [y1 [_ Hq]]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + pose proof (proj1 (witnessSet_synthetic_aux g1) _ _ Hw) as Hg.
            cbn [fst syntheticPkgs] in Hg;
              rewrite SOpt.add_in, SOpt.singleton_in in Hg.
            destruct Hg as [Hg | Hg]; [left | right]; congruence.
          + discriminate Hq.
        - intro Hw; right; left; exists r, g; split; [exact HD |].
          apply Hsub; cbn [syntheticPkgs];
            rewrite SOpt.add_in, SOpt.singleton_in.
          destruct Hw as [-> | ->]; [left | right]; reflexivity.
      Qed.

      Theorem dependees_lookupNegDep : forall Y_x R D n vs (i : Version.t),
          T.PkgSet.In (Name.NegDep n vs, i) (reduceReal Y_x R D) ->
          T.dependees (reduceDeps Y_x D) (Name.NegDep n vs, i) =
          T.DependeesSet.empty.
      Proof.
        intros Y_x R D n vs i _; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [f [_ He]]]; unfold encodeNNF in He.
        assert (E := proj1 (encodeNNF_src_negDep_aux Y_x f) _ _ _ _ _ He).
        unfold embedPkg in E; simpl in E; discriminate.
      Qed.

    End Lookup.
  End Reduction.
End VariableFormula.
