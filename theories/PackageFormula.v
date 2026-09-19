From Stdlib Require Import MSets List Lia.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_pkgf.
Create Rewrite HintDb cmp_pkgf.

(* Each spine-fused fixpoint family is four functions, so its lemmas are
   four-way conjunctions; repeat split would run past the conjunction and
   into the products and conjunctions of the conjuncts themselves. *)
Ltac split4 := split; [| split; [| split]].

Module PackageFormula (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive Formula : Type :=
  | FDep (n : N.t) (vs : VSet.t)
  | FConj (f1 f2 : Formula)
  | FDisj (f1 f2 : Formula)
  | FNeg (f : Formula).

  Fixpoint Satisfies (S : PkgSet.t) (f : Formula) : Prop :=
    match f with
    | FDep n vs => exists v, VSet.In v vs /\ PkgSet.In (n, v) S
    | FConj f1 f2 => Satisfies S f1 /\ Satisfies S f2
    | FDisj f1 f2 => Satisfies S f1 \/ Satisfies S f2
    | FNeg f1 => ~ Satisfies S f1
    end.

  Fixpoint satisfiesb (S : PkgSet.t) (f : Formula) : bool :=
    match f with
    | FDep n vs => VSet.exists_ (fun v => PkgSet.mem (n, v) S) vs
    | FConj f1 f2 => andb (satisfiesb S f1) (satisfiesb S f2)
    | FDisj f1 f2 => orb (satisfiesb S f1) (satisfiesb S f2)
    | FNeg f1 => negb (satisfiesb S f1)
    end.

  Lemma satisfiesb_iff : forall S f, satisfiesb S f = true <-> Satisfies S f.
  Proof.
    intros S f; induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
      simpl.
    - rewrite VSet.exists_spec'.
      split; intros [v [Hv Hm]]; exists v; split; try assumption;
        apply PkgSet.mem_spec; assumption.
    - rewrite Bool.andb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.orb_true_iff, IHa, IHb; reflexivity.
    - rewrite Bool.negb_true_iff; split.
      + intros E Hs; apply IHa in Hs; congruence.
      + intro Hn; destruct (satisfiesb S a) eqn:E; [| reflexivity].
        exfalso; apply Hn, IHa; reflexivity.
  Qed.

  Lemma satisfiesb_false_iff : forall S f,
      satisfiesb S f = false <-> ~ Satisfies S f.
  Proof.
    intros S f; split.
    - intros E Hs; apply satisfiesb_iff in Hs; congruence.
    - intro Hn; destruct (satisfiesb S f) eqn:E; [| reflexivity].
      exfalso; apply Hn, satisfiesb_iff; exact E.
  Qed.

  Lemma satisfies_double_neg : forall S f, ~ ~ Satisfies S f -> Satisfies S f.
  Proof.
    intros S f Hnn; destruct (satisfiesb S f) eqn:E.
    - apply satisfiesb_iff; exact E.
    - exfalso; apply Hnn, satisfiesb_false_iff; exact E.
  Qed.

  Module NF := UOTCompareFacts N.
  Module VSF := UOTCompareFacts VSet.AsUOT.
  #[local] Hint Rewrite NF.compare_eq_iff : cmp_pkgf.
  #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_pkgf.
  #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_pkgf.

  Module FComp <: ComparableType.
    Definition t := Formula.
    Definition rank (f : Formula) : nat :=
      match f with
      | FDep _ _ => 0 | FConj _ _ => 1 | FDisj _ _ => 2 | FNeg _ => 3
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
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof.
      intros x; induction x as [n1 vs1 | a IHa b IHb | a IHa b IHb | a IHa];
        intros y; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2]; simpl;
        try (split; intro H; congruence).
      - rewrite lex_eq_iff, NF.compare_eq_iff, VSF.compare_eq_iff;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite lex_eq_iff, IHa, IHb;
          split; intro H; [destruct H; congruence | injection H as -> ->; auto].
      - rewrite IHa; split; intro H; congruence.
    Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof.
      intros x; induction x as [n1 vs1 | a IHa b IHb | a IHa b IHb | a IHa];
        intros y; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2]; simpl;
        try reflexivity.
      - rewrite lex_opp, NF.compare_antisym, VSF.compare_antisym; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - rewrite lex_opp, IHa, IHb; reflexivity.
      - apply IHa.
    Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof.
      intros x;
        induction x as [n1 vs1 | a1 IHa b1 IHb | a1 IHa b1 IHb | a1 IHa];
        intros y z; destruct y as [n2 vs2 | a2 b2 | a2 b2 | a2],
          z as [n3 vs3 | a3 b3 | a3 b3 | a3]; simpl; intros H1 H2;
        try congruence.
      - exact (lex_lt_trans NF.compare_eq_iff (NF.compare_lt_trans _ _ _)
                 (VSF.compare_lt_trans _ _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (lex_lt_trans compare_eq_iff (IHa _ _) (IHb _ _) H1 H2).
      - exact (IHa _ _ H1 H2).
    Qed.
  End FComp.
  Module FOT := UOTFromCompare FComp.

  Module Dependees := FOT.
  Module DepElt := PairUOT Pkg Dependees.
  Module DepRel := FSetUOT DepElt.

  Record IsResolution
      (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_formula_closure :
        forall p, PkgSet.In p S ->
        forall f : Formula, DepRel.In (p, f) D -> Satisfies S f
    ; res_version_unique : C.VersionUnique S }.

  Module Reduction.
    Module DepF := UOTCompareFacts C.Dependees.
    Module FList := ListComp FComp.
    Module FListOT := UOTFromCompare FList.
    Module FListF := UOTCompareFacts FListOT.
    #[local] Hint Rewrite DepF.compare_eq_iff FListF.compare_eq_iff : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by FListF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by DepF.compare_lt_trans : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by FListF.compare_lt_trans : cmp_pkgf.

    (* One gadget per disjunction, named by all of its alternatives: a
       chain of two-alternative gadgets would mint an inner name for every
       proper suffix of the same disjunction. *)
    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Disjunct (fs : list Formula)
      | NegDep (n : N.t) (vs : VSet.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, _ => Lt
        | Disjunct _, Orig _ => Gt
        | Disjunct fs1, Disjunct fs2 => FListOT.compare fs1 fs2
        | Disjunct _, NegDep _ _ => Lt
        | NegDep n1 vs1, NegDep n2 vs2 =>
            C.Dependees.compare (n1, vs1) (n2, vs2)
        | NegDep _ _, _ => Gt
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_pkgf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_pkgf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_pkgf. Qed.
    End Name.

    Module VF := UOTCompareFacts V.
    Module NatF := UOTCompareFacts Nat_as_OT.
    #[local] Hint Rewrite VF.compare_eq_iff NatF.compare_eq_iff : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by NatF.compare_antisym : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_pkgf.
    #[local] Hint Extern 1 => cmp_by NatF.compare_lt_trans : cmp_pkgf.

    (* A gadget version is the position of the alternative it selects, so a
       disjunction of any width is one node. *)
    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Idx (i : nat).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, _ => Lt
        | Idx _, Orig _ => Gt
        | Idx i, Idx j => Nat.compare i j
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_pkgf. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_pkgf. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_pkgf. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module T := Core NameOT VersionOT.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(n, v) := p in (Name.Orig n, Version.Orig v).

    Module SOvv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map Version.Orig vs.

    (* The alternatives a disjunction offers, and the alternatives De
       Morgan reads off a negated conjunction: the gadget's own name, and
       the list its versions index. *)
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
    (* A De Morgan case would recurse on a rewritten term, demanding
       well-founded recursion on a measure under which negation strictly
       decreases; fusing one unfolding step keeps this pair structural.
       The spine walkers carry the position of the alternative they are
       encoding, and repeat their sibling's non-spine cases for the same
       reason: calling the sibling on the matched term itself would leave
       the guard condition. *)
    Fixpoint encodeNNF (p : T.Pkg.t) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.singleton (p, (Name.Orig n, embedVS vs))
      | FConj a b =>
          T.DepRel.union (encodeNNF p a) (encodeNNF p b)
      | FDisj a b =>
          let nm := Name.Disjunct (a :: disjSpine b) in
          T.DepRel.add (p, (nm, idxSet (List.length (a :: disjSpine b))))
            (T.DepRel.union (encodeNNF (nm, Version.Idx 0) a)
               (encodeDisj nm 1 b))
      | FNeg a => encodeNNFneg p a
      end
    with encodeDisj (nm : Name.t) (i : nat) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.singleton ((nm, Version.Idx i), (Name.Orig n, embedVS vs))
      | FConj a b =>
          T.DepRel.union (encodeNNF (nm, Version.Idx i) a)
            (encodeNNF (nm, Version.Idx i) b)
      | FDisj a b =>
          T.DepRel.union (encodeNNF (nm, Version.Idx i) a)
            (encodeDisj nm (S i) b)
      | FNeg a => encodeNNFneg (nm, Version.Idx i) a
      end
    with encodeNNFneg (p : T.Pkg.t) (f : Formula) : T.DepRel.t :=
      match f with
      | FDep n vs =>
          T.DepRel.add (p, (Name.NegDep n vs, T.VSet.singleton (Version.Idx 1)))
            (SOvd.map (fun u =>
                 ((Name.Orig n, Version.Orig u),
                  (Name.NegDep n vs, T.VSet.singleton (Version.Idx 0))))
               vs)
      | FConj a b =>
          let nm := Name.Disjunct (FNeg a :: negConjSpine b) in
          T.DepRel.add
            (p, (nm, idxSet (List.length (FNeg a :: negConjSpine b))))
            (T.DepRel.union (encodeNNFneg (nm, Version.Idx 0) a)
               (encodeConjNeg nm 1 b))
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg p a) (encodeNNFneg p b)
      | FNeg a => encodeNNF p a
      end
    with encodeConjNeg (nm : Name.t) (i : nat) (f : Formula) : T.DepRel.t :=
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
          T.DepRel.union (encodeNNFneg (nm, Version.Idx i) a)
            (encodeConjNeg nm (S i) b)
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg (nm, Version.Idx i) a)
            (encodeNNFneg (nm, Version.Idx i) b)
      | FNeg a => encodeNNF (nm, Version.Idx i) a
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
      end.

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Module SOet := SetOps DepElt T.Pkg DepRel T.PkgSet.
    Definition reduceReal (R : PkgSet.t) (D : DepRel.t) : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg R)
        (SOet.unionMap (fun '(p, f) => witnessSet (embedPkg p) f) D).

    Module SOed := SetOps DepElt T.DepElt DepRel T.DepRel.
    Definition reduceDeps (D : DepRel.t) : T.DepRel.t :=
      SOed.unionMap (fun '(p, f) => encodeNNF (embedPkg p) f) D.

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

    Lemma mem_reduceReal : forall R D (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal R D) <->
        (exists p, PkgSet.In p R /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\
                     T.PkgSet.In y (witnessSet (embedPkg p) f)).
    Proof.
      intros R D y; unfold reduceReal.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap.
      split.
      - intros [H | [[q g] [He Hy]]]; [left; exact H |].
        right; exists q, g; split; [exact He | exact Hy].
      - intros [H | [q [g [Hd Hy]]]]; [left; exact H |].
        right; exists (q, g); split; [exact Hd | exact Hy].
    Qed.

    Lemma mem_reduceDeps : forall D (d : T.DepElt.t),
        T.DepRel.In d (reduceDeps D) <->
        exists p f, DepRel.In (p, f) D /\
                    T.DepRel.In d (encodeNNF (embedPkg p) f).
    Proof.
      intros D d; unfold reduceDeps; rewrite SOed.mem_unionMap.
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
    Definition packageFormulaResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_packageFormulaResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (packageFormulaResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold packageFormulaResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Definition GadgetName (n : Name.t) : Prop :=
      (exists n' vs, n = Name.NegDep n' vs) \/ (exists fs, n = Name.Disjunct fs).

    Lemma witnessSet_name_classify_aux : forall f : Formula,
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSet p f) -> GadgetName n) /\
        (forall (p : T.Pkg.t) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetNeg p f) -> GadgetName n) /\
        (forall (nm : Name.t) (i : nat) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessDisj nm i f) -> GadgetName n) /\
        (forall (nm : Name.t) (i : nat) (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessConjNeg nm i f) -> GadgetName n).
    Proof.
      unfold GadgetName;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
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
    Qed.

    Lemma witnessSet_not_orig : forall (p : T.Pkg.t) (f : Formula) n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSet p f).
    Proof.
      intros p f n v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall (p : Pkg.t) R D,
        T.PkgSet.In (embedPkg p) (reduceReal R D) -> PkgSet.In p R.
    Proof.
      intros [pn pv] R D H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [q [g [_ Hy]]]].
      - apply embedPkg_injective in Hq as ->; exact HqR.
      - exfalso; exact (witnessSet_not_orig _ _ _ _ Hy).
    Qed.

    Lemma encodeNNF_satisfies : forall (R : T.PkgSet.t) (D : T.DepRel.t)
                                    (r : T.Pkg.t) (S : T.PkgSet.t),
        T.IsResolution R D r S ->
        forall (q : T.Pkg.t) (f : Formula),
          (forall d, T.DepRel.In d (encodeNNF q f) -> T.DepRel.In d D) ->
          T.PkgSet.In q S ->
          Satisfies (packageFormulaResolution S) f.
    Proof.
      intros R D r S Hres; destruct Hres as [Hsub Hroot Hdep Huniq].
      cut (forall f : Formula,
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNF q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S -> Satisfies (packageFormulaResolution S) f) /\
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNFneg q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S -> ~ Satisfies (packageFormulaResolution S) f) /\
        (forall (nm : Name.t) (i0 i : nat),
            (forall d, T.DepRel.In d (encodeDisj nm i0 f) -> T.DepRel.In d D) ->
            T.PkgSet.In (nm, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (disjSpine f) ->
            Satisfies (packageFormulaResolution S) f) /\
        (forall (nm : Name.t) (i0 i : nat),
            (forall d,
                T.DepRel.In d (encodeConjNeg nm i0 f) -> T.DepRel.In d D) ->
            T.PkgSet.In (nm, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (negConjSpine f) ->
            ~ Satisfies (packageFormulaResolution S) f)).
      { intros H q f; exact (proj1 (H f) q). }
      (* the FDep dependency edge, read back through the resolution *)
      assert (Hpos : forall (q : T.Pkg.t) n vs,
                 T.DepRel.In (q, (Name.Orig n, embedVS vs)) D ->
                 T.PkgSet.In q S ->
                 Satisfies (packageFormulaResolution S) (FDep n vs)).
      { intros q n vs Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        unfold embedVS in Hw; apply SOvv.mem_map in Hw;
          destruct Hw as [v [Hv ->]].
        exists v; split; [exact Hv |].
        apply mem_packageFormulaResolution; exact HwS. }
      (* the NegDep gadget: version 1 says the dependency is not taken, and
         every taker of it is pinned to version 0 *)
      assert (Hneg : forall (q : T.Pkg.t) n vs,
                 (forall d,
                     T.DepRel.In d (encodeNNFneg q (FDep n vs)) ->
                     T.DepRel.In d D) ->
                 T.PkgSet.In q S ->
                 ~ Satisfies (packageFormulaResolution S) (FDep n vs)).
      { intros q n vs Henc HqS.
        assert (Hd1 : T.DepRel.In
                  (q, (Name.NegDep n vs, T.VSet.singleton (Version.Idx 1))) D).
        { apply Henc; simpl; apply SOed.add_in; left; reflexivity. }
        destruct (Hdep q HqS _ _ Hd1) as [w [Hw HwS]].
        apply SOvv.singleton_in in Hw; subst w.
        intros [v [Hv HvS]].
        apply mem_packageFormulaResolution in HvS.
        assert (Hd2 : T.DepRel.In ((Name.Orig n, Version.Orig v),
                        (Name.NegDep n vs,
                         T.VSet.singleton (Version.Idx 0))) D).
        { apply Henc; simpl; apply SOed.add_in; right.
          apply SOvd.mem_map; exists v; split; [exact Hv | reflexivity]. }
        destruct (Hdep _ HvS _ _ Hd2) as [w2 [Hw2 Hw2S]].
        apply SOvv.singleton_in in Hw2; subst w2.
        assert (E := Huniq _ _ _ HwS Hw2S); discriminate. }
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa].
      - split4.
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
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
          * refine (IHb4 nm 1 (Datatypes.S i') _ HwS _ _ HsatB); [| lia | simpl; lia].
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
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne].
          * refine (IHa2 (nm, Version.Idx i0) _ HiS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb4 nm (Datatypes.S i0) i _ HiS _ _ HsatB); [| lia | lia].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
          * right; refine (IHb3 nm 1 (Datatypes.S i') _ HwS _ _); [| lia | simpl; lia].
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
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne].
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
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros q Henc HqS; exact (IHa2 q Henc HqS).
        + intros q Henc HqS; simpl; intro Hn; exact (Hn (IHa1 q Henc HqS)).
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          exact (IHa2 (nm, Version.Idx i0) Henc HiS).
        + intros nm i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; intro Hn.
          exact (Hn (IHa1 (nm, Version.Idx i0) Henc HiS)).
    Qed.

    Theorem package_formula_soundness :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D) (reduceDeps D) (embedPkg r) S ->
        IsResolution R D r (packageFormulaResolution S).
    Proof.
      intros R D r S Hres.
      assert (H := Hres); destruct H as [Hsub Hroot Hdep Huniq].
      constructor.
      - intros p Hp; apply mem_packageFormulaResolution in Hp.
        exact (embedPkg_mem_reduceReal p R D (Hsub _ Hp)).
      - apply mem_packageFormulaResolution; exact Hroot.
      - intros p Hp f Hdf.
        apply mem_packageFormulaResolution in Hp.
        apply (encodeNNF_satisfies _ _ _ _ Hres (embedPkg p) f); [| exact Hp].
        intros d Hd; apply mem_reduceDeps;
          exists p, f; split; [exact Hdf | exact Hd].
      - intros n v v' Hv Hv'.
        apply mem_packageFormulaResolution in Hv, Hv'.
        unfold embedPkg in Hv, Hv'; simpl in Hv, Hv'.
        assert (E := Huniq _ _ _ Hv Hv').
        injection E as E; exact E.
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
      end.

    (* The alternative a gadget takes: the first satisfied one, and the last
       one when none is -- which is what the two-alternative chain this
       replaces settled on, and keeps the index inside idxSet. *)
    Fixpoint firstSatIdx (Sv : PkgSet.t) (fs : list Formula) : nat :=
      match fs with
      | nil => 0
      | _ :: nil => 0
      | g :: fs' =>
          if satisfiesb Sv g then 0 else Datatypes.S (firstSatIdx Sv fs')
      end.

    Fixpoint witnessSetTaken (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetTaken S a) (witnessSetTaken S b)
      | FDisj a b =>
          T.PkgSet.add
            (Name.Disjunct (a :: disjSpine b),
             Version.Idx (firstSatIdx S (a :: disjSpine b)))
            (if satisfiesb S a
             then T.PkgSet.union (witnessSetTaken S a) (witnessSetUntaken S b)
             else T.PkgSet.union (witnessSetUntaken S a) (takenDisj S b))
      | FNeg a => witnessSetTakenNeg S a
      end
    with takenDisj (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetTaken S a) (witnessSetTaken S b)
      | FDisj a b =>
          if satisfiesb S a
          then T.PkgSet.union (witnessSetTaken S a) (witnessSetUntaken S b)
          else T.PkgSet.union (witnessSetUntaken S a) (takenDisj S b)
      | FNeg a => witnessSetTakenNeg S a
      end
    with witnessSetTakenNeg (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs => T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 1)
      | FConj a b =>
          T.PkgSet.add
            (Name.Disjunct (FNeg a :: negConjSpine b),
             Version.Idx (firstSatIdx S (FNeg a :: negConjSpine b)))
            (if satisfiesb S a
             then T.PkgSet.union (witnessSetUntakenNeg S a)
                    (takenConjNeg S b)
             else T.PkgSet.union (witnessSetTakenNeg S a)
                    (witnessSetUntakenNeg S b))
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S a) (witnessSetTakenNeg S b)
      | FNeg a => witnessSetTaken S a
      end
    with takenConjNeg (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep n vs => T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 1)
      | FConj a b =>
          if satisfiesb S a
          then T.PkgSet.union (witnessSetUntakenNeg S a) (takenConjNeg S b)
          else T.PkgSet.union (witnessSetTakenNeg S a)
                 (witnessSetUntakenNeg S b)
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S a) (witnessSetTakenNeg S b)
      | FNeg a => witnessSetTaken S a
      end.

    (* The walkers and their hosts agree everywhere but the spine, so the
       host's own case is the walker's plus the gadget version it takes. *)
    Lemma witnessSetTaken_disj_eq : forall S a b,
        witnessSetTaken S (FDisj a b) =
        T.PkgSet.add
          (Name.Disjunct (a :: disjSpine b),
           Version.Idx (firstSatIdx S (a :: disjSpine b)))
          (takenDisj S (FDisj a b)).
    Proof. reflexivity. Qed.

    Lemma witnessSetTakenNeg_conj_eq : forall S a b,
        witnessSetTakenNeg S (FConj a b) =
        T.PkgSet.add
          (Name.Disjunct (FNeg a :: negConjSpine b),
           Version.Idx (firstSatIdx S (FNeg a :: negConjSpine b)))
          (takenConjNeg S (FConj a b)).
    Proof. reflexivity. Qed.

    Lemma takenDisj_disj_eq : forall S a b,
        takenDisj S (FDisj a b) =
        (if satisfiesb S a
         then T.PkgSet.union (witnessSetTaken S a) (witnessSetUntaken S b)
         else T.PkgSet.union (witnessSetUntaken S a) (takenDisj S b)).
    Proof. reflexivity. Qed.

    Lemma takenConjNeg_conj_eq : forall S a b,
        takenConjNeg S (FConj a b) =
        (if satisfiesb S a
         then T.PkgSet.union (witnessSetUntakenNeg S a) (takenConjNeg S b)
         else T.PkgSet.union (witnessSetTakenNeg S a)
                (witnessSetUntakenNeg S b)).
    Proof. reflexivity. Qed.

    Lemma firstSatIdx_lt : forall S fs,
        fs <> nil -> firstSatIdx S fs < List.length fs.
    Proof.
      intros S fs; induction fs as [| g fs IH]; intro Hne.
      - contradiction Hne; reflexivity.
      - destruct fs as [| h t]; [simpl; lia |].
        change (firstSatIdx S (g :: h :: t))
          with (if satisfiesb S g then 0
                else Datatypes.S (firstSatIdx S (h :: t))).
        assert (Hlt : firstSatIdx S (h :: t) < List.length (h :: t))
          by (apply IH; discriminate).
        destruct (satisfiesb S g); simpl List.length in *; lia.
    Qed.

    Lemma disjSpine_nonnil : forall f, disjSpine f <> nil.
    Proof. intro f; destruct f; simpl; discriminate. Qed.

    Lemma negConjSpine_nonnil : forall f, negConjSpine f <> nil.
    Proof. intro f; destruct f; simpl; discriminate. Qed.

    Lemma firstSatIdx_cons : forall S g fs,
        fs <> nil ->
        firstSatIdx S (g :: fs) =
        (if satisfiesb S g then 0 else Datatypes.S (firstSatIdx S fs)).
    Proof.
      intros S g [| h t] Hne;
        [contradiction Hne; reflexivity | reflexivity].
    Qed.

    (* Which alternative a gadget's taken version stands for: the witness of
       that alternative is the one the walker actually laid down. *)
    Lemma takenDisj_firstSat : forall S f,
        Satisfies S f ->
        exists g,
          List.nth_error (disjSpine f) (firstSatIdx S (disjSpine f)) = Some g /\
          Satisfies S g /\
          T.PkgSet.Subset (witnessSetTaken S g) (takenDisj S f).
    Proof.
      intros S f; induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros y Hy; exact Hy]).
      cbn [disjSpine];
        rewrite (firstSatIdx_cons S a (disjSpine b) (disjSpine_nonnil b)).
      destruct (satisfiesb S a) eqn:Ea.
      - exists a; split; [reflexivity |]; split;
          [apply satisfiesb_iff; exact Ea |].
        intros y Hy; simpl; rewrite Ea;
          apply T.PkgSet.union_spec; left; exact Hy.
      - assert (Hb : Satisfies S b).
        { destruct Hsat as [Ha | Hb]; [| exact Hb].
          exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
        destruct (IHb Hb) as [g [Hg [Hsg Hsub]]].
        exists g; split; [exact Hg |]; split; [exact Hsg |].
        intros y Hy; simpl; rewrite Ea;
          apply T.PkgSet.union_spec; right; exact (Hsub y Hy).
    Qed.

    Lemma takenConjNeg_firstSat : forall S f,
        ~ Satisfies S f ->
        exists g,
          List.nth_error (negConjSpine f) (firstSatIdx S (negConjSpine f)) =
            Some g /\
          Satisfies S g /\
          T.PkgSet.Subset (witnessSetTaken S g) (takenConjNeg S f).
    Proof.
      intros S f; induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros y Hy; exact Hy]).
      cbn [negConjSpine];
        rewrite (firstSatIdx_cons S (FNeg a) (negConjSpine b)
                   (negConjSpine_nonnil b)).
      destruct (satisfiesb S a) eqn:Ea.
      - assert (Hb : ~ Satisfies S b).
        { intro Hb; apply Hsat; split;
            [apply satisfiesb_iff; exact Ea | exact Hb]. }
        destruct (IHb Hb) as [g [Hg [Hsg Hsub]]].
        exists g; split;
          [change (satisfiesb S (FNeg a)) with (negb (satisfiesb S a));
           rewrite Ea; exact Hg |]; split; [exact Hsg |].
        intros y Hy; simpl; rewrite Ea;
          apply T.PkgSet.union_spec; right; exact (Hsub y Hy).
      - exists (FNeg a); split;
          [change (satisfiesb S (FNeg a)) with (negb (satisfiesb S a));
           rewrite Ea; reflexivity |]; split;
          [apply satisfiesb_false_iff; exact Ea |].
        intros y Hy; simpl; rewrite Ea;
          apply T.PkgSet.union_spec; left; exact Hy.
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
      intros S f; induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
        intros g Hg; simpl in Hg.
      - destruct Hg as [<- | []]; intros y Hy; exact Hy.
      - destruct Hg as [<- | []]; intros y Hy; exact Hy.
      - destruct Hg as [<- | Hg]; intros y Hy; simpl;
          apply T.PkgSet.union_spec;
          [left; exact Hy | right; exact (IHb g Hg y Hy)].
      - destruct Hg as [<- | []]; intros y Hy; exact Hy.
    Qed.

    Lemma negConjSpine_untaken_sub : forall S f g,
        List.In g (negConjSpine f) ->
        T.PkgSet.Subset (witnessSetUntaken S g) (witnessSetUntakenNeg S f).
    Proof.
      intros S f; induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
        intros g Hg; simpl in Hg.
      - destruct Hg as [<- | []]; intros y Hy; exact Hy.
      - destruct Hg as [<- | Hg]; intros y Hy; simpl;
          apply T.PkgSet.union_spec;
          [left; exact Hy | right; exact (IHb g Hg y Hy)].
      - destruct Hg as [<- | []]; intros y Hy; exact Hy.
      - destruct Hg as [<- | []]; intros y Hy; exact Hy.
    Qed.

    (* Every alternative but the taken one contributes its untaken witness,
       so a gadget version that the resolution does not carry still has the
       shape the encoding's recursive call demands. *)
    Lemma takenDisj_untaken_others : forall S f,
        Satisfies S f ->
        forall k g, List.nth_error (disjSpine f) k = Some g ->
          k <> firstSatIdx S (disjSpine f) ->
          T.PkgSet.Subset (witnessSetUntaken S g) (takenDisj S f).
    Proof.
      intros S f; induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
        intros Hsat k g Hg Hne.
      1, 2, 4:
        cbn [disjSpine] in Hg, Hne;
        apply nth_error_single in Hg; destruct Hg as [-> _];
        exfalso; apply Hne; reflexivity.
      cbn [disjSpine] in Hg, Hne;
        rewrite (firstSatIdx_cons S a (disjSpine b) (disjSpine_nonnil b))
          in Hne.
      rewrite takenDisj_disj_eq; destruct (satisfiesb S a) eqn:Ea;
        simpl in Hne.
      - destruct k as [| k']; [contradiction Hne; reflexivity |].
        cbn [List.nth_error] in Hg.
        intros y Hy; apply T.PkgSet.union_spec; right.
        exact (disjSpine_untaken_sub S b g (List.nth_error_In _ _ Hg) y Hy).
      - destruct k as [| k'].
        + cbn [List.nth_error] in Hg; injection Hg as <-.
          intros y Hy; apply T.PkgSet.union_spec; left; exact Hy.
        + cbn [List.nth_error] in Hg.
          assert (Hb : Satisfies S b).
          { destruct Hsat as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
          assert (Hne' : k' <> firstSatIdx S (disjSpine b))
            by (intro E; apply Hne; f_equal; exact E).
          intros y Hy; apply T.PkgSet.union_spec; right.
          exact (IHb Hb k' g Hg Hne' y Hy).
    Qed.

    Lemma takenConjNeg_untaken_others : forall S f,
        ~ Satisfies S f ->
        forall k g, List.nth_error (negConjSpine f) k = Some g ->
          k <> firstSatIdx S (negConjSpine f) ->
          T.PkgSet.Subset (witnessSetUntaken S g) (takenConjNeg S f).
    Proof.
      intros S f; induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa];
        intros Hsat k g Hg Hne.
      1, 3, 4:
        cbn [negConjSpine] in Hg, Hne;
        apply nth_error_single in Hg; destruct Hg as [-> _];
        exfalso; apply Hne; reflexivity.
      cbn [negConjSpine] in Hg, Hne;
        rewrite (firstSatIdx_cons S (FNeg a) (negConjSpine b)
                   (negConjSpine_nonnil b)) in Hne.
      rewrite takenConjNeg_conj_eq;
        change (satisfiesb S (FNeg a)) with (negb (satisfiesb S a)) in Hne;
        destruct (satisfiesb S a) eqn:Ea; simpl in Hne.
      - destruct k as [| k'].
        + cbn [List.nth_error] in Hg; injection Hg as <-.
          intros y Hy; apply T.PkgSet.union_spec; left; exact Hy.
        + cbn [List.nth_error] in Hg.
          assert (Hb : ~ Satisfies S b).
          { intro Hb; apply Hsat; split;
              [apply satisfiesb_iff; exact Ea | exact Hb]. }
          assert (Hne' : k' <> firstSatIdx S (negConjSpine b))
            by (intro E; apply Hne; f_equal; exact E).
          intros y Hy; apply T.PkgSet.union_spec; right.
          exact (IHb Hb k' g Hg Hne' y Hy).
      - destruct k as [| k']; [contradiction Hne; reflexivity |].
        cbn [List.nth_error] in Hg.
        intros y Hy; apply T.PkgSet.union_spec; right.
        exact (negConjSpine_untaken_sub S b g (List.nth_error_In _ _ Hg) y Hy).
    Qed.

    Definition coreResolution (S : PkgSet.t) (D : DepRel.t) : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg S)
        (SOet.unionMap (fun '(p, f) =>
             if PkgSet.mem p S
             then witnessSetTaken S f
             else witnessSetUntaken S f)
           D).

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
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
      - split4.
        + intros p y H; exfalso; exact (SOpt.empty_in _ H).
        + intros p y; simpl; destruct (depTakenb S m ws); intro H;
            [apply SOpt.singleton_in in H; subst y;
             apply SOpt.add_in; left; reflexivity
            | exfalso; exact (SOpt.empty_in _ H)].
        + intros nm i y H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i y; simpl; destruct (depTakenb S m ws); intro H;
            [apply SOpt.singleton_in in H; subst y;
             apply SOpt.add_in; left; reflexivity
            | exfalso; exact (SOpt.empty_in _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 p _ H) | right; exact (IHb1 p _ H)].
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H;
            apply T.PkgSet.union_spec; right; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb4 _ _ _ H)].
        + intros nm i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb1 _ _ H)].
        + intros nm i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb4 _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H;
            apply T.PkgSet.union_spec; right; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 p _ H) | right; exact (IHb2 p _ H)].
        + intros nm i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros nm i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros p y; exact (IHa2 p y).
        + intros p y; exact (IHa1 p y).
        + intros nm i y; exact (IHa2 _ y).
        + intros nm i y; exact (IHa1 _ y).
    Qed.

    Lemma witnessSetUntaken_subset_witnessSet : forall S (p : T.Pkg.t) f,
        T.PkgSet.Subset (witnessSetUntaken S f) (witnessSet p f).
    Proof.
      intros S p f;
        exact (proj1 (witnessSetUntaken_subset_witnessSet_aux S f) p).
    Qed.

    Lemma witnessSetTaken_subset_witnessSet_aux : forall S f,
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTaken S f) (witnessSet p f)) /\
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTakenNeg S f) (witnessSetNeg p f)) /\
        (forall (nm : Name.t) (i : nat),
            T.PkgSet.Subset (takenDisj S f) (witnessDisj nm i f)) /\
        (forall (nm : Name.t) (i : nat),
            T.PkgSet.Subset (takenConjNeg S f) (witnessConjNeg nm i f)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
      - split4.
        + intros p y H; exfalso; exact (SOpt.empty_in _ H).
        + intros p y; simpl; intro H; apply SOpt.singleton_in in H; subst y;
            apply SOpt.add_in; right; apply SOpt.singleton_in; reflexivity.
        + intros nm i y H; exfalso; exact (SOpt.empty_in _ H).
        + intros nm i y; simpl; intro H; apply SOpt.singleton_in in H; subst y;
            apply SOpt.add_in; right; apply SOpt.singleton_in; reflexivity.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_subset_witnessSet_aux S a)
            as (Ua1 & Ua2 & Ua3 & Ua4);
          pose proof (witnessSetUntaken_subset_witnessSet_aux S b)
            as (Ub1 & Ub2 & Ub3 & Ub4); split4.
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 p _ H) | right; exact (IHb1 p _ H)].
        + intros p y; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; simpl witnessSetNeg;
            apply T.PkgSet.union_spec.
          * destruct H as [-> | H].
            -- left; apply mem_idxPkgs;
                 exists (firstSatIdx S (FNeg a :: negConjSpine b));
                 split; [apply firstSatIdx_lt; discriminate | reflexivity].
            -- right; revert H; simpl takenConjNeg;
                 destruct (satisfiesb S a); intro H;
                 apply T.PkgSet.union_spec in H;
                 apply T.PkgSet.union_spec; destruct H as [H | H];
                 [left; exact (Ua2 _ _ H) | right; exact (IHb4 _ _ _ H)
                 | left; exact (IHa2 _ _ H) | right; exact (Ub4 _ _ _ H)].
        + intros nm i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb1 _ _ H)].
        + intros nm i y; simpl;
            destruct (satisfiesb S a); intro H;
            apply T.PkgSet.union_spec in H;
            apply T.PkgSet.union_spec; destruct H as [H | H];
            [left; exact (Ua2 _ _ H) | right; exact (IHb4 _ _ _ H)
            | left; exact (IHa2 _ _ H) | right; exact (Ub4 _ _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_subset_witnessSet_aux S a)
            as (Ua1 & Ua2 & Ua3 & Ua4);
          pose proof (witnessSetUntaken_subset_witnessSet_aux S b)
            as (Ub1 & Ub2 & Ub3 & Ub4); split4.
        + intros p y; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; simpl witnessSet;
            apply T.PkgSet.union_spec.
          * destruct H as [-> | H].
            -- left; apply mem_idxPkgs;
                 exists (firstSatIdx S (a :: disjSpine b));
                 split; [apply firstSatIdx_lt; discriminate | reflexivity].
            -- right; revert H; simpl takenDisj;
                 destruct (satisfiesb S a); intro H;
                 apply T.PkgSet.union_spec in H;
                 apply T.PkgSet.union_spec; destruct H as [H | H];
                 [left; exact (IHa1 _ _ H) | right; exact (Ub3 _ _ _ H)
                 | left; exact (Ua1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 p _ H) | right; exact (IHb2 p _ H)].
        + intros nm i y; simpl;
            destruct (satisfiesb S a); intro H;
            apply T.PkgSet.union_spec in H;
            apply T.PkgSet.union_spec; destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (Ub3 _ _ _ H)
            | left; exact (Ua1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros nm i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros p y; exact (IHa2 p y).
        + intros p y; exact (IHa1 p y).
        + intros nm i y; exact (IHa2 _ y).
        + intros nm i y; exact (IHa1 _ y).
    Qed.

    Lemma witnessSetTaken_subset_witnessSet : forall S (p : T.Pkg.t) f,
        T.PkgSet.Subset (witnessSetTaken S f) (witnessSet p f).
    Proof.
      intros S p f;
        exact (proj1 (witnessSetTaken_subset_witnessSet_aux S f) p).
    Qed.

    Lemma witnessSetUntaken_negDep_det_aux : forall S f,
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntaken S f) ->
            v = Version.Idx 0) /\
        (forall n vs v,
            T.PkgSet.In (Name.NegDep n vs, v) (witnessSetUntakenNeg S f) ->
            v = Version.Idx 0).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
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
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
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
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
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
    Qed.

    Lemma witnessSetUntaken_disjunct_det : forall S f fs v,
        T.PkgSet.In (Name.Disjunct fs, v) (witnessSetUntaken S f) -> False.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_disjunct_det_aux S f)).
    Qed.

    Lemma witnessSetTaken_disjunct_det_aux : forall S f,
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (witnessSetTaken S f) ->
            v = Version.Idx (firstSatIdx S fs)) /\
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (witnessSetTakenNeg S f) ->
            v = Version.Idx (firstSatIdx S fs)) /\
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (takenDisj S f) ->
            v = Version.Idx (firstSatIdx S fs)) /\
        (forall fs v,
            T.PkgSet.In (Name.Disjunct fs, v) (takenConjNeg S f) ->
            v = Version.Idx (firstSatIdx S fs)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
      - split4; intros fs v; simpl; intro H;
          solve [exfalso; exact (SOpt.empty_in _ H)
                | apply SOpt.singleton_in in H; congruence].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_disjunct_det_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_disjunct_det_aux S b) as (Ub1 & Ub2);
          split4.
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros fs v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; simpl takenConjNeg; destruct (satisfiesb S a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exfalso; exact (Ua2 _ _ H) | exact (IHb4 _ _ H)
            | exact (IHa2 _ _ H) | exfalso; exact (Ub2 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros fs v; simpl; destruct (satisfiesb S a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exfalso; exact (Ua2 _ _ H) | exact (IHb4 _ _ H)
            | exact (IHa2 _ _ H) | exfalso; exact (Ub2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_disjunct_det_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_disjunct_det_aux S b) as (Ub1 & Ub2);
          split4.
        + intros fs v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; simpl takenDisj; destruct (satisfiesb S a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exfalso; exact (Ub1 _ _ H)
            | exfalso; exact (Ua1 _ _ H) | exact (IHb3 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros fs v; simpl; destruct (satisfiesb S a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exfalso; exact (Ub1 _ _ H)
            | exfalso; exact (Ua1 _ _ H) | exact (IHb3 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4;
          intros fs v; [exact (IHa2 fs v) | exact (IHa1 fs v)
                       | exact (IHa2 fs v) | exact (IHa1 fs v)].
    Qed.

    Lemma witnessSetTaken_disjunct_det : forall S f fs v,
        T.PkgSet.In (Name.Disjunct fs, v) (witnessSetTaken S f) ->
        v = Version.Idx (firstSatIdx S fs).
    Proof.
      intros S f; exact (proj1 (witnessSetTaken_disjunct_det_aux S f)).
    Qed.

    Lemma witnessSetTaken_negDep_det_aux : forall S f,
        (Satisfies S f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTaken S f) ->
           v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)) /\
        (~ Satisfies S f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTakenNeg S f) ->
           v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)) /\
        (Satisfies S f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (takenDisj S f) ->
           v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)) /\
        (~ Satisfies S f ->
         forall n vs v,
           T.PkgSet.In (Name.NegDep n vs, v) (takenConjNeg S f) ->
           v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
      - split4; intros Hyp n vs v; simpl; intro H;
          solve
            [exfalso; exact (SOpt.empty_in _ H)
            | apply SOpt.singleton_in in H; injection H as -> -> ->;
              destruct (depTakenb S m ws) eqn:E; [| reflexivity];
              exfalso; apply Hyp, depTakenb_iff; exact E].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_negDep_val_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_negDep_val_aux S b) as (Ub1 & Ub2);
          split4.
        + intros Hyp n vs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 (proj1 Hyp) _ _ _ H)
            | exact (IHb1 (proj2 Hyp) _ _ _ H)].
        + intros Hyp n vs v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H]; [congruence |].
          revert H; simpl takenConjNeg; destruct (satisfiesb S a) eqn:Ea;
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
        + intros Hyp n vs v; simpl; destruct (satisfiesb S a) eqn:Ea;
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
          split4.
        + intros Hyp n vs v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H]; [congruence |].
          revert H; simpl takenDisj; destruct (satisfiesb S a) eqn:Ea;
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * apply (IHa1); [apply satisfiesb_iff; exact Ea | exact H].
          * exact (Ub1 _ _ _ H).
          * exact (Ua1 _ _ _ H).
          * apply (IHb3); [| exact H].
            destruct Hyp as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha).
        + intros Hyp n vs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply (IHa2); [intro Ha; exact (Hyp (or_introl Ha)) | exact H]
            | apply (IHb2); [intro Hb; exact (Hyp (or_intror Hb)) | exact H]].
        + intros Hyp n vs v; simpl; destruct (satisfiesb S a) eqn:Ea;
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * apply (IHa1); [apply satisfiesb_iff; exact Ea | exact H].
          * exact (Ub1 _ _ _ H).
          * exact (Ua1 _ _ _ H).
          * apply (IHb3); [| exact H].
            destruct Hyp as [Ha | Hb]; [| exact Hb].
            exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha).
        + intros Hyp n vs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [apply (IHa2); [intro Ha; exact (Hyp (or_introl Ha)) | exact H]
            | apply (IHb2); [intro Hb; exact (Hyp (or_intror Hb)) | exact H]].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4; intros Hyp n vs v.
        + exact (IHa2 Hyp n vs v).
        + exact (IHa1 (satisfies_double_neg S a Hyp) n vs v).
        + exact (IHa2 Hyp n vs v).
        + exact (IHa1 (satisfies_double_neg S a Hyp) n vs v).
    Qed.

    Lemma witnessSetTaken_negDep_det : forall S f,
        Satisfies S f ->
        forall n vs v,
          T.PkgSet.In (Name.NegDep n vs, v) (witnessSetTaken S f) ->
          v = (if depTakenb S n vs then Version.Idx 0 else Version.Idx 1).
    Proof. intros S f; exact (proj1 (witnessSetTaken_negDep_det_aux S f)). Qed.

    Lemma witnessSetUntaken_name_classify_aux : forall S f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetUntaken S f) -> GadgetName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetUntakenNeg S f) -> GadgetName n).
    Proof.
      unfold GadgetName; intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
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
    Qed.

    Lemma witnessSetUntaken_name_classify :
      forall S f (n : Name.t) (v : Version.t),
        T.PkgSet.In (n, v) (witnessSetUntaken S f) -> GadgetName n.
    Proof.
      intros S f; exact (proj1 (witnessSetUntaken_name_classify_aux S f)).
    Qed.

    Lemma witnessSetTaken_name_classify_aux : forall S f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTaken S f) -> GadgetName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTakenNeg S f) -> GadgetName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (takenDisj S f) -> GadgetName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (takenConjNeg S f) -> GadgetName n).
    Proof.
      unfold GadgetName; intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
      - split4; intros n v; simpl; intro H;
          solve [exfalso; exact (SOpt.empty_in _ H)
                | apply SOpt.singleton_in in H; injection H as -> _;
                  left; exists m, ws; reflexivity].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_name_classify_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_name_classify_aux S b) as (Ub1 & Ub2);
          unfold GadgetName in Ua1, Ua2, Ub1, Ub2; split4.
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; right; eauto |].
          revert H; simpl takenConjNeg; destruct (satisfiesb S a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (Ua2 _ _ H) | exact (IHb4 _ _ H)
            | exact (IHa2 _ _ H) | exact (Ub2 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; simpl; destruct (satisfiesb S a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (Ua2 _ _ H) | exact (IHb4 _ _ H)
            | exact (IHa2 _ _ H) | exact (Ub2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_name_classify_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_name_classify_aux S b) as (Ub1 & Ub2);
          unfold GadgetName in Ua1, Ua2, Ub1, Ub2; split4.
        + intros n v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; right; eauto |].
          revert H; simpl takenDisj; destruct (satisfiesb S a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (Ub1 _ _ H)
            | exact (Ua1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros n v; simpl; destruct (satisfiesb S a);
            intro H; apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (Ub1 _ _ H)
            | exact (Ua1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4; intros n v;
          [exact (IHa2 n v) | exact (IHa1 n v)
          | exact (IHa2 n v) | exact (IHa1 n v)].
    Qed.

    Lemma witnessSetTaken_name_classify :
      forall S f (n : Name.t) (v : Version.t),
        T.PkgSet.In (n, v) (witnessSetTaken S f) -> GadgetName n.
    Proof.
      intros S f; exact (proj1 (witnessSetTaken_name_classify_aux S f)).
    Qed.

    Lemma witnessSetUntaken_not_orig : forall S f n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSetUntaken S f).
    Proof.
      intros S f n v H.
      destruct (witnessSetUntaken_name_classify S f _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
    Qed.

    Lemma witnessSetTaken_not_orig : forall S f n v,
        ~ T.PkgSet.In (Name.Orig n, v) (witnessSetTaken S f).
    Proof.
      intros S f n v H.
      destruct (witnessSetTaken_name_classify S f _ _ H)
        as [[n' [vs E]] | [fs E]]; discriminate.
    Qed.

    Lemma mem_coreResolution : forall S D (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution S D) <->
        (exists p, PkgSet.In p S /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\
           T.PkgSet.In y (if PkgSet.mem p S
                          then witnessSetTaken S f
                          else witnessSetUntaken S f)).
    Proof.
      intros S D y; unfold coreResolution.
      rewrite T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap.
      split.
      - intros [H | [[q g] [He Hy]]]; [left; exact H |].
        right; exists q, g; split; [exact He | exact Hy].
      - intros [H | [q [g [Hd Hy]]]]; [left; exact H |].
        right; exists (q, g); split; [exact Hd | exact Hy].
    Qed.

    Lemma witnessSet_subset_coreResolution : forall S D p f,
        DepRel.In (p, f) D ->
        T.PkgSet.Subset
          (if PkgSet.mem p S
           then witnessSetTaken S f
           else witnessSetUntaken S f)
          (coreResolution S D).
    Proof.
      intros S D p f Hd y Hy; apply mem_coreResolution; right.
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

    (* Reading a gadget version out of a taken witness: it names an
       alternative that holds, and that alternative's own taken witness is
       already part of the same set. *)
    Lemma witnessSetTaken_disj_mono_aux : forall S f,
        (Satisfies S f ->
         forall fs i,
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i)
             (witnessSetTaken S f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S g /\
             T.PkgSet.Subset (witnessSetTaken S g) (witnessSetTaken S f)) /\
        (~ Satisfies S f ->
         forall fs i,
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i)
             (witnessSetTakenNeg S f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S g /\
             T.PkgSet.Subset (witnessSetTaken S g) (witnessSetTakenNeg S f)) /\
        (Satisfies S f ->
         forall fs i,
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i) (takenDisj S f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S g /\
             T.PkgSet.Subset (witnessSetTaken S g) (takenDisj S f)) /\
        (~ Satisfies S f ->
         forall fs i,
           T.PkgSet.In (Name.Disjunct fs, Version.Idx i) (takenConjNeg S f) ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S g /\
             T.PkgSet.Subset (witnessSetTaken S g) (takenConjNeg S f)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
      - split4; intros Hyp fs i; simpl; intro H;
          solve [exfalso; exact (SOpt.empty_in _ H)
                | apply SOpt.singleton_in in H; discriminate H].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_disjunct_det_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_disjunct_det_aux S b) as (Ub1 & Ub2);
          split4.
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [pick_alt (IHa1 (proj1 Hyp) _ _ H)
               ltac:(apply T.PkgSet.union_spec; left)
            | pick_alt (IHb1 (proj2 Hyp) _ _ H)
                ltac:(apply T.PkgSet.union_spec; right)].
        + intros Hyp fs i; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H].
          * injection H as -> ->;
              pick_alt (takenConjNeg_firstSat S (FConj a b) Hyp)
                ltac:(apply SOpt.add_in; right).
          * revert H; rewrite takenConjNeg_conj_eq;
              destruct (satisfiesb S a) eqn:Ea; intro H;
              apply T.PkgSet.union_spec in H; destruct H as [H | H].
            -- exfalso; exact (Ua2 _ _ H).
            -- assert (Hb : ~ Satisfies S b).
               { intro Hb; apply Hyp; split;
                   [apply satisfiesb_iff; exact Ea | exact Hb]. }
               pick_alt (IHb4 Hb _ _ H)
                 ltac:(apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; right).
            -- pick_alt (IHa2 (proj1 (satisfiesb_false_iff S a) Ea) _ _ H)
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
            destruct (satisfiesb S a) eqn:Ea; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * exfalso; exact (Ua2 _ _ H).
          * assert (Hb : ~ Satisfies S b).
            { intro Hb; apply Hyp; split;
                [apply satisfiesb_iff; exact Ea | exact Hb]. }
            pick_alt (IHb4 Hb _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
          * pick_alt (IHa2 (proj1 (satisfiesb_false_iff S a) Ea) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * exfalso; exact (Ub2 _ _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4);
          pose proof (witnessSetUntaken_disjunct_det_aux S a) as (Ua1 & Ua2);
          pose proof (witnessSetUntaken_disjunct_det_aux S b) as (Ub1 & Ub2);
          split4.
        + intros Hyp fs i; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H].
          * injection H as -> ->;
              pick_alt (takenDisj_firstSat S (FDisj a b) Hyp)
                ltac:(apply SOpt.add_in; right).
          * revert H; rewrite takenDisj_disj_eq;
              destruct (satisfiesb S a) eqn:Ea; intro H;
              apply T.PkgSet.union_spec in H; destruct H as [H | H].
            -- pick_alt (IHa1 (proj1 (satisfiesb_iff S a) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right;
                       apply T.PkgSet.union_spec; left).
            -- exfalso; exact (Ub1 _ _ H).
            -- exfalso; exact (Ua1 _ _ H).
            -- assert (Hb : Satisfies S b).
               { destruct Hyp as [Ha | Hb]; [| exact Hb].
                 exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
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
            destruct (satisfiesb S a) eqn:Ea; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa1 (proj1 (satisfiesb_iff S a) Ea) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * exfalso; exact (Ub1 _ _ H).
          * exfalso; exact (Ua1 _ _ H).
          * assert (Hb : Satisfies S b).
            { destruct Hyp as [Ha | Hb]; [| exact Hb].
              exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
            pick_alt (IHb3 Hb _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa2 (fun Ha => Hyp (or_introl Ha)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * pick_alt (IHb2 (fun Hb => Hyp (or_intror Hb)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4; intros Hyp fs i.
        + exact (IHa2 Hyp fs i).
        + exact (IHa1 (satisfies_double_neg S a Hyp) fs i).
        + exact (IHa2 Hyp fs i).
        + exact (IHa1 (satisfies_double_neg S a Hyp) fs i).
    Qed.

    Lemma coreResolution_disj : forall S D fs i,
        (forall p, PkgSet.In p S ->
         forall f, DepRel.In (p, f) D -> Satisfies S f) ->
        T.PkgSet.In (Name.Disjunct fs, Version.Idx i) (coreResolution S D) ->
        exists g, List.nth_error fs i = Some g /\ Satisfies S g /\
          T.PkgSet.Subset (witnessSetTaken S g) (coreResolution S D).
    Proof.
      intros S D fs i Hclo H; apply mem_coreResolution in H.
      destruct H as [[p [_ Hp]] | [p [g [Hd Hw]]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - pose proof (witnessSet_subset_coreResolution S D p g Hd) as Hsub.
        revert Hw Hsub; destruct (PkgSet.mem p S) eqn:Ep; intros Hw Hsub.
        + assert (Hsat : Satisfies S g).
          { apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hd]. }
          destruct (proj1 (witnessSetTaken_disj_mono_aux S g) Hsat fs i Hw)
            as [h [Hh [Hsh Hsubh]]].
          exists h; split; [exact Hh |]; split; [exact Hsh |].
          intros y Hy; apply Hsub, Hsubh; exact Hy.
        + exfalso; exact (witnessSetUntaken_disjunct_det _ _ _ _ Hw).
    Qed.

    Lemma encodeNNF_dep_closure_aux :
      forall (S : PkgSet.t) (w : T.PkgSet.t),
        (forall p, PkgSet.In p S -> T.PkgSet.In (embedPkg p) w) ->
        (forall n v, T.PkgSet.In (Name.Orig n, v) w ->
           exists p, PkgSet.In p S /\ embedPkg p = (Name.Orig n, v)) ->
        (forall fs i, T.PkgSet.In (Name.Disjunct fs, Version.Idx i) w ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S g /\
             T.PkgSet.Subset (witnessSetTaken S g) w) ->
        forall f : Formula,
          (forall q0 : T.Pkg.t,
              (~ T.PkgSet.In q0 w /\
               T.PkgSet.Subset (witnessSetUntaken S f) w) \/
              (Satisfies S f /\
               T.PkgSet.Subset (witnessSetTaken S f) w) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeNNF q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w) /\
          (forall q0 : T.Pkg.t,
              (~ T.PkgSet.In q0 w /\
               T.PkgSet.Subset (witnessSetUntakenNeg S f) w) \/
              (~ Satisfies S f /\
               T.PkgSet.Subset (witnessSetTakenNeg S f) w) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeNNFneg q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w) /\
          (forall (nm : Name.t) (i0 : nat),
              (forall k g, List.nth_error (disjSpine f) k = Some g ->
                 (~ T.PkgSet.In (nm, Version.Idx (i0 + k)) w /\
                  T.PkgSet.Subset (witnessSetUntaken S g) w) \/
                 (Satisfies S g /\
                  T.PkgSet.Subset (witnessSetTaken S g) w)) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeDisj nm i0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w) /\
          (forall (nm : Name.t) (i0 : nat),
              (forall k g, List.nth_error (negConjSpine f) k = Some g ->
                 (~ T.PkgSet.In (nm, Version.Idx (i0 + k)) w /\
                  T.PkgSet.Subset (witnessSetUntaken S g) w) \/
                 (Satisfies S g /\
                  T.PkgSet.Subset (witnessSetTaken S g) w)) ->
              forall (q : T.Pkg.t) (m : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (m, ws)) (encodeConjNeg nm i0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (m, v) w).
    Proof.
      intros S w Hemb Horig Hdisj f.
      induction f as [n vs | a IHa b IHb | a IHa b IHb | a IHa].
      - split4.
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
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros q0 Hwit q m ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 q0 _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]];
              [left; split; [exact Hq0 |] | right; split; [exact (proj1 Hsat) |]];
              intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb1 q0 _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]];
              [left; split; [exact Hq0 |] | right; split; [exact (proj2 Hsat) |]];
              intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
        + intros q0 Hwit q m ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [[Hq0 _] | [_ Hsub]];
              [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx
                      (firstSatIdx S (FNeg a :: negConjSpine b))); split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S (FNeg a :: negConjSpine b)); split;
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
                  ** intros y Hy; apply Hsub; simpl;
                       apply T.PkgSet.union_spec; left; exact Hy.
                  ** destruct (Nat_as_OT.eq_dec 0
                                 (firstSatIdx S (FNeg a :: negConjSpine b)))
                       as [E0 | Hne].
                     --- exfalso.
                         assert (Hin : T.PkgSet.In
                                   (Name.Disjunct (FNeg a :: negConjSpine b),
                                    Version.Idx 0) w).
                         { apply Hsub; rewrite witnessSetTakenNeg_conj_eq,
                             E0; apply SOpt.add_in; left; reflexivity. }
                         apply T.PkgSet.mem_spec in Hin;
                         discriminate (eq_trans (eq_sym Hin) EM).
                     --- intros y Hy; apply Hsub;
                           rewrite witnessSetTakenNeg_conj_eq;
                           apply SOpt.add_in; right;
                           exact (takenConjNeg_untaken_others S (FConj a b)
                                    Hsat 0 (FNeg a) eq_refl Hne y Hy).
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
                  ** intros y Hy; apply Hsub; simpl;
                       apply T.PkgSet.union_spec; right;
                       exact (negConjSpine_untaken_sub S b g
                                (List.nth_error_In _ _ Hg) y Hy).
                  ** destruct (Nat_as_OT.eq_dec (1 + k)
                                 (firstSatIdx S (FNeg a :: negConjSpine b)))
                       as [E0 | Hne].
                     --- exfalso.
                         assert (Hin : T.PkgSet.In
                                   (Name.Disjunct (FNeg a :: negConjSpine b),
                                    Version.Idx (1 + k)) w).
                         { apply Hsub; rewrite witnessSetTakenNeg_conj_eq,
                             E0; apply SOpt.add_in; left; reflexivity. }
                         apply T.PkgSet.mem_spec in Hin;
                         discriminate (eq_trans (eq_sym Hin) EM).
                     --- intros y Hy; apply Hsub;
                           rewrite witnessSetTakenNeg_conj_eq;
                           apply SOpt.add_in; right;
                           exact (takenConjNeg_untaken_others S (FConj a b)
                                    Hsat (1 + k) g Hg' Hne y Hy).
        + intros nm i0 Hspine q m ws Henc Hqw.
          assert (Hwit := Hspine 0 (FConj a b) eq_refl);
            replace (i0 + 0) with i0 in Hwit by lia.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 (nm, Version.Idx i0) _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]];
              [left; split; [exact Hq0 |] | right; split; [exact (proj1 Hsat) |]];
              intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb1 (nm, Version.Idx i0) _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hsat Hsub]];
              [left; split; [exact Hq0 |] | right; split; [exact (proj2 Hsat) |]];
              intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
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
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros q0 Hwit q m ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [[Hq0 _] | [_ Hsub]];
              [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx (firstSatIdx S (a :: disjSpine b))); split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S (a :: disjSpine b)); split;
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
                  ** intros y Hy; apply Hsub; simpl;
                       apply T.PkgSet.union_spec; left; exact Hy.
                  ** destruct (Nat_as_OT.eq_dec 0
                                 (firstSatIdx S (a :: disjSpine b)))
                       as [E0 | Hne].
                     --- exfalso.
                         assert (Hin : T.PkgSet.In
                                   (Name.Disjunct (a :: disjSpine b),
                                    Version.Idx 0) w).
                         { apply Hsub; rewrite witnessSetTaken_disj_eq, E0;
                             apply SOpt.add_in; left; reflexivity. }
                         apply T.PkgSet.mem_spec in Hin;
                         discriminate (eq_trans (eq_sym Hin) EM).
                     --- intros y Hy; apply Hsub;
                           rewrite witnessSetTaken_disj_eq;
                           apply SOpt.add_in; right;
                           exact (takenDisj_untaken_others S (FDisj a b)
                                    Hsat 0 a eq_refl Hne y Hy).
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
                  ** intros y Hy; apply Hsub; simpl;
                       apply T.PkgSet.union_spec; right;
                       exact (disjSpine_untaken_sub S b g
                                (List.nth_error_In _ _ Hg) y Hy).
                  ** destruct (Nat_as_OT.eq_dec (1 + k)
                                 (firstSatIdx S (a :: disjSpine b)))
                       as [E0 | Hne].
                     --- exfalso.
                         assert (Hin : T.PkgSet.In
                                   (Name.Disjunct (a :: disjSpine b),
                                    Version.Idx (1 + k)) w).
                         { apply Hsub; rewrite witnessSetTaken_disj_eq, E0;
                             apply SOpt.add_in; left; reflexivity. }
                         apply T.PkgSet.mem_spec in Hin;
                         discriminate (eq_trans (eq_sym Hin) EM).
                     --- intros y Hy; apply Hsub;
                           rewrite witnessSetTaken_disj_eq;
                           apply SOpt.add_in; right;
                           exact (takenDisj_untaken_others S (FDisj a b)
                                    Hsat (1 + k) g Hg' Hne y Hy).
        + intros q0 Hwit q m ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa2 q0 _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [intro Ha; exact (Hns (or_introl Ha)) |]];
              intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb2 q0 _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
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
              intros y Hy; apply Hsub, T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb2 (nm, Version.Idx i0) _ q m ws He Hqw).
            destruct Hwit as [[Hq0 Hsub] | [Hns Hsub]];
              [left; split; [exact Hq0 |]
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros y Hy; apply Hsub, T.PkgSet.union_spec; right; exact Hy.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros q0 Hwit q m ws Henc Hqw.
          exact (IHa2 q0 Hwit q m ws Henc Hqw).
        + intros q0 Hwit q m ws Henc Hqw.
          destruct Hwit as [[Hq0 Hsub] | [Hnn Hsub]];
            [exact (IHa1 q0 (or_introl (conj Hq0 Hsub)) q m ws Henc Hqw)
            | exact (IHa1 q0
                       (or_intror (conj (satisfies_double_neg S a Hnn) Hsub))
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
                       (or_intror (conj (satisfies_double_neg S a Hnn) Hsub))
                       q m ws Henc Hqw)].
    Qed.

    Theorem package_formula_completeness :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t),
        IsResolution R D r S ->
        T.IsResolution (reduceReal R D) (reduceDeps D) (embedPkg r)
          (coreResolution S D).
    Proof.
      intros R D r S Hres; destruct Hres as [Hsub Hroot Hclo Huniq].
      assert (Hemb : forall p, PkgSet.In p S ->
          T.PkgSet.In (embedPkg p) (coreResolution S D)).
      { intros p Hp; apply mem_coreResolution; left.
        exists p; split; [exact Hp | reflexivity]. }
      assert (Horig : forall n v,
          T.PkgSet.In (Name.Orig n, v) (coreResolution S D) ->
          exists p, PkgSet.In p S /\ embedPkg p = (Name.Orig n, v)).
      { intros n v Hv; apply mem_coreResolution in Hv.
        destruct Hv as [[p [Hp Hpe]] | [p [g [Hd Hw]]]].
        - exists p; split; [exact Hp | symmetry; exact Hpe].
        - exfalso; revert Hw; destruct (PkgSet.mem p S); intro Hw;
            [exact (witnessSetTaken_not_orig _ _ _ _ Hw)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw)]. }
      assert (Hdisj := fun fs i => coreResolution_disj S D fs i Hclo).
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy.
        apply mem_reduceReal.
        destruct Hy as [[p [Hp ->]] | [p [g [Hd Hw]]]].
        + left; exists p; split; [apply Hsub; exact Hp | reflexivity].
        + right; exists p, g; split; [exact Hd |].
          revert Hw; destruct (PkgSet.mem p S); intro Hw;
            [exact (witnessSetTaken_subset_witnessSet
                      S (embedPkg p) g _ Hw)
            | exact (witnessSetUntaken_subset_witnessSet
                       S (embedPkg p) g _ Hw)].
      - exact (Hemb r Hroot).
      - intros q Hq m vs Hd.
        apply mem_reduceDeps in Hd; destruct Hd as [p [g [Hpg Henc]]].
        destruct (PkgSet.mem p S) eqn:Ep.
        + refine (proj1 (encodeNNF_dep_closure_aux S _ Hemb Horig Hdisj g)
            (embedPkg p) _ q m vs Henc Hq).
          right; split.
          * apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hpg].
          * pose proof (witnessSet_subset_coreResolution S D p g Hpg) as Hs;
              rewrite Ep in Hs; exact Hs.
        + refine (proj1 (encodeNNF_dep_closure_aux S _ Hemb Horig Hdisj g)
            (embedPkg p) _ q m vs Henc Hq).
          left; split.
          * intro Hin; destruct p as [pn pv].
            destruct (Horig pn (Version.Orig pv) Hin) as [[qn qv] [HqS Hqe]].
            unfold embedPkg in Hqe; simpl in Hqe; injection Hqe as -> ->.
            apply PkgSet.mem_spec in HqS; congruence.
          * pose proof (witnessSet_subset_coreResolution S D p g Hpg) as Hs;
              rewrite Ep in Hs; exact Hs.
      - intros n v v' Hv Hv'.
        apply mem_coreResolution in Hv, Hv'.
        destruct Hv as [[p1 [Hp1 He1]] | [p1 [g1 [Hd1 Hw1]]]];
          destruct Hv' as [[p2 [Hp2 He2]] | [p2 [g2 [Hd2 Hw2]]]].
        + destruct p1 as [n1 w1]; destruct p2 as [n2 w2].
          unfold embedPkg in He1, He2; simpl in He1, He2.
          injection He1 as -> ->; injection He2 as -> ->.
          f_equal; exact (Huniq _ _ _ Hp1 Hp2).
        + destruct p1 as [n1 w1]; unfold embedPkg in He1; simpl in He1;
            injection He1 as -> ->.
          exfalso; revert Hw2; destruct (PkgSet.mem p2 S); intro Hw2;
            [exact (witnessSetTaken_not_orig _ _ _ _ Hw2)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw2)].
        + destruct p2 as [n2 w2]; unfold embedPkg in He2; simpl in He2;
            injection He2 as -> ->.
          exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
            [exact (witnessSetTaken_not_orig _ _ _ _ Hw1)
            | exact (witnessSetUntaken_not_orig _ _ _ _ Hw1)].
        + destruct n as [n0 | fs | n0 vs0].
          * exfalso; revert Hw1; destruct (PkgSet.mem p1 S); intro Hw1;
              [exact (witnessSetTaken_not_orig _ _ _ _ Hw1)
              | exact (witnessSetUntaken_not_orig _ _ _ _ Hw1)].
          * assert (G : forall p g v0, DepRel.In (p, g) D ->
                T.PkgSet.In (Name.Disjunct fs, v0)
                  (if PkgSet.mem p S then witnessSetTaken S g
                   else witnessSetUntaken S g) ->
                v0 = Version.Idx (firstSatIdx S fs)).
            { intros p g v0 _ Hw; revert Hw;
                destruct (PkgSet.mem p S); intro Hw.
              - exact (witnessSetTaken_disjunct_det _ _ _ _ Hw).
              - exfalso;
                  exact (witnessSetUntaken_disjunct_det _ _ _ _ Hw). }
            rewrite (G _ _ _ Hd1 Hw1), (G _ _ _ Hd2 Hw2); reflexivity.
          * assert (G : forall p g v0, DepRel.In (p, g) D ->
                T.PkgSet.In (Name.NegDep n0 vs0, v0)
                  (if PkgSet.mem p S then witnessSetTaken S g
                   else witnessSetUntaken S g) ->
                v0 =
                  (if depTakenb S n0 vs0 then Version.Idx 0 else Version.Idx 1)).
            { intros p g v0 Hd Hw; revert Hw;
                destruct (PkgSet.mem p S) eqn:Ep; intro Hw.
              - apply (witnessSetTaken_negDep_det S g); [| exact Hw].
                apply (Hclo p); [apply PkgSet.mem_spec; exact Ep | exact Hd].
              - assert (E : depTakenb S n0 vs0 = true).
                { apply depTakenb_iff;
                    exact (witnessSetUntaken_negDep_exists _ _ _ _ _ Hw). }
                rewrite E;
                  exact (witnessSetUntaken_negDep_det _ _ _ _ _ Hw). }
            rewrite (G _ _ _ Hd1 Hw1), (G _ _ _ Hd2 Hw2); reflexivity.
    Qed.

    Module Lookup.
      Inductive Atom : Type :=
      | APos (n : N.t) (vs : VSet.t)
      | ANeg (n : N.t) (vs : VSet.t)
      | ADisj (fs : list Formula).

      Module AComp <: ComparableType.
        Definition t := Atom.
        Definition compare (x y : t) : comparison :=
          match x, y with
          | APos n1 vs1, APos n2 vs2 => C.Dependees.compare (n1, vs1) (n2, vs2)
          | APos _ _, _ => Lt
          | ANeg _ _, APos _ _ => Gt
          | ANeg n1 vs1, ANeg n2 vs2 => C.Dependees.compare (n1, vs1) (n2, vs2)
          | ANeg _ _, ADisj _ => Lt
          | ADisj fs1, ADisj fs2 => FListOT.compare fs1 fs2
          | ADisj _, _ => Gt
          end.

        Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
        Proof. cmp_eq_iff cmp_pkgf. Qed.

        Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
        Proof. cmp_antisym cmp_pkgf. Qed.

        Lemma compare_lt_trans : forall x y z,
            compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
        Proof. cmp_lt_trans cmp_pkgf. Qed.
      End AComp.
      Module AOT := UOTFromCompare AComp.
      Module AtomSet := FSetUOT AOT.

      (* Mutual structural pairs (f, f-under-negation) for the same reason as
         encodeNNF, so the equations hold by reflexivity. *)
      Fixpoint deepAtoms (f : Formula) : AtomSet.t :=
        match f with
        | FDep n vs => AtomSet.singleton (APos n vs)
        | FConj a b => AtomSet.union (deepAtoms a) (deepAtoms b)
        | FDisj a b =>
            AtomSet.add (ADisj (a :: disjSpine b))
              (AtomSet.union (deepAtoms a) (deepAtoms b))
        | FNeg a => deepAtomsNeg a
        end
      with deepAtomsNeg (f : Formula) : AtomSet.t :=
        match f with
        | FDep n vs => AtomSet.singleton (ANeg n vs)
        | FConj a b =>
            AtomSet.add (ADisj (FNeg a :: negConjSpine b))
              (AtomSet.union (deepAtomsNeg a) (deepAtomsNeg b))
        | FDisj a b => AtomSet.union (deepAtomsNeg a) (deepAtomsNeg b)
        | FNeg a => deepAtoms a
        end.

      Module NEqb := UOTEqb N.
      Definition occursNegOnb (f : Formula) (n : N.t) (v : V.t) : bool :=
        AtomSet.exists_ (fun a =>
            match a with
            | ANeg n' vs => andb (NEqb.eqb n' n) (VSet.mem v vs)
            | _ => false
            end)
          (deepAtoms f).

      Definition disjAlt (fs : list Formula) (i : Version.t) :
          option Formula :=
        match i with
        | Version.Orig _ => None
        | Version.Idx k => List.nth_error fs k
        end.

      Definition withNegOn (D : DepRel.t) (n : N.t) (v : V.t) : DepRel.t :=
        DepRel.filter (fun '(_, f) => occursNegOnb f n v) D.

      Module DepRelFibred := FibredRel Pkg Dependees DepElt DepRel.
      Definition subInstanceOrig (D : DepRel.t) (p : Pkg.t) : DepRel.t :=
        let '(n, v) := p in
        DepRel.union (DepRelFibred.tailFibre D (n, v)) (withNegOn D n v).

      Lemma encodeNNF_src_orig_aux : forall f,
          (forall (q : T.Pkg.t) n v (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig n, Version.Orig v), d) (encodeNNF q f) ->
              q = (Name.Orig n, Version.Orig v) \/
              exists vs,
                AtomSet.In (ANeg n vs) (deepAtoms f) /\ VSet.In v vs) /\
          (forall (q : T.Pkg.t) n v (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig n, Version.Orig v), d)
                (encodeNNFneg q f) ->
              q = (Name.Orig n, Version.Orig v) \/
              exists vs,
                AtomSet.In (ANeg n vs) (deepAtomsNeg f) /\ VSet.In v vs) /\
          (forall (nm : Name.t) (i0 : nat) n v (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig n, Version.Orig v), d)
                (encodeDisj nm i0 f) ->
              exists vs,
                AtomSet.In (ANeg n vs) (deepAtoms f) /\ VSet.In v vs) /\
          (forall (nm : Name.t) (i0 : nat) n v (d : T.Dependees.t),
              T.DepRel.In ((Name.Orig n, Version.Orig v), d)
                (encodeConjNeg nm i0 f) ->
              exists vs,
                AtomSet.In (ANeg n vs) (deepAtomsNeg f) /\ VSet.In v vs).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
        - split4.
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
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; left;
                 exact Ha
                | exact Hv].
            * destruct (IHb4 _ _ _ _ _ H) as [vs [Ha Hv]].
              right; exists vs; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; right;
                 exact Ha
                | exact Hv].
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
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; left;
                 exact Ha
                | exact Hv].
            * destruct (IHb4 _ _ _ _ _ H) as [vs [Ha Hv]].
              exists vs; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; right;
                 exact Ha
                | exact Hv].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q n v d H; simpl in H; simpl.
            apply SOed.add_in in H; destruct H as [H | H]; [left; congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [E | [vs [Ha Hv]]];
                [discriminate |].
              right; exists vs; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; left;
                 exact Ha
                | exact Hv].
            * destruct (IHb3 _ _ _ _ _ H) as [vs [Ha Hv]].
              right; exists vs; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; right;
                 exact Ha
                | exact Hv].
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
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; left;
                 exact Ha
                | exact Hv].
            * destruct (IHb3 _ _ _ _ _ H) as [vs [Ha Hv]].
              exists vs; split;
                [apply AtomSet.add_spec; right; apply AtomSet.union_spec; right;
                 exact Ha
                | exact Hv].
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
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros q n v d H; exact (IHa2 _ _ _ _ H).
          + intros q n v d H; exact (IHa1 _ _ _ _ H).
          + intros nm i0 n v d H.
            destruct (IHa2 _ _ _ _ H) as [E | Hx]; [discriminate | exact Hx].
          + intros nm i0 n v d H.
            destruct (IHa1 _ _ _ _ H) as [E | Hx]; [discriminate | exact Hx].
      Qed.

      Lemma occursNegOnb_iff : forall f n v,
          occursNegOnb f n v = true <->
          exists vs, AtomSet.In (ANeg n vs) (deepAtoms f) /\ VSet.In v vs.
      Proof.
        intros f n v; unfold occursNegOnb.
        rewrite AtomSet.exists_spec'.
        split.
        - intros [[m ws | m ws | fs] [Ha Hm]]; simpl in Hm; try discriminate.
          apply Bool.andb_true_iff in Hm as [Hn Hv].
          apply NEqb.eqb_true_iff in Hn as ->.
          exists ws; split; [exact Ha | apply VSet.mem_spec; exact Hv].
        - intros [vs [Ha Hv]].
          exists (ANeg n vs); split; [exact Ha |]; simpl.
          rewrite NEqb.eqb_refl; simpl; apply VSet.mem_spec; exact Hv.
      Qed.

      Lemma encodeNNF_src_negDep_aux : forall f,
          (forall (q : T.Pkg.t) n vs (i : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d) (encodeNNF q f) ->
              q = (Name.NegDep n vs, i)) /\
          (forall (q : T.Pkg.t) n vs (i : Version.t) (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d) (encodeNNFneg q f) ->
              q = (Name.NegDep n vs, i)) /\
          (forall (nm : Name.t) (i0 : nat) n vs (i : Version.t)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d) (encodeDisj nm i0 f) ->
              Name.NegDep n vs = nm) /\
          (forall (nm : Name.t) (i0 : nat) n vs (i : Version.t)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.NegDep n vs, i), d) (encodeConjNeg nm i0 f) ->
              Name.NegDep n vs = nm).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
        - split4.
          + intros q n vs i d H; apply SOed.singleton_in in H; congruence.
          + intros q n vs i d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
          + intros nm i0 n vs i d H; apply SOed.singleton_in in H; congruence.
          + intros nm i0 n vs i d H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros q n vs i d H; exact (IHa2 _ _ _ _ _ H).
          + intros q n vs i d H; exact (IHa1 _ _ _ _ _ H).
          + intros nm i0 n vs i d H.
            assert (E := IHa2 _ _ _ _ _ H); injection E as E1 E2;
              symmetry; exact E1.
          + intros nm i0 n vs i d H.
            assert (E := IHa1 _ _ _ _ _ H); injection E as E1 E2;
              symmetry; exact E1.
      Qed.

      (* the witness walkers hand the disjunction gadget's own name down the
         spine, which is why the spine cases carry the extra alternative. *)
      Definition gadgetAtom (nm : Name.t) : option Atom :=
        match nm with
        | Name.Orig _ => None
        | Name.Disjunct fs => Some (ADisj fs)
        | Name.NegDep n vs => Some (ANeg n vs)
        end.

      Definition MintedBy (nm : Name.t) (A : AtomSet.t) : Prop :=
        exists a, gadgetAtom nm = Some a /\ AtomSet.In a A.

      Lemma MintedBy_unionL : forall nm A B,
          MintedBy nm A -> MintedBy nm (AtomSet.union A B).
      Proof.
        intros nm A B [a [Ha HA]]; exists a;
          split; [exact Ha | apply AtomSet.union_spec; left; exact HA].
      Qed.

      Lemma MintedBy_unionR : forall nm A B,
          MintedBy nm B -> MintedBy nm (AtomSet.union A B).
      Proof.
        intros nm A B [a [Ha HB]]; exists a;
          split; [exact Ha | apply AtomSet.union_spec; right; exact HB].
      Qed.

      Lemma MintedBy_add : forall nm a A,
          MintedBy nm A -> MintedBy nm (AtomSet.add a A).
      Proof.
        intros nm a A [b [Hb HA]]; exists b;
          split; [exact Hb | apply AtomSet.add_spec; right; exact HA].
      Qed.

      Lemma witness_atom_aux : forall f : Formula,
          (forall (p : T.Pkg.t) (nm : Name.t) (w : Version.t),
              T.PkgSet.In (nm, w) (witnessSet p f) ->
              MintedBy nm (deepAtoms f)) /\
          (forall (p : T.Pkg.t) (nm : Name.t) (w : Version.t),
              T.PkgSet.In (nm, w) (witnessSetNeg p f) ->
              MintedBy nm (deepAtomsNeg f)) /\
          (forall (nm0 : Name.t) (i : nat) (nm : Name.t) (w : Version.t),
              T.PkgSet.In (nm, w) (witnessDisj nm0 i f) ->
              MintedBy nm (deepAtoms f) \/ nm = nm0) /\
          (forall (nm0 : Name.t) (i : nat) (nm : Name.t) (w : Version.t),
              T.PkgSet.In (nm, w) (witnessConjNeg nm0 i f) ->
              MintedBy nm (deepAtomsNeg f) \/ nm = nm0).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
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
              [apply MintedBy_unionL; exact (IHa1 _ _ _ H)
              | apply MintedBy_unionR; exact (IHb1 _ _ _ H)].
          + intros p nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
            * apply mem_idxPkgs in H; destruct H as [j [_ E]];
                injection E as -> _.
              exists (ADisj (FNeg a :: negConjSpine b)); split;
                [reflexivity | apply AtomSet.add_spec; left; reflexivity].
            * apply T.PkgSet.union_spec in H; destruct H as [H | H].
              -- apply MintedBy_add, MintedBy_unionL; exact (IHa2 _ _ _ H).
              -- destruct (IHb4 _ _ _ _ H) as [HM | ->];
                   [apply MintedBy_add, MintedBy_unionR; exact HM |].
                 exists (ADisj (FNeg a :: negConjSpine b)); split;
                   [reflexivity | apply AtomSet.add_spec; left; reflexivity].
          + intros nm0 i nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [left; apply MintedBy_unionL; exact (IHa1 _ _ _ H)
              | left; apply MintedBy_unionR; exact (IHb1 _ _ _ H)].
          + intros nm0 i nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
            * left; apply MintedBy_add, MintedBy_unionL; exact (IHa2 _ _ _ H).
            * destruct (IHb4 _ _ _ _ H) as [HM | E];
                [left; apply MintedBy_add, MintedBy_unionR; exact HM
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
              -- apply MintedBy_add, MintedBy_unionL; exact (IHa1 _ _ _ H).
              -- destruct (IHb3 _ _ _ _ H) as [HM | ->];
                   [apply MintedBy_add, MintedBy_unionR; exact HM |].
                 exists (ADisj (a :: disjSpine b)); split;
                   [reflexivity | apply AtomSet.add_spec; left; reflexivity].
          + intros p nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [apply MintedBy_unionL; exact (IHa2 _ _ _ H)
              | apply MintedBy_unionR; exact (IHb2 _ _ _ H)].
          + intros nm0 i nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
            * left; apply MintedBy_add, MintedBy_unionL; exact (IHa1 _ _ _ H).
            * destruct (IHb3 _ _ _ _ H) as [HM | E];
                [left; apply MintedBy_add, MintedBy_unionR; exact HM
                | right; exact E].
          + intros nm0 i nm w H; simpl in H |- *.
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
              [left; apply MintedBy_unionL; exact (IHa2 _ _ _ H)
              | left; apply MintedBy_unionR; exact (IHb2 _ _ _ H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
          + intros p nm w H; exact (IHa2 _ _ _ H).
          + intros p nm w H; exact (IHa1 _ _ _ H).
          + intros nm0 i nm w H; left; exact (IHa2 _ _ _ H).
          + intros nm0 i nm w H; left; exact (IHa1 _ _ _ H).
      Qed.

      Definition withNeg (D : DepRel.t) (n : N.t) (vs : VSet.t) : DepRel.t :=
        DepRel.filter (fun '(_, f) => AtomSet.mem (ANeg n vs) (deepAtoms f)) D.

      Lemma mem_withNeg : forall D n vs (p : Pkg.t) (f : Formula),
          DepRel.In (p, f) (withNeg D n vs) <->
          DepRel.In (p, f) D /\ AtomSet.In (ANeg n vs) (deepAtoms f).
      Proof.
        intros D n vs p f; unfold withNeg.
        rewrite DepRel.filter_spec'.
        cbn beta iota; rewrite AtomSet.mem_spec; reflexivity.
      Qed.

      Definition gadgetPkgs (nm : Name.t) : T.PkgSet.t :=
        match nm with
        | Name.Orig _ => T.PkgSet.empty
        | Name.Disjunct fs => idxPkgs (Name.Disjunct fs) (List.length fs)
        | Name.NegDep n vs =>
            T.PkgSet.add (Name.NegDep n vs, Version.Idx 0)
              (T.PkgSet.singleton (Name.NegDep n vs, Version.Idx 1))
        end.

      Lemma witnessSet_gadget_aux : forall f : Formula,
          (forall (p q : T.Pkg.t),
              T.PkgSet.In q (witnessSet p f) ->
              T.PkgSet.In q (gadgetPkgs (fst q))) /\
          (forall (p q : T.Pkg.t),
              T.PkgSet.In q (witnessSetNeg p f) ->
              T.PkgSet.In q (gadgetPkgs (fst q))) /\
          (forall (nm : Name.t) (i : nat) (q : T.Pkg.t),
              T.PkgSet.In q (witnessDisj nm i f) ->
              T.PkgSet.In q (gadgetPkgs (fst q))) /\
          (forall (nm : Name.t) (i : nat) (q : T.Pkg.t),
              T.PkgSet.In q (witnessConjNeg nm i f) ->
              T.PkgSet.In q (gadgetPkgs (fst q))).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
        - repeat split.
          + intros p q H; simpl in H; exfalso; exact (SOpt.empty_in _ H).
          + intros p q H; simpl in H;
              rewrite SOpt.add_in, SOpt.singleton_in in H;
              destruct H as [-> | ->]; cbn [fst gadgetPkgs];
              rewrite SOpt.add_in, SOpt.singleton_in;
              [left | right]; reflexivity.
          + intros nm i q H; simpl in H; exfalso; exact (SOpt.empty_in _ H).
          + intros nm i q H; simpl in H;
              rewrite SOpt.add_in, SOpt.singleton_in in H;
              destruct H as [-> | ->]; cbn [fst gadgetPkgs];
              rewrite SOpt.add_in, SOpt.singleton_in;
              [left | right]; reflexivity.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H]; [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
          + intros p q H; simpl in H; apply T.PkgSet.union_spec in H;
              destruct H as [H | H].
            * apply mem_idxPkgs in H; destruct H as [i [Hi ->]];
                cbn [fst gadgetPkgs]; apply mem_idxPkgs; exists i;
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
                cbn [fst gadgetPkgs]; apply mem_idxPkgs; exists i;
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
      Qed.

      Lemma encodeNNF_target_gadget_aux : forall f : Formula,
          (forall (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNF p f) ->
              T.PkgSet.Subset (gadgetPkgs (fst (snd d))) (witnessSet p f)) /\
          (forall (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNFneg p f) ->
              T.PkgSet.Subset (gadgetPkgs (fst (snd d)))
                (witnessSetNeg p f)) /\
          (forall (nm : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeDisj nm i f) ->
              T.PkgSet.Subset (gadgetPkgs (fst (snd d)))
                (witnessDisj nm i f)) /\
          (forall (nm : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeConjNeg nm i f) ->
              T.PkgSet.Subset (gadgetPkgs (fst (snd d)))
                (witnessConjNeg nm i f)).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
        - repeat split.
          + intros p d H; simpl in H; apply SOed.singleton_in in H; subst d;
              cbn [fst snd gadgetPkgs]; apply T.PkgSet.empty_subset.
          + intros p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H];
              [| apply SOvd.mem_map in H; destruct H as [u [_ ->]]];
              intros z Hz; exact Hz.
          + intros nm i d H; simpl in H; apply SOed.singleton_in in H; subst d;
              cbn [fst snd gadgetPkgs]; apply T.PkgSet.empty_subset.
          + intros nm i d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H];
              [| apply SOvd.mem_map in H; destruct H as [u [_ ->]]];
              intros z Hz; exact Hz.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz) | right; exact (IHb1 _ d H z Hz)].
          + intros p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H].
            * intros z Hz; cbn [fst snd gadgetPkgs] in Hz;
                apply T.PkgSet.union_spec; left; exact Hz.
            * apply T.DepRel.union_spec in H; intros z Hz;
                apply T.PkgSet.union_spec; right;
                apply T.PkgSet.union_spec; destruct H as [H | H];
                [left; exact (IHa2 _ d H z Hz)
                | right; exact (IHb4 _ _ d H z Hz)].
          + intros nm i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz) | right; exact (IHb1 _ d H z Hz)].
          + intros nm i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz)
              | right; exact (IHb4 _ _ d H z Hz)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); repeat split.
          + intros p d H; simpl in H; rewrite SOed.add_in in H;
              destruct H as [-> | H].
            * intros z Hz; cbn [fst snd gadgetPkgs] in Hz;
                apply T.PkgSet.union_spec; left; exact Hz.
            * apply T.DepRel.union_spec in H; intros z Hz;
                apply T.PkgSet.union_spec; right;
                apply T.PkgSet.union_spec; destruct H as [H | H];
                [left; exact (IHa1 _ d H z Hz)
                | right; exact (IHb3 _ _ d H z Hz)].
          + intros p d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz) | right; exact (IHb2 _ d H z Hz)].
          + intros nm i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa1 _ d H z Hz)
              | right; exact (IHb3 _ _ d H z Hz)].
          + intros nm i d H; simpl in H; apply T.DepRel.union_spec in H;
              intros z Hz; apply T.PkgSet.union_spec; destruct H as [H | H];
              [left; exact (IHa2 _ d H z Hz) | right; exact (IHb2 _ d H z Hz)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); repeat split.
          + intros p d H; simpl in H; exact (IHa2 _ d H).
          + intros p d H; simpl in H; exact (IHa1 _ d H).
          + intros nm i d H; simpl in H; exact (IHa2 _ d H).
          + intros nm i d H; simpl in H; exact (IHa1 _ d H).
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Theorem versions_lookupOrig : forall R D (r : Pkg.t) (n : N.t),
          (exists p h, T.DepRel.In (p, (Name.Orig n, h)) (reduceDeps D)) \/
          Name.Orig n = Name.Orig (fst r) ->
          T.versions (reduceReal R D) (Name.Orig n) =
          T.versions (reduceReal (PkgFibred.tailFibre R n) DepRel.empty)
            (Name.Orig n).
      Proof.
        intros R D r n _; apply T.versions_ext; intro y.
        rewrite !mem_reduceReal.
        split.
        - intros [[[qn qv] [HR Hq]] | [p [f [_ Hw]]]].
          + unfold embedPkg in Hq; injection Hq as -> ->.
            left; exists (qn, qv).
            split; [apply PkgFibred.mem_tailFibre;
                    split; [exact HR | reflexivity]
                   | reflexivity].
          + exfalso; exact (witnessSet_not_orig _ _ _ _ Hw).
        - intros [[[qn qv] [HR Hq]] | [p [f [Hd _]]]].
          + apply PkgFibred.mem_tailFibre in HR; destruct HR as [HR _].
            left; exists (qn, qv); split; [exact HR | exact Hq].
          + destruct (DepRel.empty_spec Hd).
      Qed.

      Theorem dependees_lookupOrig : forall R D n v,
          T.PkgSet.In (Name.Orig n, Version.Orig v) (reduceReal R D) ->
          T.dependees (reduceDeps D) (Name.Orig n, Version.Orig v) =
          T.dependees (reduceDeps (subInstanceOrig D (n, v)))
            (Name.Orig n, Version.Orig v).
      Proof.
        intros R D n v _; apply T.dependees_ext; intro h.
        split; intro H;
          apply mem_reduceDeps in H; destruct H as [p [f [Hd He]]];
          apply mem_reduceDeps; unfold encodeNNF in He.
        - destruct (proj1 (encodeNNF_src_orig_aux f) _ _ _ _ He)
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

      Theorem versions_lookupDisjunct : forall R D (fs : list Formula),
          (exists p h,
              T.DepRel.In (p, (Name.Disjunct fs, h)) (reduceDeps D)) ->
          T.versions (reduceReal R D) (Name.Disjunct fs) =
          idxSet (List.length fs).
      Proof.
        intros R D fs [p [h Hd]].
        apply mem_reduceDeps in Hd; destruct Hd as [r [g [HD He]]].
        pose proof (proj1 (encodeNNF_target_gadget_aux g) (embedPkg r)
                      (p, (Name.Disjunct fs, h)) He) as Hsub.
        cbn [fst snd] in Hsub.
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_idxSet, mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [r1 [g1 [_ Hw]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + pose proof (proj1 (witnessSet_gadget_aux g1) _ _ Hw) as Hg.
            cbn [fst gadgetPkgs] in Hg; apply mem_idxPkgs in Hg.
            destruct Hg as [i [Hi Hq]]; exists i;
              split; [exact Hi | congruence].
        - intros [i [Hi ->]]; right; exists r, g; split; [exact HD |].
          apply Hsub; cbn [gadgetPkgs]; apply mem_idxPkgs;
            exists i; split; [exact Hi | reflexivity].
      Qed.

      Lemma encodeDisj_alt : forall (f : Formula) (nm : Name.t) (i0 j : nat)
                                    (g : Formula) (d : T.Dependees.t),
          List.nth_error (disjSpine f) j = Some g ->
          T.DepRel.In ((nm, Version.Idx (i0 + j)), d)
            (encodeNNF (nm, Version.Idx (i0 + j)) g) ->
          T.DepRel.In ((nm, Version.Idx (i0 + j)), d) (encodeDisj nm i0 f).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
          intros nm i0 j g d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb nm (S i0) j g d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma encodeConjNeg_alt : forall (f : Formula) (nm : Name.t)
                                       (i0 j : nat) (g : Formula)
                                       (d : T.Dependees.t),
          List.nth_error (negConjSpine f) j = Some g ->
          T.DepRel.In ((nm, Version.Idx (i0 + j)), d)
            (encodeNNF (nm, Version.Idx (i0 + j)) g) ->
          T.DepRel.In ((nm, Version.Idx (i0 + j)), d) (encodeConjNeg nm i0 f).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
          intros nm i0 j g d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb nm (S i0) j g d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma witnessSet_alt_aux : forall f : Formula,
          (forall (p : T.Pkg.t) (gs : list Formula) (k : nat) (g : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k) (witnessSet p f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF p f)) /\
          (forall (p : T.Pkg.t) (gs : list Formula) (k : nat) (g : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessSetNeg p f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNFneg p f)) /\
          (forall (nm : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (g : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessDisj nm i0 f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeDisj nm i0 f)) /\
          (forall (nm : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (g : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessConjNeg nm i0 f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeConjNeg nm i0 f)).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
        - split4.
          + intros p gs k g d H Hg Hd; simpl in H;
              exfalso; exact (SOpt.empty_in _ H).
          + intros p gs k g d H Hg Hd; simpl in H;
              rewrite SOpt.add_in, SOpt.singleton_in in H;
              destruct H as [H | H]; congruence.
          + intros nm i0 gs k g d H Hg Hd; simpl in H;
              exfalso; exact (SOpt.empty_in _ H).
          + intros nm i0 gs k g d H Hg Hd; simpl in H;
              rewrite SOpt.add_in, SOpt.singleton_in in H;
              destruct H as [H | H]; congruence.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
              -- exact (encodeConjNeg_alt b
                          (Name.Disjunct (FNeg a :: negConjSpine b))
                          1 i g d Hg Hd).
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
                | right; exact (IHb4 _ _ _ _ _ _ H Hg Hd)].
          + intros nm i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb1 _ _ _ _ _ H Hg Hd)].
          + intros nm i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb4 _ _ _ _ _ _ H Hg Hd)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros p gs k g d H Hg Hd; simpl in H; simpl.
            apply T.PkgSet.union_spec in H; apply SOed.add_in;
              destruct H as [H | H]; [| right; apply T.DepRel.union_spec].
            * apply mem_idxPkgs in H; destruct H as [i [_ H]];
                injection H as H1 H2; subst gs; subst k; right;
                apply T.DepRel.union_spec; destruct i as [| i];
                simpl in Hg; [left | right].
              -- injection Hg as <-; exact Hd.
              -- exact (encodeDisj_alt b (Name.Disjunct (a :: disjSpine b))
                          1 i g d Hg Hd).
            * apply T.PkgSet.union_spec in H; destruct H as [H | H];
                [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
                | right; exact (IHb3 _ _ _ _ _ _ H Hg Hd)].
          + intros p gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb2 _ _ _ _ _ H Hg Hd)].
          + intros nm i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa1 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb3 _ _ _ _ _ _ H Hg Hd)].
          + intros nm i0 gs k g d H Hg Hd; simpl in H; simpl;
              apply T.PkgSet.union_spec in H; apply T.DepRel.union_spec;
              destruct H as [H | H];
              [left; exact (IHa2 _ _ _ _ _ H Hg Hd)
              | right; exact (IHb2 _ _ _ _ _ H Hg Hd)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros p gs k g d H Hg Hd; exact (IHa2 _ _ _ _ _ H Hg Hd).
          + intros p gs k g d H Hg Hd; exact (IHa1 _ _ _ _ _ H Hg Hd).
          + intros nm i0 gs k g d H Hg Hd; exact (IHa2 _ _ _ _ _ H Hg Hd).
          + intros nm i0 gs k g d H Hg Hd; exact (IHa1 _ _ _ _ _ H Hg Hd).
      Qed.

      Lemma encodeNNF_alt_aux : forall f : Formula,
          (forall (q : T.Pkg.t) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF q f) ->
              q = (Name.Disjunct gs, Version.Idx k) \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (q : T.Pkg.t) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNFneg q f) ->
              q = (Name.Disjunct gs, Version.Idx k) \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (nm : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeDisj nm i0 f) ->
              (nm = Name.Disjunct gs /\
               exists j g, k = i0 + j /\
                           List.nth_error (disjSpine f) j = Some g /\
                           T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                             (encodeNNF (Name.Disjunct gs, Version.Idx k) g))
              \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (nm : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeConjNeg nm i0 f) ->
              (nm = Name.Disjunct gs /\
               exists j g, k = i0 + j /\
                           List.nth_error (negConjSpine f) j = Some g /\
                           T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                             (encodeNNF (Name.Disjunct gs, Version.Idx k) g))
              \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF (Name.Disjunct gs, Version.Idx k) g))).
      Proof.
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
        - split4.
          + intros q gs k d H; apply SOed.singleton_in in H;
              left; congruence.
          + intros q gs k d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H]; [left; congruence |].
            apply SOvd.mem_map in H; destruct H as [u [_ H]]; discriminate.
          + intros nm i0 gs k d H; apply SOed.singleton_in in H;
              injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FDep m ws); subst k;
              split; [lia | split; [reflexivity |]].
            apply SOed.singleton_in; subst d; reflexivity.
          + intros nm i0 gs k d H; simpl in H; apply SOed.add_in in H;
              destruct H as [H | H];
              [| apply SOvd.mem_map in H; destruct H as [u [_ H]];
                 discriminate].
            injection H as H1 H2 H3; left; split; [congruence |].
            exists 0, (FNeg (FDep m ws)); subst k;
              split; [lia | split; [reflexivity |]].
            simpl; apply SOed.add_in; left; subst d; reflexivity.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
          + intros nm i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FConj a b); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; left;
                exact H.
            * destruct (IHb1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FConj a b); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; right;
                exact H.
          + intros nm i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FNeg a); subst k;
                split; [lia | split; [reflexivity |]].
              exact H.
            * destruct (IHb4 _ _ _ _ _ H) as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              left; split; [exact Eq |]; exists (S j), g;
                split; [lia | split; [exact Hg | exact Hin]].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
          + intros nm i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, a; subst k; split; [lia | split; [reflexivity |]].
              exact H.
            * destruct (IHb3 _ _ _ _ _ H) as [[Eq [j [g [Hk [Hg Hin]]]]] | Hex];
                [| right; exact Hex].
              left; split; [exact Eq |]; exists (S j), g;
                split; [lia | split; [exact Hg | exact Hin]].
          + intros nm i0 gs k d H; simpl in H;
              apply T.DepRel.union_spec in H; destruct H as [H | H].
            * destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FNeg (FDisj a b)); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; left;
                exact H.
            * destruct (IHb2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
              injection Eq as Eq1 Eq2; subst nm; left;
                split; [reflexivity |].
              exists 0, (FNeg (FDisj a b)); subst k;
                split; [lia | split; [reflexivity |]].
              simpl; apply T.DepRel.union_spec; right;
                exact H.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros q gs k d H; exact (IHa2 _ _ _ _ H).
          + intros q gs k d H; exact (IHa1 _ _ _ _ H).
          + intros nm i0 gs k d H; simpl in H.
            destruct (IHa2 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
            injection Eq as Eq1 Eq2; subst nm; left;
              split; [reflexivity |].
            exists 0, (FNeg a); subst k;
              split; [lia | split; [reflexivity |]].
            exact H.
          + intros nm i0 gs k d H; simpl in H.
            destruct (IHa1 _ _ _ _ H) as [Eq | Hex]; [| right; exact Hex].
            injection Eq as Eq1 Eq2; subst nm; left;
              split; [reflexivity |].
            exists 0, (FNeg (FNeg a)); subst k;
              split; [lia | split; [reflexivity |]].
            exact H.
      Qed.

      Theorem dependees_lookupDisjunct : forall R D fs (i : Version.t),
          T.PkgSet.In (Name.Disjunct fs, i) (reduceReal R D) ->
          T.dependees (reduceDeps D) (Name.Disjunct fs, i) =
          match disjAlt fs i with
          | Some g =>
              T.dependees (encodeNNF (Name.Disjunct fs, i) g)
                (Name.Disjunct fs, i)
          | None => T.DependeesSet.empty
          end.
      Proof.
        intros R D fs i H; apply mem_reduceReal in H.
        destruct H as [[[pn pv] [_ Hq]] | [p [f [HD Hw]]]];
          [unfold embedPkg in Hq; discriminate Hq |].
        pose proof (proj1 (witnessSet_gadget_aux f) _ _ Hw) as Hgd.
        cbn [fst gadgetPkgs] in Hgd; apply mem_idxPkgs in Hgd.
        destruct Hgd as [k [Hk Hi]].
        assert (Hv : i = Version.Idx k) by congruence; subst i.
        cbn [disjAlt].
        destruct (List.nth_error fs k) as [g |] eqn:E;
          [| apply List.nth_error_None in E; lia].
        apply T.dependees_ext; intro h; rewrite mem_reduceDeps.
        split.
        - intros [q [f' [_ He]]].
          destruct (proj1 (encodeNNF_alt_aux f') _ _ _ _ He)
            as [Eq | [g' [Hg' Hin]]].
          + destruct q as [qn qv]; unfold embedPkg in Eq; simpl in Eq;
              discriminate.
          + rewrite E in Hg'; injection Hg' as <-; exact Hin.
        - intro Hin; exists p, f; split; [exact HD |].
          exact (proj1 (witnessSet_alt_aux f) _ _ _ _ _ Hw E Hin).
      Qed.

      Theorem versions_lookupNegDep : forall R D (n : N.t) (vs : VSet.t),
          (exists p h,
              T.DepRel.In (p, (Name.NegDep n vs, h)) (reduceDeps D)) ->
          T.versions (reduceReal R D) (Name.NegDep n vs) =
          T.VSet.add (Version.Idx 0) (T.VSet.singleton (Version.Idx 1)).
      Proof.
        intros R D n vs [p [h Hd]].
        apply mem_reduceDeps in Hd; destruct Hd as [r [g [HD He]]].
        pose proof (proj1 (encodeNNF_target_gadget_aux g) (embedPkg r)
                      (p, (Name.NegDep n vs, h)) He) as Hsub.
        cbn [fst snd] in Hsub.
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal, SOvv.add_in,
          SOvv.singleton_in.
        split.
        - intros [[[qn qv] [_ Hq]] | [r1 [g1 [_ Hw]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + pose proof (proj1 (witnessSet_gadget_aux g1) _ _ Hw) as Hg.
            cbn [fst gadgetPkgs] in Hg;
              rewrite SOpt.add_in, SOpt.singleton_in in Hg.
            destruct Hg as [Hg | Hg]; [left | right]; congruence.
        - intro Hw; right; exists r, g; split; [exact HD |].
          apply Hsub; cbn [gadgetPkgs];
            rewrite SOpt.add_in, SOpt.singleton_in.
          destruct Hw as [-> | ->]; [left | right]; reflexivity.
      Qed.

      Theorem dependees_lookupNegDep : forall R D n vs (i : Version.t),
          T.PkgSet.In (Name.NegDep n vs, i) (reduceReal R D) ->
          T.dependees (reduceDeps D) (Name.NegDep n vs, i) =
          T.DependeesSet.empty.
      Proof.
        intros R D n vs i _; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [f [_ He]]]; unfold encodeNNF in He.
        assert (E := proj1 (encodeNNF_src_negDep_aux f) _ _ _ _ _ He).
        unfold embedPkg in E; simpl in E; discriminate.
      Qed.

    End Lookup.
  End Reduction.
End PackageFormula.
