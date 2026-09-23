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
  | FDep (m : N.t) (vs : VSet.t)
  | FConj (f1 f2 : Formula)
  | FDisj (f1 f2 : Formula)
  | FNeg (f : Formula).

  Fixpoint Satisfies (S : PkgSet.t) (f : Formula) : Prop :=
    match f with
    | FDep m vs => exists v, VSet.In v vs /\ PkgSet.In (m, v) S
    | FConj f1 f2 => Satisfies S f1 /\ Satisfies S f2
    | FDisj f1 f2 => Satisfies S f1 \/ Satisfies S f2
    | FNeg f1 => ~ Satisfies S f1
    end.

  Fixpoint satisfiesb (S : PkgSet.t) (f : Formula) : bool :=
    match f with
    | FDep m vs => VSet.exists_ (fun v => PkgSet.mem (m, v) S) vs
    | FConj f1 f2 => andb (satisfiesb S f1) (satisfiesb S f2)
    | FDisj f1 f2 => orb (satisfiesb S f1) (satisfiesb S f2)
    | FNeg f1 => negb (satisfiesb S f1)
    end.

  Lemma satisfiesb_iff : forall S f, satisfiesb S f = true <-> Satisfies S f.
  Proof.
    intros S f; induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa];
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

    (* One disjunct package per disjunction, named by all of its
       alternatives: a chain of two-alternative disjuncts would introduce an
       inner name for every proper suffix of the same disjunction. *)
    Module Name.
      Inductive name : Type :=
      | Orig (m : N.t)
      | Disjunct (fs : list Formula).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, Disjunct _ => Lt
        | Disjunct _, Orig _ => Gt
        | Disjunct fs1, Disjunct fs2 => FListOT.compare fs1 fs2
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

    (* A synthetic version is the position of the alternative it selects, so
       a disjunction of any width is one node.  Bot is absence: every original
       name has it, and it is the greatest version so that a solver preferring
       the greatest leaves a name nobody needs positively out of the
       resolution. *)
    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Idx (i : nat)
      | Bot.
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, _ => Lt
        | Idx _, Orig _ => Gt
        | Idx i, Idx j => Nat.compare i j
        | Idx _, Bot => Lt
        | Bot, Bot => Eq
        | Bot, _ => Gt
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
    Module NSet := FSetUOT N.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(m, v) := p in (Name.Orig m, Version.Orig v).

    Module SOvv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map Version.Orig vs.

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

    Definition idxPkgs (n : Name.t) (k : nat) : T.PkgSet.t :=
      T.PkgSet.ofList (List.map (fun i => (n, Version.Idx i)) (List.seq 0 k)).

    (* The versions a negated atom admits at its name: every real version
       the atom does not name, and absence.  The encoder reads real versions
       through the oracle Vq, so a sub-instance agreeing there gives the same
       edges. *)
    Definition negVS (Vq : N.t -> VSet.t) (m : N.t) (vs : VSet.t) : T.VSet.t :=
      T.VSet.add Version.Bot (embedVS (VSet.diff (Vq m) vs)).

    (* A De Morgan case would recurse on a rewritten term, demanding
       well-founded recursion on a measure under which negation strictly
       decreases; fusing one unfolding step keeps this pair structural.
       The spine walkers carry the position of the alternative they are
       encoding, and repeat their sibling's non-spine cases for the same
       reason: calling the sibling on the matched term itself would leave
       the guard condition. *)
    Fixpoint encodeNNF (Vq : N.t -> VSet.t) (p : T.Pkg.t) (f : Formula)
      : T.DepRel.t :=
      match f with
      | FDep m vs =>
          T.DepRel.singleton (p, (Name.Orig m, embedVS vs))
      | FConj a b =>
          T.DepRel.union (encodeNNF Vq p a) (encodeNNF Vq p b)
      | FDisj a b =>
          let n := Name.Disjunct (a :: disjSpine b) in
          T.DepRel.add (p, (n, idxSet (List.length (a :: disjSpine b))))
            (T.DepRel.union (encodeNNF Vq (n, Version.Idx 0) a)
               (encodeDisj Vq n 1 b))
      | FNeg a => encodeNNFneg Vq p a
      end
    with encodeDisj (Vq : N.t -> VSet.t) (n : Name.t) (i : nat) (f : Formula)
      : T.DepRel.t :=
      match f with
      | FDep m vs =>
          T.DepRel.singleton ((n, Version.Idx i), (Name.Orig m, embedVS vs))
      | FConj a b =>
          T.DepRel.union (encodeNNF Vq (n, Version.Idx i) a)
            (encodeNNF Vq (n, Version.Idx i) b)
      | FDisj a b =>
          T.DepRel.union (encodeNNF Vq (n, Version.Idx i) a)
            (encodeDisj Vq n (S i) b)
      | FNeg a => encodeNNFneg Vq (n, Version.Idx i) a
      end
    with encodeNNFneg (Vq : N.t -> VSet.t) (p : T.Pkg.t) (f : Formula)
      : T.DepRel.t :=
      match f with
      | FDep m vs =>
          T.DepRel.singleton (p, (Name.Orig m, negVS Vq m vs))
      | FConj a b =>
          let n := Name.Disjunct (FNeg a :: negConjSpine b) in
          T.DepRel.add
            (p, (n, idxSet (List.length (FNeg a :: negConjSpine b))))
            (T.DepRel.union (encodeNNFneg Vq (n, Version.Idx 0) a)
               (encodeConjNeg Vq n 1 b))
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg Vq p a) (encodeNNFneg Vq p b)
      | FNeg a => encodeNNF Vq p a
      end
    with encodeConjNeg (Vq : N.t -> VSet.t) (n : Name.t) (i : nat)
        (f : Formula) : T.DepRel.t :=
      match f with
      | FDep m vs =>
          T.DepRel.singleton ((n, Version.Idx i), (Name.Orig m, negVS Vq m vs))
      | FConj a b =>
          T.DepRel.union (encodeNNFneg Vq (n, Version.Idx i) a)
            (encodeConjNeg Vq n (S i) b)
      | FDisj a b =>
          T.DepRel.union (encodeNNFneg Vq (n, Version.Idx i) a)
            (encodeNNFneg Vq (n, Version.Idx i) b)
      | FNeg a => encodeNNF Vq (n, Version.Idx i) a
      end.

    (* The synthetic packages a formula's encoding introduces: the disjunct
       packages, and nothing for a negated atom. *)
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
      end.

    (* The names a formula mentions. *)
    Fixpoint fnames (f : Formula) : NSet.t :=
      match f with
      | FDep m _ => NSet.singleton m
      | FConj a b => NSet.union (fnames a) (fnames b)
      | FDisj a b => NSet.union (fnames a) (fnames b)
      | FNeg a => fnames a
      end.

    Module SOen := SetOps DepElt N DepRel NSet.
    Definition depNames (D : DepRel.t) : NSet.t :=
      SOen.unionMap (fun '(_, f) => fnames f) D.

    (* Every name of the instance -- those with a version and those some
       formula mentions -- has the absent version. *)
    Module SOpn := SetOps Pkg N PkgSet NSet.
    Definition instNames (R : PkgSet.t) (D : DepRel.t) : NSet.t :=
      NSet.union (SOpn.map fst R) (depNames D).

    Module SOnt := SetOps N T.Pkg NSet T.PkgSet.
    Definition absentPkgs (ns : NSet.t) : T.PkgSet.t :=
      SOnt.map (fun n => (Name.Orig n, Version.Bot)) ns.

    Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Module SOet := SetOps DepElt T.Pkg DepRel T.PkgSet.
    Definition reduceReal (R : PkgSet.t) (D : DepRel.t) : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg R)
        (T.PkgSet.union
           (SOet.unionMap (fun '(p, f) => witnessSet (embedPkg p) f) D)
           (absentPkgs (instNames R D))).

    Module SOed := SetOps DepElt T.DepElt DepRel T.DepRel.
    Definition reduceDepsBy (Vq : N.t -> VSet.t) (D : DepRel.t) : T.DepRel.t :=
      SOed.unionMap (fun '(p, f) => encodeNNF Vq (embedPkg p) f) D.

    Definition reduceDeps (R : PkgSet.t) (D : DepRel.t) : T.DepRel.t :=
      reduceDepsBy (C.versions R) D.

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

    Lemma mem_negVS : forall Vq m vs (w : Version.t),
        T.VSet.In w (negVS Vq m vs) <->
        w = Version.Bot \/
        exists u, VSet.In u (Vq m) /\ ~ VSet.In u vs /\ w = Version.Orig u.
    Proof.
      intros Vq m vs w; unfold negVS.
      rewrite SOvv.add_in; unfold embedVS; rewrite SOvv.mem_map.
      split.
      - intros [-> | [u [Hu ->]]]; [left; reflexivity | right].
        apply VSet.diff_spec in Hu; destruct Hu as [Hu Hnv].
        exists u; auto.
      - intros [-> | [u [Hu [Hnv ->]]]]; [left; reflexivity | right].
        exists u; split; [| reflexivity].
        apply VSet.diff_spec; split; assumption.
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

    Lemma mem_reduceReal : forall R D (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal R D) <->
        (exists p, PkgSet.In p R /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\
                     T.PkgSet.In y (witnessSet (embedPkg p) f)) \/
        (exists n, NSet.In n (instNames R D) /\ y = (Name.Orig n, Version.Bot)).
    Proof.
      intros R D y; unfold reduceReal.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap,
        mem_absentPkgs.
      split.
      - intros [H | [[[q g] [He Hy]] | H]]; [left; exact H | | right; right; exact H].
        right; left; exists q, g; split; [exact He | exact Hy].
      - intros [H | [[q [g [Hd Hy]]] | H]]; [left; exact H | | right; right; exact H].
        right; left; exists (q, g); split; [exact Hd | exact Hy].
    Qed.

    Lemma mem_reduceDepsBy : forall Vq D (d : T.DepElt.t),
        T.DepRel.In d (reduceDepsBy Vq D) <->
        exists p f, DepRel.In (p, f) D /\
                    T.DepRel.In d (encodeNNF Vq (embedPkg p) f).
    Proof.
      intros Vq D d; unfold reduceDepsBy; rewrite SOed.mem_unionMap.
      split.
      - intros [[q g] [He Hd]]; exists q, g; split; [exact He | exact Hd].
      - intros [q [g [Hq Hd]]]; exists (q, g); split; [exact Hq | exact Hd].
    Qed.

    Lemma mem_reduceDeps : forall R D (d : T.DepElt.t),
        T.DepRel.In d (reduceDeps R D) <->
        exists p f, DepRel.In (p, f) D /\
                    T.DepRel.In d (encodeNNF (C.versions R) (embedPkg p) f).
    Proof. intros R D d; apply mem_reduceDepsBy. Qed.

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
    Definition packageFormulaResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_packageFormulaResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (packageFormulaResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold packageFormulaResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

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
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
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
    Qed.

    Lemma witnessSet_not_orig : forall (p : T.Pkg.t) (f : Formula) m v,
        ~ T.PkgSet.In (Name.Orig m, v) (witnessSet p f).
    Proof.
      intros p f m v H.
      destruct (proj1 (witnessSet_name_classify_aux f) _ _ _ H) as [fs E];
        discriminate.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall (p : Pkg.t) R D,
        T.PkgSet.In (embedPkg p) (reduceReal R D) -> PkgSet.In p R.
    Proof.
      intros [pn pv] R D H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [[q [g [_ Hy]]] | [n [_ Hy]]]].
      - apply embedPkg_injective in Hq as ->; exact HqR.
      - exfalso; exact (witnessSet_not_orig _ _ _ _ Hy).
      - discriminate Hy.
    Qed.

    Lemma encodeNNF_satisfies : forall (R : T.PkgSet.t) (D : T.DepRel.t)
                                    (r : T.Pkg.t) (S : T.PkgSet.t),
        T.IsResolution R D r S ->
        forall (Vq : N.t -> VSet.t) (q : T.Pkg.t) (f : Formula),
          (forall d, T.DepRel.In d (encodeNNF Vq q f) -> T.DepRel.In d D) ->
          T.PkgSet.In q S ->
          Satisfies (packageFormulaResolution S) f.
    Proof.
      intros R D r S Hres Vq; destruct Hres as [Hsub Hroot Hdep Huniq].
      cut (forall f : Formula,
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNF Vq q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S -> Satisfies (packageFormulaResolution S) f) /\
        (forall q : T.Pkg.t,
            (forall d, T.DepRel.In d (encodeNNFneg Vq q f) -> T.DepRel.In d D) ->
            T.PkgSet.In q S -> ~ Satisfies (packageFormulaResolution S) f) /\
        (forall (n : Name.t) (i0 i : nat),
            (forall d, T.DepRel.In d (encodeDisj Vq n i0 f) -> T.DepRel.In d D) ->
            T.PkgSet.In (n, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (disjSpine f) ->
            Satisfies (packageFormulaResolution S) f) /\
        (forall (n : Name.t) (i0 i : nat),
            (forall d,
                T.DepRel.In d (encodeConjNeg Vq n i0 f) -> T.DepRel.In d D) ->
            T.PkgSet.In (n, Version.Idx i) S ->
            i0 <= i -> i < i0 + List.length (negConjSpine f) ->
            ~ Satisfies (packageFormulaResolution S) f)).
      { intros H q f; exact (proj1 (H f) q). }
      (* the FDep dependency edge, read back through the resolution *)
      assert (Hpos : forall (q : T.Pkg.t) m vs,
                 T.DepRel.In (q, (Name.Orig m, embedVS vs)) D ->
                 T.PkgSet.In q S ->
                 Satisfies (packageFormulaResolution S) (FDep m vs)).
      { intros q m vs Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        unfold embedVS in Hw; apply SOvv.mem_map in Hw;
          destruct Hw as [v [Hv ->]].
        exists v; split; [exact Hv |].
        apply mem_packageFormulaResolution; exact HwS. }
      (* the negated atom's edge: closure picks a version the atom does not
         name, or absence, and version uniqueness leaves room for no other *)
      assert (Hneg : forall (q : T.Pkg.t) m vs,
                 T.DepRel.In (q, (Name.Orig m, negVS Vq m vs)) D ->
                 T.PkgSet.In q S ->
                 ~ Satisfies (packageFormulaResolution S) (FDep m vs)).
      { intros q m vs Hd HqS.
        destruct (Hdep q HqS _ _ Hd) as [w [Hw HwS]].
        intros [v [Hv HvS]].
        apply mem_packageFormulaResolution in HvS.
        assert (E := Huniq _ _ _ HwS HvS); subst w.
        apply mem_negVS in Hw.
        destruct Hw as [Hw | [u [_ [Hnv E]]]]; [discriminate Hw |].
        injection E as <-; exact (Hnv Hv). }
      induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa].
      - split4.
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
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
          * refine (IHb4 n 1 (Datatypes.S i') _ HwS _ _ HsatB); [| lia | simpl; lia].
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
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne].
          * refine (IHa2 (n, Version.Idx i0) _ HiS HsatA).
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; left; exact Hd.
          * refine (IHb4 n (Datatypes.S i0) i _ HiS _ _ HsatB); [| lia | lia].
            intros d Hd; apply Henc; simpl;
              apply T.DepRel.union_spec; right; exact Hd.
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
          * right; refine (IHb3 n 1 (Datatypes.S i') _ HwS _ _); [| lia | simpl; lia].
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
          destruct (Nat_as_OT.eq_dec i i0) as [-> | Hne].
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
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros q Henc HqS; exact (IHa2 q Henc HqS).
        + intros q Henc HqS; simpl; intro Hn; exact (Hn (IHa1 q Henc HqS)).
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia.
          exact (IHa2 (n, Version.Idx i0) Henc HiS).
        + intros n i0 i Henc HiS Hle Hlt; simpl in Hlt.
          assert (i = i0) as -> by lia; simpl; intro Hn.
          exact (Hn (IHa1 (n, Version.Idx i0) Henc HiS)).
    Qed.

    Theorem package_formula_soundness :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D) (reduceDeps R D) (embedPkg r) S ->
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
        apply (encodeNNF_satisfies _ _ _ _ Hres (C.versions R) (embedPkg p) f);
          [| exact Hp].
        intros d Hd; apply mem_reduceDeps;
          exists p, f; split; [exact Hdf | exact Hd].
      - intros m v v' Hv Hv'.
        apply mem_packageFormulaResolution in Hv, Hv'.
        unfold embedPkg in Hv, Hv'; simpl in Hv, Hv'.
        assert (E := Huniq _ _ _ Hv Hv').
        injection E as E; exact E.
    Qed.

    (* The alternative a disjunct package takes: the first satisfied one,
       and the last one when none is -- which is what the two-alternative
       chain this replaces settled on, and keeps the index inside idxSet. *)
    Fixpoint firstSatIdx (Sv : PkgSet.t) (fs : list Formula) : nat :=
      match fs with
      | nil => 0
      | _ :: nil => 0
      | g :: fs' =>
          if satisfiesb Sv g then 0 else Datatypes.S (firstSatIdx Sv fs')
      end.

    (* The synthetic packages a selected package's satisfied formula puts in
       the resolution: each disjunct at the alternative it takes, and that
       alternative's own witnesses.  A negated atom contributes nothing; its
       edge is met by the target's version, or by absence. *)
    Fixpoint witnessSetTaken (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetTaken S a) (witnessSetTaken S b)
      | FDisj a b =>
          T.PkgSet.add
            (Name.Disjunct (a :: disjSpine b),
             Version.Idx (firstSatIdx S (a :: disjSpine b)))
            (if satisfiesb S a then witnessSetTaken S a else takenDisj S b)
      | FNeg a => witnessSetTakenNeg S a
      end
    with takenDisj (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.union (witnessSetTaken S a) (witnessSetTaken S b)
      | FDisj a b =>
          if satisfiesb S a then witnessSetTaken S a else takenDisj S b
      | FNeg a => witnessSetTakenNeg S a
      end
    with witnessSetTakenNeg (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          T.PkgSet.add
            (Name.Disjunct (FNeg a :: negConjSpine b),
             Version.Idx (firstSatIdx S (FNeg a :: negConjSpine b)))
            (if satisfiesb S a then takenConjNeg S b
             else witnessSetTakenNeg S a)
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S a) (witnessSetTakenNeg S b)
      | FNeg a => witnessSetTaken S a
      end
    with takenConjNeg (S : PkgSet.t) (f : Formula) : T.PkgSet.t :=
      match f with
      | FDep _ _ => T.PkgSet.empty
      | FConj a b =>
          if satisfiesb S a then takenConjNeg S b else witnessSetTakenNeg S a
      | FDisj a b =>
          T.PkgSet.union (witnessSetTakenNeg S a) (witnessSetTakenNeg S b)
      | FNeg a => witnessSetTaken S a
      end.

    (* The walkers and their hosts agree everywhere but the spine, so the
       host's own case is the walker's plus the synthetic version it takes. *)
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
        (if satisfiesb S a then witnessSetTaken S a else takenDisj S b).
    Proof. reflexivity. Qed.

    Lemma takenConjNeg_conj_eq : forall S a b,
        takenConjNeg S (FConj a b) =
        (if satisfiesb S a then takenConjNeg S b else witnessSetTakenNeg S a).
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

    (* Which alternative a disjunct package's taken version stands for: the
       witness of that alternative is the one the walker actually laid
       down. *)
    Lemma takenDisj_firstSat : forall S f,
        Satisfies S f ->
        exists g,
          List.nth_error (disjSpine f) (firstSatIdx S (disjSpine f)) = Some g /\
          Satisfies S g /\
          T.PkgSet.Subset (witnessSetTaken S g) (takenDisj S f).
    Proof.
      intros S f; induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa];
        intro Hsat;
        try (eexists; split; [reflexivity |]; split;
             [exact Hsat | intros y Hy; exact Hy]).
      cbn [disjSpine];
        rewrite (firstSatIdx_cons S a (disjSpine b) (disjSpine_nonnil b)).
      destruct (satisfiesb S a) eqn:Ea.
      - exists a; split; [reflexivity |]; split;
          [apply satisfiesb_iff; exact Ea |].
        intros y Hy; simpl; rewrite Ea; exact Hy.
      - assert (Hb : Satisfies S b).
        { destruct Hsat as [Ha | Hb]; [| exact Hb].
          exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
        destruct (IHb Hb) as [g [Hg [Hsg Hsub]]].
        exists g; split; [exact Hg |]; split; [exact Hsg |].
        intros y Hy; simpl; rewrite Ea; exact (Hsub y Hy).
    Qed.

    Lemma takenConjNeg_firstSat : forall S f,
        ~ Satisfies S f ->
        exists g,
          List.nth_error (negConjSpine f) (firstSatIdx S (negConjSpine f)) =
            Some g /\
          Satisfies S g /\
          T.PkgSet.Subset (witnessSetTaken S g) (takenConjNeg S f).
    Proof.
      intros S f; induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa];
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
        intros y Hy; simpl; rewrite Ea; exact (Hsub y Hy).
      - exists (FNeg a); split;
          [change (satisfiesb S (FNeg a)) with (negb (satisfiesb S a));
           rewrite Ea; reflexivity |]; split;
          [apply satisfiesb_false_iff; exact Ea |].
        intros y Hy; simpl; rewrite Ea; exact Hy.
    Qed.

    (* Whether a name has a version in S; the names that do not carry
       absence in the completeness construction. *)
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
        assert (Ht : hasNameb S n = true) by (apply hasNameb_true; exists v; exact Hv).
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

    Definition coreResolution (S : PkgSet.t) (R : PkgSet.t) (D : DepRel.t)
      : T.PkgSet.t :=
      T.PkgSet.union (SOpt.map embedPkg S)
        (T.PkgSet.union
           (SOet.unionMap (fun '(p, f) =>
                if PkgSet.mem p S then witnessSetTaken S f else T.PkgSet.empty)
              D)
           (absentPkgs (absentIn S (instNames R D)))).

    Lemma witnessSetTaken_subset_witnessSet_aux : forall S f,
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTaken S f) (witnessSet p f)) /\
        (forall p : T.Pkg.t,
            T.PkgSet.Subset (witnessSetTakenNeg S f) (witnessSetNeg p f)) /\
        (forall (n : Name.t) (i : nat),
            T.PkgSet.Subset (takenDisj S f) (witnessDisj n i f)) /\
        (forall (n : Name.t) (i : nat),
            T.PkgSet.Subset (takenConjNeg S f) (witnessConjNeg n i f)).
    Proof.
      intros S f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
      - split4; intros; intros y H; exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 p _ H) | right; exact (IHb1 p _ H)].
        + intros p y; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; simpl witnessSetNeg;
            apply T.PkgSet.union_spec.
          destruct H as [-> | H].
          * left; apply mem_idxPkgs;
              exists (firstSatIdx S (FNeg a :: negConjSpine b));
              split; [apply firstSatIdx_lt; discriminate | reflexivity].
          * right; revert H; rewrite takenConjNeg_conj_eq;
              destruct (satisfiesb S a); intro H;
              apply T.PkgSet.union_spec;
              [right; exact (IHb4 _ _ _ H) | left; exact (IHa2 _ _ H)].
        + intros n i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa1 _ _ H) | right; exact (IHb1 _ _ H)].
        + intros n i y; rewrite takenConjNeg_conj_eq; simpl witnessConjNeg;
            destruct (satisfiesb S a); intro H;
            apply T.PkgSet.union_spec;
            [right; exact (IHb4 _ _ _ H) | left; exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros p y; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; simpl witnessSet;
            apply T.PkgSet.union_spec.
          destruct H as [-> | H].
          * left; apply mem_idxPkgs;
              exists (firstSatIdx S (a :: disjSpine b));
              split; [apply firstSatIdx_lt; discriminate | reflexivity].
          * right; revert H; rewrite takenDisj_disj_eq;
              destruct (satisfiesb S a); intro H;
              apply T.PkgSet.union_spec;
              [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros p y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 p _ H) | right; exact (IHb2 p _ H)].
        + intros n i y; rewrite takenDisj_disj_eq; simpl witnessDisj;
            destruct (satisfiesb S a); intro H;
            apply T.PkgSet.union_spec;
            [left; exact (IHa1 _ _ H) | right; exact (IHb3 _ _ _ H)].
        + intros n i y; simpl; intro H;
            apply T.PkgSet.union_spec in H; apply T.PkgSet.union_spec;
            destruct H as [H | H];
            [left; exact (IHa2 _ _ H) | right; exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros p y; exact (IHa2 p y).
        + intros p y; exact (IHa1 p y).
        + intros n i y; exact (IHa2 _ y).
        + intros n i y; exact (IHa1 _ y).
    Qed.

    Lemma witnessSetTaken_subset_witnessSet : forall S (p : T.Pkg.t) f,
        T.PkgSet.Subset (witnessSetTaken S f) (witnessSet p f).
    Proof.
      intros S p f;
        exact (proj1 (witnessSetTaken_subset_witnessSet_aux S f) p).
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
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros fs v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; rewrite takenConjNeg_conj_eq; destruct (satisfiesb S a);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros fs v; rewrite takenConjNeg_conj_eq; destruct (satisfiesb S a);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros fs v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> ->; reflexivity |].
          revert H; rewrite takenDisj_disj_eq; destruct (satisfiesb S a);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros fs v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros fs v; rewrite takenDisj_disj_eq; destruct (satisfiesb S a);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
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

    Lemma witnessSetTaken_name_classify_aux : forall S f,
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTaken S f) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (witnessSetTakenNeg S f) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (takenDisj S f) -> SyntheticName n) /\
        (forall (n : Name.t) (v : Version.t),
            T.PkgSet.In (n, v) (takenConjNeg S f) -> SyntheticName n).
    Proof.
      unfold SyntheticName; intros S f;
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
      - split4; intros n v; simpl; intro H;
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; rewrite witnessSetTakenNeg_conj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; eauto |].
          revert H; rewrite takenConjNeg_conj_eq; destruct (satisfiesb S a);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa1 _ _ H) | exact (IHb1 _ _ H)].
        + intros n v; rewrite takenConjNeg_conj_eq; destruct (satisfiesb S a);
            intro H; [exact (IHb4 _ _ H) | exact (IHa2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros n v; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H];
            [injection H as -> _; eauto |].
          revert H; rewrite takenDisj_disj_eq; destruct (satisfiesb S a);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
        + intros n v; rewrite takenDisj_disj_eq; destruct (satisfiesb S a);
            intro H; [exact (IHa1 _ _ H) | exact (IHb3 _ _ H)].
        + intros n v; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [exact (IHa2 _ _ H) | exact (IHb2 _ _ H)].
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4; intros n v;
          [exact (IHa2 n v) | exact (IHa1 n v)
          | exact (IHa2 n v) | exact (IHa1 n v)].
    Qed.

    Lemma witnessSetTaken_not_orig : forall S f m v,
        ~ T.PkgSet.In (Name.Orig m, v) (witnessSetTaken S f).
    Proof.
      intros S f m v H.
      destruct (proj1 (witnessSetTaken_name_classify_aux S f) _ _ H) as [fs E];
        discriminate.
    Qed.

    Lemma mem_coreResolution : forall S R D (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution S R D) <->
        (exists p, PkgSet.In p S /\ y = embedPkg p) \/
        (exists p f, DepRel.In (p, f) D /\ PkgSet.In p S /\
                     T.PkgSet.In y (witnessSetTaken S f)) \/
        (exists n, NSet.In n (instNames R D) /\
                   (forall v, ~ PkgSet.In (n, v) S) /\
                   y = (Name.Orig n, Version.Bot)).
    Proof.
      intros S R D y; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, SOpt.mem_map, SOet.mem_unionMap,
        mem_absentPkgs.
      split.
      - intros [H | [[[q g] [He Hy]] | [n [Hn ->]]]]; [left; exact H | |].
        + right; left; cbn beta iota in Hy.
          destruct (PkgSet.mem q S) eqn:E;
            [| exfalso; exact (SOpt.empty_in _ Hy)].
          exists q, g; split; [exact He |];
            split; [apply PkgSet.mem_spec; exact E | exact Hy].
        + right; right; apply mem_absentIn in Hn; destruct Hn as [Hn Hnone].
          exists n; auto.
      - intros [H | [[q [g [Hd [HqS Hy]]]] | [n [Hn [Hnone ->]]]]];
          [left; exact H | |].
        + right; left; exists (q, g); split; [exact Hd |].
          apply PkgSet.mem_spec in HqS; cbn beta iota; rewrite HqS; exact Hy.
        + right; right; exists n; split; [| reflexivity].
          apply mem_absentIn; auto.
    Qed.

    Lemma witnessSetTaken_subset_coreResolution : forall S R D p f,
        DepRel.In (p, f) D -> PkgSet.In p S ->
        T.PkgSet.Subset (witnessSetTaken S f) (coreResolution S R D).
    Proof.
      intros S R D p f Hd HpS y Hy; apply mem_coreResolution; right; left.
      exists p, f; auto.
    Qed.

    (* Passing an alternative up through one set constructor: nav is the
       step from the inner witness set to the outer one, which is all that
       differs between the places this conclusion is rebuilt. *)
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
          exfalso; exact (SOpt.empty_in _ H).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
              destruct (satisfiesb S a) eqn:Ea; intro H.
            -- assert (Hb : ~ Satisfies S b).
               { intro Hb; apply Hyp; split;
                   [apply satisfiesb_iff; exact Ea | exact Hb]. }
               pick_alt (IHb4 Hb _ _ H) ltac:(apply SOpt.add_in; right).
            -- pick_alt (IHa2 (proj1 (satisfiesb_false_iff S a) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H];
            [pick_alt (IHa1 (proj1 Hyp) _ _ H)
               ltac:(apply T.PkgSet.union_spec; left)
            | pick_alt (IHb1 (proj2 Hyp) _ _ H)
                ltac:(apply T.PkgSet.union_spec; right)].
        + intros Hyp fs i; rewrite takenConjNeg_conj_eq;
            destruct (satisfiesb S a) eqn:Ea; intro H.
          * assert (Hb : ~ Satisfies S b).
            { intro Hb; apply Hyp; split;
                [apply satisfiesb_iff; exact Ea | exact Hb]. }
            pick_alt (IHb4 Hb _ _ H) ltac:(idtac).
          * pick_alt (IHa2 (proj1 (satisfiesb_false_iff S a) Ea) _ _ H)
              ltac:(idtac).
      - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros Hyp fs i; rewrite witnessSetTaken_disj_eq; intro H;
            apply SOpt.add_in in H; destruct H as [H | H].
          * injection H as -> ->;
              pick_alt (takenDisj_firstSat S (FDisj a b) Hyp)
                ltac:(apply SOpt.add_in; right).
          * revert H; rewrite takenDisj_disj_eq;
              destruct (satisfiesb S a) eqn:Ea; intro H.
            -- pick_alt (IHa1 (proj1 (satisfiesb_iff S a) Ea) _ _ H)
                 ltac:(apply SOpt.add_in; right).
            -- assert (Hb : Satisfies S b).
               { destruct Hyp as [Ha | Hb]; [| exact Hb].
                 exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
               pick_alt (IHb3 Hb _ _ H) ltac:(apply SOpt.add_in; right).
        + intros Hyp fs i; simpl; intro H;
            apply T.PkgSet.union_spec in H; destruct H as [H | H].
          * pick_alt (IHa2 (fun Ha => Hyp (or_introl Ha)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; left).
          * pick_alt (IHb2 (fun Hb => Hyp (or_intror Hb)) _ _ H)
              ltac:(apply T.PkgSet.union_spec; right).
        + intros Hyp fs i; rewrite takenDisj_disj_eq;
            destruct (satisfiesb S a) eqn:Ea; intro H.
          * pick_alt (IHa1 (proj1 (satisfiesb_iff S a) Ea) _ _ H) ltac:(idtac).
          * assert (Hb : Satisfies S b).
            { destruct Hyp as [Ha | Hb]; [| exact Hb].
              exfalso; exact (proj1 (satisfiesb_false_iff S a) Ea Ha). }
            pick_alt (IHb3 Hb _ _ H) ltac:(idtac).
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

    Lemma coreResolution_disj : forall S R D fs i,
        (forall p, PkgSet.In p S ->
         forall f, DepRel.In (p, f) D -> Satisfies S f) ->
        T.PkgSet.In (Name.Disjunct fs, Version.Idx i) (coreResolution S R D) ->
        exists g, List.nth_error fs i = Some g /\ Satisfies S g /\
          T.PkgSet.Subset (witnessSetTaken S g) (coreResolution S R D).
    Proof.
      intros S R D fs i Hclo H; apply mem_coreResolution in H.
      destruct H as [[p [_ Hp]] | [[p [g [Hd [HpS Hw]]]] | [n [_ [_ Hn]]]]].
      - destruct p as [pn pv]; unfold embedPkg in Hp; discriminate.
      - assert (Hsat : Satisfies S g) by exact (Hclo p HpS g Hd).
        destruct (proj1 (witnessSetTaken_disj_mono_aux S g) Hsat fs i Hw)
          as [h [Hh [Hsh Hsubh]]].
        exists h; split; [exact Hh |]; split; [exact Hsh |].
        intros y Hy;
          apply (witnessSetTaken_subset_coreResolution S R D p g Hd HpS), Hsubh;
          exact Hy.
      - discriminate Hn.
    Qed.

    (* Dependency closure over one formula's encoding.  Every source is
       either the owner q0 (then the formula holds and its taken witness is
       in w) or a disjunct node already in w, whose alternative Hdisj says
       holds; a negated atom's edge is met by the version its target has in
       S, or by absence when it has none. *)
    Lemma encodeNNF_dep_closure_aux :
      forall (S : PkgSet.t) (Vq : N.t -> VSet.t) (Ns : NSet.t) (w : T.PkgSet.t),
        (forall p, PkgSet.In p S -> T.PkgSet.In (embedPkg p) w) ->
        (forall m u, PkgSet.In (m, u) S -> VSet.In u (Vq m)) ->
        (forall m, NSet.In m Ns -> (forall u, ~ PkgSet.In (m, u) S) ->
           T.PkgSet.In (Name.Orig m, Version.Bot) w) ->
        (forall fs i, T.PkgSet.In (Name.Disjunct fs, Version.Idx i) w ->
           exists g, List.nth_error fs i = Some g /\ Satisfies S g /\
             T.PkgSet.Subset (witnessSetTaken S g) w) ->
        forall f : Formula,
          NSet.Subset (fnames f) Ns ->
          (forall q0 : T.Pkg.t,
              ~ T.PkgSet.In q0 w \/
              (Satisfies S f /\ T.PkgSet.Subset (witnessSetTaken S f) w) ->
              forall (q : T.Pkg.t) (o : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (o, ws)) (encodeNNF Vq q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (o, v) w) /\
          (forall q0 : T.Pkg.t,
              ~ T.PkgSet.In q0 w \/
              (~ Satisfies S f /\
               T.PkgSet.Subset (witnessSetTakenNeg S f) w) ->
              forall (q : T.Pkg.t) (o : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (o, ws)) (encodeNNFneg Vq q0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (o, v) w) /\
          (forall (n : Name.t) (i0 : nat),
              (forall k g, List.nth_error (disjSpine f) k = Some g ->
                 ~ T.PkgSet.In (n, Version.Idx (i0 + k)) w \/
                 (Satisfies S g /\
                  T.PkgSet.Subset (witnessSetTaken S g) w)) ->
              forall (q : T.Pkg.t) (o : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (o, ws)) (encodeDisj Vq n i0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (o, v) w) /\
          (forall (n : Name.t) (i0 : nat),
              (forall k g, List.nth_error (negConjSpine f) k = Some g ->
                 ~ T.PkgSet.In (n, Version.Idx (i0 + k)) w \/
                 (Satisfies S g /\
                  T.PkgSet.Subset (witnessSetTaken S g) w)) ->
              forall (q : T.Pkg.t) (o : NameOT.t) (ws : T.VSet.t),
                T.DepRel.In (q, (o, ws)) (encodeConjNeg Vq n i0 f) ->
                T.PkgSet.In q w ->
                exists v, T.VSet.In v ws /\ T.PkgSet.In (o, v) w).
    Proof.
      intros S Vq Ns w Hemb HVq Hbot Hdisj f.
      (* the negated atom's edge, from any source in w *)
      assert (Hneg : forall m vs,
                 NSet.In m Ns ->
                 ~ Satisfies S (FDep m vs) ->
                 exists v, T.VSet.In v (negVS Vq m vs) /\
                           T.PkgSet.In (Name.Orig m, v) w).
      { intros m vs Hm Hns.
        destruct (hasNameb S m) eqn:E.
        - apply hasNameb_true in E; destruct E as [u Hu].
          exists (Version.Orig u); split; [| exact (Hemb (m, u) Hu)].
          apply mem_negVS; right; exists u.
          split; [exact (HVq m u Hu) | split; [| reflexivity]].
          intro Huv; apply Hns; exists u; auto.
        - assert (Hnone := proj1 (hasNameb_false S m) E).
          exists Version.Bot; split; [apply mem_negVS; left; reflexivity |].
          exact (Hbot m Hm Hnone). }
      induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa]; intro Hsub.
      - assert (Hm : NSet.In m Ns)
          by (apply Hsub; simpl; apply NSet.singleton_spec; reflexivity).
        split4.
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
          by (intros x Hx; apply Hsub; simpl; apply NSet.union_spec; left; exact Hx).
        assert (Hsb : NSet.Subset (fnames b) Ns)
          by (intros x Hx; apply Hsub; simpl; apply NSet.union_spec; right; exact Hx).
        destruct (IHa Hsa) as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct (IHb Hsb) as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros q0 Hwit q o ws Henc Hqw.
          apply T.DepRel.union_spec in Henc; destruct Henc as [He | He].
          * refine (IHa1 q0 _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj1 Hsat) |]];
              intros y Hy; apply Hsub', T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb1 q0 _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj2 Hsat) |]];
              intros y Hy; apply Hsub', T.PkgSet.union_spec; right; exact Hy.
        + intros q0 Hwit q o ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [Hq0 | [_ Hsub']]; [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx
                      (firstSatIdx S (FNeg a :: negConjSpine b))); split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S (FNeg a :: negConjSpine b)); split;
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
              intros y Hy; apply Hsub', T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb1 (n, Version.Idx i0) _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hsat Hsub']];
              [left; exact Hq0 | right; split; [exact (proj2 Hsat) |]];
              intros y Hy; apply Hsub', T.PkgSet.union_spec; right; exact Hy.
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
          by (intros x Hx; apply Hsub; simpl; apply NSet.union_spec; left; exact Hx).
        assert (Hsb : NSet.Subset (fnames b) Ns)
          by (intros x Hx; apply Hsub; simpl; apply NSet.union_spec; right; exact Hx).
        destruct (IHa Hsa) as (IHa1 & IHa2 & IHa3 & IHa4);
          destruct (IHb Hsb) as (IHb1 & IHb2 & IHb3 & IHb4); split4.
        + intros q0 Hwit q o ws Henc Hqw.
          apply SOed.add_in in Henc; destruct Henc as [He | He].
          * injection He as -> -> ->.
            destruct Hwit as [Hq0 | [_ Hsub']]; [exfalso; exact (Hq0 Hqw) |].
            exists (Version.Idx (firstSatIdx S (a :: disjSpine b))); split.
            -- apply mem_idxSet;
                 exists (firstSatIdx S (a :: disjSpine b)); split;
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
              intros y Hy; apply Hsub', T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb2 q0 _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros y Hy; apply Hsub', T.PkgSet.union_spec; right; exact Hy.
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
              intros y Hy; apply Hsub', T.PkgSet.union_spec; left; exact Hy.
          * refine (IHb2 (n, Version.Idx i0) _ q o ws He Hqw).
            destruct Hwit as [Hq0 | [Hns Hsub']];
              [left; exact Hq0
              | right; split; [intro Hb; exact (Hns (or_intror Hb)) |]];
              intros y Hy; apply Hsub', T.PkgSet.union_spec; right; exact Hy.
      - destruct (IHa Hsub) as (IHa1 & IHa2 & IHa3 & IHa4); split4.
        + intros q0 Hwit q o ws Henc Hqw.
          exact (IHa2 q0 Hwit q o ws Henc Hqw).
        + intros q0 Hwit q o ws Henc Hqw.
          destruct Hwit as [Hq0 | [Hnn Hsub']];
            [exact (IHa1 q0 (or_introl Hq0) q o ws Henc Hqw)
            | exact (IHa1 q0
                       (or_intror (conj (satisfies_double_neg S a Hnn) Hsub'))
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
                       (or_intror (conj (satisfies_double_neg S a Hnn) Hsub'))
                       q o ws Henc Hqw)].
    Qed.

    Theorem package_formula_completeness :
      forall (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t),
        IsResolution R D r S ->
        T.IsResolution (reduceReal R D) (reduceDeps R D) (embedPkg r)
          (coreResolution S R D).
    Proof.
      intros R D r S Hres; destruct Hres as [Hsub Hroot Hclo Huniq].
      assert (Hemb : forall p, PkgSet.In p S ->
          T.PkgSet.In (embedPkg p) (coreResolution S R D)).
      { intros p Hp; apply mem_coreResolution; left.
        exists p; split; [exact Hp | reflexivity]. }
      assert (HVq : forall m u, PkgSet.In (m, u) S ->
          VSet.In u (C.versions R m)).
      { intros m u Hu; apply C.mem_versions; apply Hsub; exact Hu. }
      assert (Hbot : forall m, NSet.In m (instNames R D) ->
          (forall u, ~ PkgSet.In (m, u) S) ->
          T.PkgSet.In (Name.Orig m, Version.Bot) (coreResolution S R D)).
      { intros m Hm Hnone; apply mem_coreResolution; right; right.
        exists m; auto. }
      assert (Horig : forall m v,
          T.PkgSet.In (Name.Orig m, Version.Orig v) (coreResolution S R D) ->
          PkgSet.In (m, v) S).
      { intros m v Hv; apply mem_coreResolution in Hv.
        destruct Hv as [[[pn pv] [Hp Hpe]] | [[p [g [_ [_ Hw]]]] | [n [_ [_ Hn]]]]].
        - unfold embedPkg in Hpe; injection Hpe as -> ->; exact Hp.
        - exfalso; exact (witnessSetTaken_not_orig _ _ _ _ Hw).
        - discriminate Hn. }
      assert (Hdisj := fun fs i => coreResolution_disj S R D fs i Hclo).
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy.
        apply mem_reduceReal.
        destruct Hy as [[p [Hp ->]] | [[p [g [Hd [_ Hw]]]] | [n [Hn [_ ->]]]]].
        + left; exists p; split; [apply Hsub; exact Hp | reflexivity].
        + right; left; exists p, g; split; [exact Hd |].
          exact (witnessSetTaken_subset_witnessSet S (embedPkg p) g _ Hw).
        + right; right; exists n; auto.
      - exact (Hemb r Hroot).
      - intros q Hq m vs Hd.
        apply mem_reduceDeps in Hd; destruct Hd as [p [g [Hpg Henc]]].
        assert (Hfn : NSet.Subset (fnames g) (instNames R D)).
        { intros x Hx; apply mem_instNames; right; apply mem_depNames.
          exists p, g; auto. }
        refine (proj1 (encodeNNF_dep_closure_aux S (C.versions R) (instNames R D)
                         _ Hemb HVq Hbot Hdisj g Hfn)
                  (embedPkg p) _ q m vs Henc Hq).
        destruct (PkgSet.mem p S) eqn:Ep.
        + apply PkgSet.mem_spec in Ep.
          right; split; [exact (Hclo p Ep g Hpg) |].
          exact (witnessSetTaken_subset_coreResolution S R D p g Hpg Ep).
        + left; intro Hin; destruct p as [pn pv].
          apply Horig, PkgSet.mem_spec in Hin; congruence.
      - intros n v v' Hv Hv'.
        apply mem_coreResolution in Hv, Hv'.
        destruct Hv as [[[n1 w1] [Hp1 He1]] | [[p1 [g1 [Hd1 [Hp1 Hw1]]]]
                       | [m1 [_ [Hn1 He1]]]]];
          destruct Hv' as [[[n2 w2] [Hp2 He2]] | [[p2 [g2 [Hd2 [Hp2 Hw2]]]]
                          | [m2 [_ [Hn2 He2]]]]];
          unfold embedPkg in *.
        + injection He1 as -> ->; injection He2 as -> ->.
          f_equal; exact (Huniq _ _ _ Hp1 Hp2).
        + injection He1 as -> ->.
          exfalso; exact (witnessSetTaken_not_orig _ _ _ _ Hw2).
        + injection He1 as -> ->; injection He2 as -> ->.
          exfalso; exact (Hn2 _ Hp1).
        + injection He2 as -> ->.
          exfalso; exact (witnessSetTaken_not_orig _ _ _ _ Hw1).
        + destruct n as [n0 | fs].
          * exfalso; exact (witnessSetTaken_not_orig _ _ _ _ Hw1).
          * rewrite (witnessSetTaken_disjunct_det _ _ _ _ Hw1),
              (witnessSetTaken_disjunct_det _ _ _ _ Hw2); reflexivity.
        + injection He2 as -> ->.
          exfalso; exact (witnessSetTaken_not_orig _ _ _ _ Hw1).
        + injection He1 as -> ->; injection He2 as -> ->.
          exfalso; exact (Hn1 _ Hp2).
        + injection He1 as -> ->.
          exfalso; exact (witnessSetTaken_not_orig _ _ _ _ Hw2).
        + injection He1 as -> ->; injection He2 as _ ->; reflexivity.
    Qed.

    Module Lookup.
      Definition disjAlt (fs : list Formula) (i : Version.t) :
          option Formula :=
        match i with
        | Version.Idx k => List.nth_error fs k
        | _ => None
        end.

      (* An edge out of an original package is the owner's own: the only
         other sources an encoding has are the disjunct nodes it introduces,
         whose versions are indices. *)
      Definition notIdx (w : Version.t) : Prop :=
        forall i, w <> Version.Idx i.

      Lemma encodeNNF_src_orig_aux : forall Vq f,
          (forall (q : T.Pkg.t) m (w : Version.t) (d : T.Dependees.t),
              notIdx w ->
              T.DepRel.In ((Name.Orig m, w), d) (encodeNNF Vq q f) ->
              q = (Name.Orig m, w)) /\
          (forall (q : T.Pkg.t) m (w : Version.t) (d : T.Dependees.t),
              notIdx w ->
              T.DepRel.In ((Name.Orig m, w), d) (encodeNNFneg Vq q f) ->
              q = (Name.Orig m, w)) /\
          (forall (n : Name.t) (i0 : nat) m (w : Version.t) (d : T.Dependees.t),
              notIdx w ->
              T.DepRel.In ((Name.Orig m, w), d) (encodeDisj Vq n i0 f) ->
              False) /\
          (forall (n : Name.t) (i0 : nat) m (w : Version.t) (d : T.Dependees.t),
              notIdx w ->
              T.DepRel.In ((Name.Orig m, w), d) (encodeConjNeg Vq n i0 f) ->
              False).
      Proof.
        intros Vq f; induction f as [o ws | a IHa b IHb | a IHa b IHb | a IHa].
        - split4.
          + intros q m w d Hw H; apply SOed.singleton_in in H; congruence.
          + intros q m w d Hw H; apply SOed.singleton_in in H; congruence.
          + intros n i0 m w d Hw H; apply SOed.singleton_in in H;
              injection H as _ E _; destruct (Hw i0 E).
          + intros n i0 m w d Hw H; apply SOed.singleton_in in H;
              injection H as _ E _; destruct (Hw i0 E).
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q m w d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa1 _ _ _ _ Hw H) | exact (IHb1 _ _ _ _ Hw H)].
          + intros q m w d Hw H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ Hw H); injection E as _ E;
               destruct (Hw 0 (eq_sym E))
              | destruct (IHb4 _ _ _ _ _ Hw H)].
          + intros n i0 m w d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ Hw H) | assert (E := IHb1 _ _ _ _ Hw H)];
              injection E as _ E; destruct (Hw i0 (eq_sym E)).
          + intros n i0 m w d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ Hw H); injection E as _ E;
               destruct (Hw i0 (eq_sym E))
              | destruct (IHb4 _ _ _ _ _ Hw H)].
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
          + intros q m w d Hw H; simpl in H.
            apply SOed.add_in in H; destruct H as [H | H]; [congruence |].
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ Hw H); injection E as _ E;
               destruct (Hw 0 (eq_sym E))
              | destruct (IHb3 _ _ _ _ _ Hw H)].
          + intros q m w d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [exact (IHa2 _ _ _ _ Hw H) | exact (IHb2 _ _ _ _ Hw H)].
          + intros n i0 m w d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa1 _ _ _ _ Hw H); injection E as _ E;
               destruct (Hw i0 (eq_sym E))
              | destruct (IHb3 _ _ _ _ _ Hw H)].
          + intros n i0 m w d Hw H; simpl in H.
            apply T.DepRel.union_spec in H; destruct H as [H | H];
              [assert (E := IHa2 _ _ _ _ Hw H) | assert (E := IHb2 _ _ _ _ Hw H)];
              injection E as _ E; destruct (Hw i0 (eq_sym E)).
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros q m w d Hw H; exact (IHa2 _ _ _ _ Hw H).
          + intros q m w d Hw H; exact (IHa1 _ _ _ _ Hw H).
          + intros n i0 m w d Hw H; assert (E := IHa2 _ _ _ _ Hw H);
              injection E as _ E; destruct (Hw i0 (eq_sym E)).
          + intros n i0 m w d Hw H; assert (E := IHa1 _ _ _ _ Hw H);
              injection E as _ E; destruct (Hw i0 (eq_sym E)).
      Qed.

      Lemma notIdx_orig : forall v, notIdx (Version.Orig v).
      Proof. intros v i E; discriminate E. Qed.

      Lemma notIdx_bot : notIdx Version.Bot.
      Proof. intros i E; discriminate E. Qed.

      (* An edge's original target is a name the formula mentions. *)
      Lemma encodeNNF_tgt_aux : forall Vq f,
          (forall (q q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeNNF Vq q f) ->
              NSet.In m (fnames f)) /\
          (forall (q q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeNNFneg Vq q f) ->
              NSet.In m (fnames f)) /\
          (forall (n : Name.t) (i0 : nat) (q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeDisj Vq n i0 f) ->
              NSet.In m (fnames f)) /\
          (forall (n : Name.t) (i0 : nat) (q' : T.Pkg.t) m (ws : T.VSet.t),
              T.DepRel.In (q', (Name.Orig m, ws)) (encodeConjNeg Vq n i0 f) ->
              NSet.In m (fnames f)).
      Proof.
        intros Vq f; induction f as [o vs | a IHa b IHb | a IHa b IHb | a IHa].
        - split4; intros; apply SOed.singleton_in in H; injection H as _ <- _;
            simpl; apply NSet.singleton_spec; reflexivity.
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
            destruct IHb as (IHb1 & IHb2 & IHb3 & IHb4); split4.
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
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros q q' m ws H; exact (IHa2 _ _ _ _ H).
          + intros q q' m ws H; exact (IHa1 _ _ _ _ H).
          + intros n i0 q' m ws H; exact (IHa2 _ _ _ _ H).
          + intros n i0 q' m ws H; exact (IHa1 _ _ _ _ H).
      Qed.

      (* The encoder reads the oracle at the names the formula mentions and
         nowhere else. *)
      Lemma encodeNNF_agree_aux : forall Vq Vq' f,
          (forall m, NSet.In m (fnames f) -> Vq m = Vq' m) ->
          (forall p, encodeNNF Vq p f = encodeNNF Vq' p f) /\
          (forall p, encodeNNFneg Vq p f = encodeNNFneg Vq' p f) /\
          (forall n i, encodeDisj Vq n i f = encodeDisj Vq' n i f) /\
          (forall n i, encodeConjNeg Vq n i f = encodeConjNeg Vq' n i f).
      Proof.
        intros Vq Vq' f;
          induction f as [m vs | a IHa b IHb | a IHa b IHb | a IHa]; intro Hag.
        - assert (E : Vq m = Vq' m)
            by (apply Hag; simpl; apply NSet.singleton_spec; reflexivity).
          split4; intros; simpl; unfold negVS; try rewrite E; reflexivity.
        - assert (Ha : forall m, NSet.In m (fnames a) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; left;
                exact Hm).
          assert (Hb : forall m, NSet.In m (fnames b) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag; simpl; apply NSet.union_spec; right;
                exact Hm).
          destruct (IHa Ha) as (IHa1 & IHa2 & IHa3 & IHa4);
            destruct (IHb Hb) as (IHb1 & IHb2 & IHb3 & IHb4); split4;
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
            destruct (IHb Hb) as (IHb1 & IHb2 & IHb3 & IHb4); split4;
            intros; simpl.
          + rewrite IHa1, IHb3; reflexivity.
          + rewrite IHa2, IHb2; reflexivity.
          + rewrite IHa1, IHb3; reflexivity.
          + rewrite IHa2, IHb2; reflexivity.
        - destruct (IHa Hag) as (IHa1 & IHa2 & IHa3 & IHa4); split4;
            intros; simpl; [apply IHa2 | apply IHa1 | apply IHa2 | apply IHa1].
      Qed.

      Lemma reduceDepsBy_agree : forall Vq Vq' D,
          (forall m, NSet.In m (depNames D) -> Vq m = Vq' m) ->
          reduceDepsBy Vq D = reduceDepsBy Vq' D.
      Proof.
        intros Vq Vq' D Hag; apply T.DepRel.ext; intro d.
        rewrite !mem_reduceDepsBy.
        split; intros [p [f [Hd He]]]; exists p, f; split; try exact Hd;
          assert (Hf : forall m, NSet.In m (fnames f) -> Vq m = Vq' m)
            by (intros m Hm; apply Hag, mem_depNames; exists p, f; auto);
          [rewrite <- (proj1 (encodeNNF_agree_aux Vq Vq' f Hf))
          | rewrite (proj1 (encodeNNF_agree_aux Vq Vq' f Hf))]; exact He.
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Module DepRelFibred := FibredRel Pkg Dependees DepElt DepRel.
      Module RKeys := PreimageOfKeys N Pkg NSet PkgSet.

      (* The repository at a set of names. *)
      Definition nameRestrict (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
        RKeys.ofKeys fst ns R.

      Lemma versions_nameRestrict : forall R ns n,
          NSet.In n ns -> C.versions (nameRestrict R ns) n = C.versions R n.
      Proof.
        intros R ns n Hn; apply C.versions_ext; intro v.
        unfold nameRestrict; rewrite RKeys.mem_ofKeys; cbn [fst]; tauto.
      Qed.

      Definition syntheticPkgs (n : Name.t) : T.PkgSet.t :=
        match n with
        | Name.Orig _ => T.PkgSet.empty
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
        induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
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
      Qed.

      Lemma encodeNNF_target_synthetic_aux : forall Vq (f : Formula),
          (forall (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNF Vq p f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d))) (witnessSet p f)) /\
          (forall (p : T.Pkg.t) (d : T.DepElt.t),
              T.DepRel.In d (encodeNNFneg Vq p f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessSetNeg p f)) /\
          (forall (n : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeDisj Vq n i f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessDisj n i f)) /\
          (forall (n : Name.t) (i : nat) (d : T.DepElt.t),
              T.DepRel.In d (encodeConjNeg Vq n i f) ->
              T.PkgSet.Subset (syntheticPkgs (fst (snd d)))
                (witnessConjNeg n i f)).
      Proof.
        intros Vq f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
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
      Qed.

      Lemma reachable_instNames : forall R D (m : N.t),
          (exists p h, T.DepRel.In (p, (Name.Orig m, h)) (reduceDeps R D)) ->
          NSet.In m (instNames R D).
      Proof.
        intros R D m [p [h Hd]]; apply mem_reduceDeps in Hd.
        destruct Hd as [q [f [Hq He]]].
        apply mem_instNames; right; apply mem_depNames; exists q, f.
        split; [exact Hq |].
        exact (proj1 (encodeNNF_tgt_aux (C.versions R) f) _ _ _ _ He).
      Qed.

      (* A reachable name's versions are its real versions and absence: the
         repository at the name, and nothing of who negates it. *)
      Theorem versions_lookupOrig : forall R D (r : Pkg.t) (m : N.t),
          PkgSet.In r R ->
          (exists p h, T.DepRel.In (p, (Name.Orig m, h)) (reduceDeps R D)) \/
          Name.Orig m = Name.Orig (fst r) ->
          T.versions (reduceReal R D) (Name.Orig m) =
          T.VSet.add Version.Bot
            (embedVS (C.versions (PkgFibred.tailFibre R m) m)).
      Proof.
        intros R D r m Hr Hreach.
        assert (Hm : NSet.In m (instNames R D)).
        { destruct Hreach as [Hreach | E];
            [exact (reachable_instNames R D m Hreach) |].
          injection E as ->; apply mem_instNames; left.
          destruct r as [rn rv]; exists rv; exact Hr. }
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_reduceReal, SOvv.add_in.
        unfold embedVS; rewrite SOvv.mem_map.
        split.
        - intros [[[qn qv] [HR Hq]] | [[p [f [_ Hw]]] | [n [_ Hy]]]].
          + unfold embedPkg in Hq; injection Hq as -> ->.
            right; exists qv; split; [| reflexivity].
            apply C.mem_versions, PkgFibred.mem_tailFibre; auto.
          + exfalso; exact (witnessSet_not_orig _ _ _ _ Hw).
          + injection Hy as -> ->; left; reflexivity.
        - intros [-> | [v [Hv ->]]].
          + right; right; exists m; auto.
          + apply C.mem_versions, PkgFibred.mem_tailFibre in Hv.
            destruct Hv as [Hv _].
            left; exists (m, v); split; [exact Hv | reflexivity].
      Qed.

      (* A package's dependees read its own formulas and the repository at
         the names those formulas mention. *)
      Theorem dependees_lookupOrig : forall R D m v,
          T.dependees (reduceDeps R D) (Name.Orig m, Version.Orig v) =
          T.dependees
            (reduceDeps
               (nameRestrict R (depNames (DepRelFibred.tailFibre D (m, v))))
               (DepRelFibred.tailFibre D (m, v)))
            (Name.Orig m, Version.Orig v).
      Proof.
        intros R D m v; apply T.dependees_ext; intro h.
        rewrite !mem_reduceDeps.
        assert (Hag : forall f,
                   DepRel.In ((m, v), f) (DepRelFibred.tailFibre D (m, v)) ->
                   encodeNNF (C.versions R) (embedPkg (m, v)) f =
                   encodeNNF (C.versions (nameRestrict R
                                (depNames (DepRelFibred.tailFibre D (m, v)))))
                     (embedPkg (m, v)) f).
        { intros f Hf.
          assert (Hag' : forall x, NSet.In x (fnames f) ->
                     C.versions R x =
                     C.versions (nameRestrict R
                                   (depNames (DepRelFibred.tailFibre D (m, v)))) x).
          { intros x Hx; symmetry; apply versions_nameRestrict.
            apply mem_depNames; exists (m, v), f; auto. }
          exact (proj1 (encodeNNF_agree_aux _ _ f Hag') (embedPkg (m, v))). }
        split.
        - intros [p [f [Hd He]]].
          assert (E := proj1 (encodeNNF_src_orig_aux (C.versions R) f)
                         _ _ _ _ (notIdx_orig v) He).
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

      (* The shape a driver computes: the package's own formulas reduced
         under any oracle that agrees with the repository at the names they
         mention. *)
      Theorem dependees_lookupOrigBy : forall R D Vq m v,
          (forall n, NSet.In n (depNames (DepRelFibred.tailFibre D (m, v))) ->
                     Vq n = C.versions R n) ->
          T.dependees (reduceDeps R D) (Name.Orig m, Version.Orig v) =
          T.dependees (reduceDepsBy Vq (DepRelFibred.tailFibre D (m, v)))
            (Name.Orig m, Version.Orig v).
      Proof.
        intros R D Vq m v HVq; rewrite dependees_lookupOrig; unfold reduceDeps.
        f_equal; apply reduceDepsBy_agree; intros n Hn.
        rewrite versions_nameRestrict by exact Hn; symmetry; apply HVq; exact Hn.
      Qed.

      (* Absence depends on nothing. *)
      Theorem dependees_lookupAbsent : forall R D m,
          T.dependees (reduceDeps R D) (Name.Orig m, Version.Bot) =
          T.DependeesSet.empty.
      Proof.
        intros R D m; apply T.dependees_empty_iff; intros h H.
        apply mem_reduceDeps in H.
        destruct H as [[pn pv] [f [_ He]]].
        assert (E := proj1 (encodeNNF_src_orig_aux (C.versions R) f)
                       _ _ _ _ notIdx_bot He).
        unfold embedPkg in E; discriminate.
      Qed.

      Theorem versions_lookupDisjunct : forall R D (fs : list Formula),
          (exists p h,
              T.DepRel.In (p, (Name.Disjunct fs, h)) (reduceDeps R D)) ->
          T.versions (reduceReal R D) (Name.Disjunct fs) =
          idxSet (List.length fs).
      Proof.
        intros R D fs [p [h Hd]].
        apply mem_reduceDeps in Hd; destruct Hd as [r [g [HD He]]].
        pose proof (proj1 (encodeNNF_target_synthetic_aux (C.versions R) g)
                      (embedPkg r) (p, (Name.Disjunct fs, h)) He) as Hsub.
        cbn [fst snd] in Hsub.
        apply T.VSet.ext; intro w.
        rewrite T.mem_versions, mem_idxSet, mem_reduceReal.
        split.
        - intros [[[qn qv] [_ Hq]] | [[r1 [g1 [_ Hw]]] | [n [_ Hy]]]].
          + unfold embedPkg in Hq; discriminate Hq.
          + pose proof (proj1 (witnessSet_synthetic_aux g1) _ _ Hw) as Hg.
            cbn [fst syntheticPkgs] in Hg; apply mem_idxPkgs in Hg.
            destruct Hg as [i [Hi Hq]]; exists i;
              split; [exact Hi | congruence].
          + discriminate Hy.
        - intros [i [Hi ->]]; right; left; exists r, g; split; [exact HD |].
          apply Hsub; cbn [syntheticPkgs]; apply mem_idxPkgs;
            exists i; split; [exact Hi | reflexivity].
      Qed.

      Lemma encodeDisj_alt : forall Vq (f : Formula) (n : Name.t) (i0 j : nat)
                                    (g : Formula) (d : T.Dependees.t),
          List.nth_error (disjSpine f) j = Some g ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d)
            (encodeNNF Vq (n, Version.Idx (i0 + j)) g) ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d) (encodeDisj Vq n i0 f).
      Proof.
        intros Vq f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
          intros n i0 j g d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb n (S i0) j g d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma encodeConjNeg_alt : forall Vq (f : Formula) (n : Name.t)
                                       (i0 j : nat) (g : Formula)
                                       (d : T.Dependees.t),
          List.nth_error (negConjSpine f) j = Some g ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d)
            (encodeNNF Vq (n, Version.Idx (i0 + j)) g) ->
          T.DepRel.In ((n, Version.Idx (i0 + j)), d) (encodeConjNeg Vq n i0 f).
      Proof.
        intros Vq f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa];
          intros n i0 j g d Hg Hd; simpl in Hg.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j].
          + injection Hg as <-; replace (i0 + 0) with i0 in * by lia;
              apply T.DepRel.union_spec; left; exact Hd.
          + apply T.DepRel.union_spec; right;
              replace (i0 + S j) with (S i0 + j) in * by lia;
              exact (IHb n (S i0) j g d Hg Hd).
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
        - destruct j as [| j]; [| destruct j; discriminate].
          injection Hg as <-; replace (i0 + 0) with i0 in * by lia; exact Hd.
      Qed.

      Lemma witnessSet_alt_aux : forall Vq (f : Formula),
          (forall (p : T.Pkg.t) (gs : list Formula) (k : nat) (g : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k) (witnessSet p f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Vq p f)) /\
          (forall (p : T.Pkg.t) (gs : list Formula) (k : nat) (g : Formula)
                  (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessSetNeg p f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNFneg Vq p f)) /\
          (forall (n : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (g : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessDisj n i0 f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeDisj Vq n i0 f)) /\
          (forall (n : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (g : Formula) (d : T.Dependees.t),
              T.PkgSet.In (Name.Disjunct gs, Version.Idx k)
                (witnessConjNeg n i0 f) ->
              List.nth_error gs k = Some g ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g) ->
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeConjNeg Vq n i0 f)).
      Proof.
        intros Vq f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
        - split4; intros; exfalso; eapply SOpt.empty_in; eassumption.
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
              -- exact (encodeConjNeg_alt Vq b
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
              -- exact (encodeDisj_alt Vq b (Name.Disjunct (a :: disjSpine b))
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
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
          + intros p gs k g d H Hg Hd; exact (IHa2 _ _ _ _ _ H Hg Hd).
          + intros p gs k g d H Hg Hd; exact (IHa1 _ _ _ _ _ H Hg Hd).
          + intros n i0 gs k g d H Hg Hd; exact (IHa2 _ _ _ _ _ H Hg Hd).
          + intros n i0 gs k g d H Hg Hd; exact (IHa1 _ _ _ _ _ H Hg Hd).
      Qed.

      Lemma encodeNNF_alt_aux : forall Vq (f : Formula),
          (forall (q : T.Pkg.t) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNF Vq q f) ->
              q = (Name.Disjunct gs, Version.Idx k) \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (q : T.Pkg.t) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeNNFneg Vq q f) ->
              q = (Name.Disjunct gs, Version.Idx k) \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (n : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeDisj Vq n i0 f) ->
              (n = Name.Disjunct gs /\
               exists j g, k = i0 + j /\
                           List.nth_error (disjSpine f) j = Some g /\
                           T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                             (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g))
              \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g))) /\
          (forall (n : Name.t) (i0 : nat) (gs : list Formula) (k : nat)
                  (d : T.Dependees.t),
              T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                (encodeConjNeg Vq n i0 f) ->
              (n = Name.Disjunct gs /\
               exists j g, k = i0 + j /\
                           List.nth_error (negConjSpine f) j = Some g /\
                           T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                             (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g))
              \/
              (exists g, List.nth_error gs k = Some g /\
                         T.DepRel.In ((Name.Disjunct gs, Version.Idx k), d)
                           (encodeNNF Vq (Name.Disjunct gs, Version.Idx k) g))).
      Proof.
        intros Vq f; induction f as [m ws | a IHa b IHb | a IHa b IHb | a IHa].
        - split4.
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
        - destruct IHa as (IHa1 & IHa2 & IHa3 & IHa4); split4.
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
      Qed.

      (* A disjunct's dependees are read off the spine its name carries:
         version i carries alternative i's own encoding, under the repository
         at the names that alternative mentions. *)
      Theorem dependees_lookupDisjunct : forall R D fs (i : Version.t),
          T.PkgSet.In (Name.Disjunct fs, i) (reduceReal R D) ->
          T.dependees (reduceDeps R D) (Name.Disjunct fs, i) =
          match disjAlt fs i with
          | Some g =>
              T.dependees (encodeNNF (C.versions R) (Name.Disjunct fs, i) g)
                (Name.Disjunct fs, i)
          | None => T.DependeesSet.empty
          end.
      Proof.
        intros R D fs i H; apply mem_reduceReal in H.
        destruct H as [[[pn pv] [_ Hq]] | [[p [f [HD Hw]]] | [n [_ Hy]]]];
          [unfold embedPkg in Hq; discriminate Hq | | discriminate Hy].
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
          destruct (proj1 (encodeNNF_alt_aux (C.versions R) f') _ _ _ _ He)
            as [Eq | [g' [Hg' Hin]]].
          + destruct q as [qn qv]; unfold embedPkg in Eq; simpl in Eq;
              discriminate.
          + rewrite E in Hg'; injection Hg' as <-; exact Hin.
        - intro Hin; exists p, f; split; [exact HD |].
          exact (proj1 (witnessSet_alt_aux (C.versions R) f) _ _ _ _ _ Hw E Hin).
      Qed.

    End Lookup.
  End Reduction.
End PackageFormula.
