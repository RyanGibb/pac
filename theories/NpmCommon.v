From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude.

Module NpmCommon (N V : UsualOrderedType) (VSet : SetsOn V).
  Module RealPackage := PairUOT N V.
  Module RealPackageSet := FSetUOT RealPackage.
  Module NEqb := UOTEqb N.
  Module RealPackageEqb := UOTEqb RealPackage.

  Definition ownedBy {A : Type} (p : RealPackage.t) (l : list (RealPackage.t * A))
    : list A :=
    fold_right
      (fun q acc => if RealPackageEqb.eqb (fst q) p then snd q :: acc else acc)
      nil l.

  Lemma in_ownedBy : forall (A : Type) (l : list (RealPackage.t * A)) p a,
      In a (ownedBy p l) <-> In (p, a) l.
  Proof.
    intros A l p a; induction l as [| [q b] l IH]; simpl.
    - split; intros [].
    - destruct (RealPackageEqb.eqb q p) eqn:Hq.
      + apply RealPackageEqb.eqb_true_iff in Hq; subst q; simpl.
        split.
        * intros [-> | H]; [left; reflexivity | right; apply IH; exact H].
        * intros [H | H]; [| right; apply IH; exact H].
          assert (b = a) by congruence; subst b; left; reflexivity.
      + rewrite IH; split; [intro H; right; exact H |].
        intros [H | H]; [| exact H].
        assert (q = p) by congruence; subst q.
        rewrite RealPackageEqb.eqb_refl in Hq; discriminate.
  Qed.

  Lemma ownedBy_filter : forall (A : Type) (l : list (RealPackage.t * A)) f p,
      (forall a, In (p, a) l -> f (p, a) = true) ->
      ownedBy p (List.filter f l) = ownedBy p l.
  Proof.
    intros A l f p; induction l as [| [q b] l IH]; simpl; [reflexivity |].
    intro H.
    assert (Htl : forall a, In (p, a) l -> f (p, a) = true)
      by (intros a Ha; apply H; right; exact Ha).
    destruct (RealPackageEqb.eqb q p) eqn:Hq.
    - apply RealPackageEqb.eqb_true_iff in Hq; subst q.
      rewrite (H b (or_introl eq_refl)); simpl.
      rewrite RealPackageEqb.eqb_refl, (IH Htl); reflexivity.
    - destruct (f (q, b)); simpl; rewrite ?Hq; exact (IH Htl).
  Qed.

  Module SOrv := SetOps RealPackage V RealPackageSet VSet.
  Definition realVersions (R : RealPackageSet.t) (n : N.t) : VSet.t :=
    SOrv.filterMap
      (fun q => if NEqb.eqb (fst q) n then Some (snd q) else None) R.

  Lemma mem_realVersions : forall R n v,
      VSet.In v (realVersions R n) <-> RealPackageSet.In (n, v) R.
  Proof.
    intros R n v; unfold realVersions; rewrite SOrv.mem_filterMap_if.
    split.
    - intros [[m u] [HR [Hm ->]]]; cbn [fst snd] in *.
      apply NEqb.eqb_true_iff in Hm; subst m; exact HR.
    - intro H; exists (n, v); cbn [fst snd]; rewrite NEqb.eqb_refl; auto.
  Qed.

  Fixpoint lookupOvr {R : Type} (l : list (N.t * R)) (n : N.t) : option R :=
    match l with
    | nil => None
    | (m, rg) :: l' => if NEqb.eqb m n then Some rg else lookupOvr l' n
    end.
End NpmCommon.
