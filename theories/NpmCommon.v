From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude.

Module NpmCommon (N V : UsualOrderedType) (VS : SetsOn V).
  Module RPkg := PairUOT N V.
  Module RepoSet := FSetUOT RPkg.
  Module NEqb := UOTEqb N.
  Module RPkgEqb := UOTEqb RPkg.

  Definition ownedBy {A : Type} (p : RPkg.t) (l : list (RPkg.t * A))
    : list A :=
    fold_right
      (fun q acc => if RPkgEqb.eqb (fst q) p then snd q :: acc else acc)
      nil l.

  Lemma in_ownedBy : forall (A : Type) (l : list (RPkg.t * A)) p a,
      In a (ownedBy p l) <-> In (p, a) l.
  Proof.
    intros A l p a; induction l as [| [q b] l IH]; simpl.
    - split; intros [].
    - destruct (RPkgEqb.eqb q p) eqn:Hq.
      + apply RPkgEqb.eqb_true_iff in Hq; subst q; simpl.
        split.
        * intros [-> | H]; [left; reflexivity | right; apply IH; exact H].
        * intros [H | H]; [| right; apply IH; exact H].
          assert (b = a) by congruence; subst b; left; reflexivity.
      + rewrite IH; split; [intro H; right; exact H |].
        intros [H | H]; [| exact H].
        assert (q = p) by congruence; subst q.
        rewrite RPkgEqb.eqb_refl in Hq; discriminate.
  Qed.

  Module SOrv := SetOps RPkg V RepoSet VS.
  Definition realVersions (R : RepoSet.t) (n : N.t) : VS.t :=
    SOrv.filterMap
      (fun q => if NEqb.eqb (fst q) n then Some (snd q) else None) R.

  Lemma mem_realVersions : forall R n v,
      VS.In v (realVersions R n) <-> RepoSet.In (n, v) R.
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
