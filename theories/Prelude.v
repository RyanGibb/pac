From Stdlib Require Import MSetList Lia.

(* Sets are MSetList.MakeWithLeibniz -- sorted duplicate-free lists -- because
   the representation is canonical: two sets with the same elements are the same
   term, so set equality is Leibniz =, statements never mention setoid
   equivalences, and no Proper (respectfulness) side-conditions arise
   anywhere. The cost is that "sorted" needs a total order on every element
   type, including tuples, synthetic names, formulas, and sets themselves.

   This file makes them cheap. There are two entrances into UsualOrderedType
   (the stdlib's Leibniz-equality ordered interface, "UOT"): UOTFromCompare, for
   hand-defined inductives -- supply a compare and three laws (ComparableType),
   the functor derives the rest; and PairUOT/TripleUOT, lexicographic products
   of existing UOTs -- which also order constructor payloads, so new inductives'
   law proofs are one-line appeals to product facts. FSetUOT closes the loop: it
   builds the canonical set type over any UOT and re-exports it as a UOT
   (AsUOT), which is how sets nest inside elements of other sets.

   The stdlib's own compare-first path (OrderedTypeAlt) and product functors are
   unergonomic because they land in setoid equality; this file contains the
   small Leibniz-preserving replacement for that ecosystem gap. *)

(* enum is data, not an "exists a listing" fact (Stdlib's Finite): witnesses
   iterate it, so it must survive extraction. *)
Module Type FiniteUsualOrderedType.
  Include UsualOrderedType.
  Parameter enum : list t.
  Axiom enum_complete : forall x : t, List.In x enum.
End FiniteUsualOrderedType.

Definition lex (c d : comparison) : comparison :=
  match c with Eq => d | _ => c end.

Lemma lex_eq_iff : forall c d, lex c d = Eq <-> c = Eq /\ d = Eq.
Proof. destruct c; simpl; intuition congruence. Qed.

Lemma lex_opp : forall c d, CompOpp (lex c d) = lex (CompOpp c) (CompOpp d).
Proof. destruct c; reflexivity. Qed.

(* Transitivity for a lexicographic pair needs the left comparator's eq law to
   transport the tie, but only needs transitivity at the three points actually
   reached -- which is the shape an induction hypothesis comes in. Everything
   but the two premises is implicit so recursive uses stay one appeal. *)
Lemma lex_lt_trans {A B : Type} {ca : A -> A -> comparison}
    {cb : B -> B -> comparison} {a a' a'' : A} {b b' b'' : B} :
  (forall x y, ca x y = Eq <-> x = y) ->
  (ca a a' = Lt -> ca a' a'' = Lt -> ca a a'' = Lt) ->
  (cb b b' = Lt -> cb b' b'' = Lt -> cb b b'' = Lt) ->
  lex (ca a a') (cb b b') = Lt ->
  lex (ca a' a'') (cb b' b'') = Lt ->
  lex (ca a a'') (cb b b'') = Lt.
Proof.
  intros Heq Hta Htb H1 H2.
  destruct (ca a a') eqn:E1; simpl in H1; try discriminate.
  - apply Heq in E1 as ->.
    destruct (ca a' a'') eqn:E2; simpl in H2; try discriminate; simpl;
      [exact (Htb H1 H2) | reflexivity].
  - destruct (ca a' a'') eqn:E2; simpl in H2; try discriminate.
    + apply Heq in E2 as <-; rewrite E1; reflexivity.
    + rewrite (Hta eq_refl eq_refl); reflexivity.
Qed.

Module Type ComparableType.
  Parameter t : Type.
  Parameter compare : t -> t -> comparison.
  Axiom compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
  Axiom compare_antisym : forall x y, compare y x = CompOpp (compare x y).
  Axiom compare_lt_trans : forall x y z,
      compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
End ComparableType.

Module UOTFromCompare (X : ComparableType) <: UsualOrderedType.
  Definition t := X.t.
  Definition eq := @Logic.eq t.
  Definition eq_equiv := @eq_equivalence t.
  Definition lt (x y : t) : Prop := X.compare x y = Lt.

  Lemma compare_refl : forall x, X.compare x x = Eq.
  Proof. intro x; apply X.compare_eq_iff; reflexivity. Qed.

  #[global] Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - intros x H; unfold lt in H; rewrite compare_refl in H; discriminate.
    - intros x y z; unfold lt; apply X.compare_lt_trans.
  Qed.

  #[global] Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. intros x x' -> y y' ->; reflexivity. Qed.

  Definition compare := X.compare.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros x y; unfold compare, eq, lt.
    destruct (X.compare x y) eqn:E.
    - constructor; apply X.compare_eq_iff; exact E.
    - constructor; exact E.
    - constructor; rewrite X.compare_antisym, E; reflexivity.
  Qed.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros x y; destruct (X.compare x y) eqn:E.
    - left; apply X.compare_eq_iff; exact E.
    - right; intro H; subst; rewrite compare_refl in E; discriminate.
    - right; intro H; subst; rewrite compare_refl in E; discriminate.
  (* Defined, not Qed: eq_dec feeds if-then-else, so it must stay reducible *)
  Defined.
End UOTFromCompare.

(* Same facts as OrderedTypeFacts but stated with plain Logic.eq, so that
   subst works on the results. *)
Module UOTCompareFacts (X : UsualOrderedType).
  Module F := OrderedTypeFacts X.

  Lemma compare_eq_iff : forall a b, X.compare a b = Eq <-> a = b.
  Proof. intros a b; exact (F.compare_eq_iff a b). Qed.

  Lemma compare_antisym : forall a b, X.compare b a = CompOpp (X.compare a b).
  Proof. intros a b; exact (F.compare_antisym a b). Qed.

  Lemma compare_lt_trans : forall a b c,
      X.compare a b = Lt -> X.compare b c = Lt -> X.compare a c = Lt.
  Proof.
    intros a b c A B; apply F.compare_lt_iff in A, B; apply F.compare_lt_iff.
    eapply StrictOrder_Transitive; eassumption.
  Qed.
End UOTCompareFacts.

(* Discharging a goal by a UOTCompareFacts instance of a functor-built
   comparator needs delta to see through the instance's statement, which only
   full elaboration does -- Hint Resolve's simple apply and eassumption both
   fail. So transitivity, whose middle element resolution would anyway have to
   guess, takes both premises from the context and lets the application
   typecheck; antisymmetry is a plain apply. *)
Ltac cmp_by t :=
  first [ match goal with
          | A : _ = Lt, B : _ = Lt |- _ => exact (t _ _ _ A B)
          end
        | apply t ].

(* solve would report only "No applicable tactic"; the constructor pair that
   went wrong is legible only from the goal itself. *)
Ltac cmp_stuck := match goal with |- ?G => fail 2 "no delegate for" G end.

(* Every synthetic name/version inductive proves the three ComparableType laws
   by the same case bash over constructor pairs: off-diagonal pairs are settled
   by constructor disjointness, diagonal pairs delegate to a UOTCompareFacts
   instance registered in db: compare_eq_iff as a rewrite rule, the other two
   as cmp_by hints. The database is an argument rather than one fixed name so
   that a file only ever searches the delegates it registered; a shared
   database would grow with every Require and make the proofs order-dependent.
   cbn rather than simpl because a rank-indexed compare stays stuck under
   simpl, while cbn still declines to unfold the delegates. *)
Tactic Notation "cmp_eq_iff" ident(db) :=
  intros x y; destruct x, y; cbn;
  first [ solve [split; intro H; congruence]
        | solve [autorewrite with db; split; intro H; congruence]
        | cmp_stuck ].

Tactic Notation "cmp_antisym" ident(db) :=
  intros x y; destruct x, y; cbn;
  first [ reflexivity | solve [auto with db] | cmp_stuck ].

Tactic Notation "cmp_lt_trans" ident(db) :=
  intros x y z; destruct x, y, z; cbn; intros H1 H2;
  first [ solve [congruence] | solve [auto with db] | cmp_stuck ].

(* Deciding equality inside a set-comprehension guard means an if-then-else on
   eq_dec, whose two branches then have to be re-derived at every proof that
   reads the guard back; this packages the test with its three laws. *)
Module UOTEqb (X : UsualOrderedType).
  Definition eqb (a b : X.t) : bool := if X.eq_dec a b then true else false.

  Lemma eqb_true_iff : forall a b, eqb a b = true <-> a = b.
  Proof.
    intros a b; unfold eqb; destruct (X.eq_dec a b) as [E | NE];
      split; intro H; solve [exact E | reflexivity | discriminate
                            | contradiction NE].
  Qed.

  Lemma eqb_refl : forall a, eqb a a = true.
  Proof. intro a; apply eqb_true_iff; reflexivity. Qed.

  Lemma eqb_false_iff : forall a b, eqb a b = false <-> a <> b.
  Proof.
    intros a b; unfold eqb; destruct (X.eq_dec a b) as [E | NE];
      split; intro H;
      [discriminate | contradiction (H E) | exact NE | reflexivity].
  Qed.
End UOTEqb.

Module BoolComp <: ComparableType.
  Definition t := bool.
  Definition compare (a b : bool) : comparison :=
    match a, b with
    | false, false => Eq | false, true => Lt
    | true, false => Gt | true, true => Eq
    end.
  Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
  Proof. intros [|] [|]; simpl; split; intro; congruence. Qed.
  Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
  Proof. intros [|] [|]; reflexivity. Qed.
  Lemma compare_lt_trans : forall x y z,
      compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
  Proof. intros [|] [|] [|]; simpl; congruence. Qed.
End BoolComp.
Module BoolOT := UOTFromCompare BoolComp.

(* Syntax whose shape is a list -- a conjunction, a disjunction of those --
   needs an order as soon as it is carried inside a set element. Ordering
   head-first with nil least keeps the three laws one appeal to the
   element's own, exactly as PairUOT does for products. *)
Module ListComp (A : ComparableType) <: ComparableType.
  Definition t : Type := list A.t.

  Fixpoint compare (x y : t) : comparison :=
    match x, y with
    | nil, nil => Eq
    | nil, _ :: _ => Lt
    | _ :: _, nil => Gt
    | a :: x', b :: y' => lex (A.compare a b) (compare x' y')
    end.

  Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
  Proof.
    intro x; induction x as [| a x IH]; intros y; destruct y as [| b y];
      simpl; try (split; intro H; congruence).
    rewrite lex_eq_iff, A.compare_eq_iff, IH.
    split;
      [intros [-> ->]; reflexivity | intro H; injection H as -> ->; auto].
  Qed.

  Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
  Proof.
    intro x; induction x as [| a x IH]; intros y; destruct y as [| b y];
      simpl; try reflexivity.
    rewrite lex_opp, A.compare_antisym, IH; reflexivity.
  Qed.

  Lemma compare_lt_trans : forall x y z,
      compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
  Proof.
    intro x; induction x as [| a x IH]; intros y z;
      destruct y as [| b y], z as [| c z]; simpl; intros H1 H2;
      try congruence.
    exact (lex_lt_trans A.compare_eq_iff (A.compare_lt_trans a b c)
             (IH y z) H1 H2).
  Qed.
End ListComp.

(* Stdlib's pair-ordered-type functors build setoid eq; none preserves
   UsualOrderedType. *)
Module PairUOT (A B : UsualOrderedType) <: UsualOrderedType.
  Definition t : Type := (A.t * B.t)%type.
  Definition eq := @Logic.eq t.
  Definition eq_equiv : Equivalence eq := eq_equivalence.

  Definition lt (x y : t) : Prop :=
    A.lt (fst x) (fst y) \/ (fst x = fst y /\ B.lt (snd x) (snd y)).

  #[global] Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - intros [a b] [H | [_ H]]; simpl in H.
      + exact (StrictOrder_Irreflexive a H).
      + exact (StrictOrder_Irreflexive b H).
    - intros [a1 b1] [a2 b2] [a3 b3] H12 H23.
      destruct H12 as [H12 | [E12 H12]]; destruct H23 as [H23 | [E23 H23]];
        simpl in *; subst.
      + left; exact (StrictOrder_Transitive _ _ _ H12 H23).
      + left; exact H12.
      + left; exact H23.
      + right; split;
          [reflexivity | exact (StrictOrder_Transitive _ _ _ H12 H23)].
  Qed.

  #[global] Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. intros x x' -> y y' ->; reflexivity. Qed.

  Definition compare (x y : t) : comparison :=
    match A.compare (fst x) (fst y) with
    | Eq => B.compare (snd x) (snd y)
    | c => c
    end.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros [a1 b1] [a2 b2]; unfold compare; simpl.
    destruct (A.compare_spec a1 a2) as [E | L | G].
    - (* A.eq is Logic.eq for UsualOrderedType *)
      destruct (B.compare_spec b1 b2) as [E' | L' | G'].
      + constructor; unfold eq; congruence.
      + constructor; right; simpl; auto.
      + constructor; right; simpl; auto.
    - constructor; left; exact L.
    - constructor; left; exact G.
  Qed.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros [a1 b1] [a2 b2].
    destruct (A.eq_dec a1 a2) as [-> | Hn].
    - destruct (B.eq_dec b1 b2) as [-> | Hn].
      + left; reflexivity.
      + right; intro H; apply Hn; congruence.
    - right; intro H; apply Hn; congruence.
  Defined.
End PairUOT.

Module TripleUOT (A B C : UsualOrderedType) <: UsualOrderedType.
  Module BC := PairUOT B C.
  Include PairUOT A BC.
End TripleUOT.

(* MSets makes the filter/exists_/for_all specs conditional on the
   predicate respecting E.eq; with eq Leibniz that condition is vacuous, so it is
   discharged once here rather than re-proved inline at every call site. *)
Module SetSpecs (E : UsualOrderedType) (S : SetsOn E).
  Lemma compat : forall f : E.t -> bool, Proper (E.eq ==> Logic.eq) f.
  Proof. intros f x y Heq; rewrite Heq; reflexivity. Qed.

  Lemma filter_spec' : forall (f : E.t -> bool) (s : S.t) (x : E.t),
      S.In x (S.filter f s) <-> S.In x s /\ f x = true.
  Proof. intros f s x; apply S.filter_spec, compat. Qed.

  Lemma exists_spec' : forall (f : E.t -> bool) (s : S.t),
      S.exists_ f s = true <-> exists x : E.t, S.In x s /\ f x = true.
  Proof. intros f s; apply S.exists_spec, compat. Qed.

  Lemma for_all_spec' : forall (f : E.t -> bool) (s : S.t),
      S.for_all f s = true <-> forall x : E.t, S.In x s -> f x = true.
  Proof. intros f s; apply S.for_all_spec, compat. Qed.

  (* Cutting a set down to s' is invisible to a test that only ever looks at
     elements s' keeps -- the shape every lookup theorem's restriction lemma
     has. The combinator forms live in SetOps, which knows the target set. *)
  Lemma mem_restrict : forall (s s' : S.t) (x : E.t),
      S.Subset s' s -> (S.In x s -> S.In x s') -> S.mem x s' = S.mem x s.
  Proof.
    intros s s' x Hsub Hin.
    destruct (S.mem x s') eqn:H'; destruct (S.mem x s) eqn:H;
      try reflexivity; exfalso.
    - rewrite S.mem_spec in H'; apply Hsub in H'.
      rewrite <- S.mem_spec in H'; rewrite H' in H; discriminate.
    - rewrite S.mem_spec in H; apply Hin in H.
      rewrite <- S.mem_spec in H; rewrite H in H'; discriminate.
  Qed.

  Lemma exists_restrict : forall (f : E.t -> bool) (s s' : S.t),
      S.Subset s' s -> (forall x, S.In x s -> f x = true -> S.In x s') ->
      S.exists_ f s' = S.exists_ f s.
  Proof.
    intros f s s' Hsub Hkeep.
    destruct (S.exists_ f s') eqn:H'; destruct (S.exists_ f s) eqn:H;
      try reflexivity; exfalso.
    - rewrite exists_spec' in H'; destruct H' as [x [Hx Hf]].
      assert (S.exists_ f s = true) as C.
      { apply exists_spec'; exists x; split; [exact (Hsub _ Hx) | exact Hf]. }
      rewrite C in H; discriminate.
    - rewrite exists_spec' in H; destruct H as [x [Hx Hf]].
      assert (S.exists_ f s' = true) as C.
      { apply exists_spec'; exists x;
          split; [exact (Hkeep _ Hx Hf) | exact Hf]. }
      rewrite C in H'; discriminate.
  Qed.
End SetSpecs.

(* Building a sorted-list set by repeated add is quadratic, since every add
   walks the list. union, however, is a linear merge of two sorted lists, so
   pairing off a list of sets and repeating until one remains is a merge sort
   over proved primitives -- O(n log n), with dedup falling out of the merge --
   and never needs the representation or a Sorted proof, which is what keeps it
   usable through the abstract SetsOn interface. The fuel is the input's
   length, which each round halves, so the fold branch is never reached; it
   still meets the spec so that the proof need not argue about reachability. *)
Module SetBuild (B : UsualOrderedType) (SB : SetsOn B).
  Fixpoint pairUp (l : list SB.t) : list SB.t :=
    match l with
    | a :: b :: l' => SB.union a b :: pairUp l'
    | _ => l
    end.

  Fixpoint unionsFuel (fuel : nat) (l : list SB.t) : SB.t :=
    match l with
    | nil => SB.empty
    | s :: nil => s
    | _ => match fuel with
           | O => List.fold_left SB.union l SB.empty
           | S k => unionsFuel k (pairUp l)
           end
    end.

  Definition unions (l : list SB.t) : SB.t := unionsFuel (List.length l) l.

  Definition ofList (l : list B.t) : SB.t := unions (List.map SB.singleton l).

  Lemma in_pairUp : forall (n : nat) (l : list SB.t) (y : B.t),
      List.length l <= n ->
      ((exists s, List.In s (pairUp l) /\ SB.In y s) <->
       (exists s, List.In s l /\ SB.In y s)).
  Proof.
    induction n as [| n IH]; intros [| a [| b l]] y Hlen; simpl in Hlen;
      cbn [pairUp]; try reflexivity; [inversion Hlen |].
    assert (List.length l <= n) as Hl by lia.
    split.
    - intros [s [[<- | Hs] Hy]].
      + apply SB.union_spec in Hy; destruct Hy as [Hy | Hy];
          [exists a; split; [left; reflexivity | exact Hy]
          | exists b; split; [right; left; reflexivity | exact Hy]].
      + destruct (proj1 (IH l y Hl) (ex_intro _ s (conj Hs Hy)))
          as [s' [Hs' Hy']].
        exists s'; split; [right; right; exact Hs' | exact Hy'].
    - intros [s [[<- | [<- | Hs]] Hy]].
      + exists (SB.union a b); split;
          [left; reflexivity | apply SB.union_spec; left; exact Hy].
      + exists (SB.union a b); split;
          [left; reflexivity | apply SB.union_spec; right; exact Hy].
      + destruct (proj2 (IH l y Hl) (ex_intro _ s (conj Hs Hy)))
          as [s' [Hs' Hy']].
        exists s'; split; [right; exact Hs' | exact Hy'].
  Qed.

  Lemma in_fold_union : forall (l : list SB.t) (i : SB.t) (y : B.t),
      SB.In y (List.fold_left SB.union l i) <->
      SB.In y i \/ exists s, List.In s l /\ SB.In y s.
  Proof.
    induction l as [| s l IH]; intros i y; simpl.
    - split; [tauto | intros [H | [s [[] _]]]; exact H].
    - rewrite IH, SB.union_spec; split.
      + intros [[Hi | Hs] | [s' [Hs' Hy]]];
          [left; exact Hi | right; exists s; auto | right; exists s'; auto].
      + intros [Hi | [s' [[<- | Hs'] Hy]]];
          [left; left; exact Hi | left; right; exact Hy
          | right; exists s'; auto].
  Qed.

  Lemma mem_unionsFuel : forall (fuel : nat) (l : list SB.t) (y : B.t),
      SB.In y (unionsFuel fuel l) <-> exists s, List.In s l /\ SB.In y s.
  Proof.
    induction fuel as [| fuel IH]; intros [| a [| b l]] y; cbn [unionsFuel].
    - split; [intro H; destruct (SB.empty_spec H) | intros [s [[] _]]].
    - split; [intro H; exists a; split; [left; reflexivity | exact H]
             | intros [s [[<- | []] H]]; exact H].
    - rewrite in_fold_union; split;
        [intros [H | H]; [destruct (SB.empty_spec H) | exact H]
        | intro H; right; exact H].
    - split; [intro H; destruct (SB.empty_spec H) | intros [s [[] _]]].
    - split; [intro H; exists a; split; [left; reflexivity | exact H]
             | intros [s [[<- | []] H]]; exact H].
    - rewrite IH; exact (in_pairUp _ (a :: b :: l) y (le_n _)).
  Qed.

  Lemma mem_unions : forall (l : list SB.t) (y : B.t),
      SB.In y (unions l) <-> exists s, List.In s l /\ SB.In y s.
  Proof. intros l y; apply mem_unionsFuel. Qed.

  Lemma mem_ofList : forall (l : list B.t) (y : B.t),
      SB.In y (ofList l) <-> List.In y l.
  Proof.
    intros l y; unfold ofList; rewrite mem_unions; split.
    - intros [s [Hs Hy]]; apply List.in_map_iff in Hs;
        destruct Hs as [x [<- Hx]].
      apply SB.singleton_spec in Hy; assert (y = x) as -> by exact Hy; exact Hx.
    - intro Hy; exists (SB.singleton y); split;
        [apply List.in_map_iff; exists y; auto
        | apply SB.singleton_spec; reflexivity].
  Qed.
End SetBuild.

Module FSetUOT (X : UsualOrderedType).
  Module OTWL <: OrderedTypeWithLeibniz.
    Include X.
    Lemma eq_leibniz : forall x y, eq x y -> x = y.
    Proof. intros x y H; exact H. Qed.
  End OTWL.
  Module M := MSetList.MakeWithLeibniz OTWL.
  Include M.
  Include SetSpecs OTWL M.
  Include SetBuild OTWL M.

  Lemma ext : forall s s' : t, (forall x, In x s <-> In x s') -> s = s'.
  Proof. intros s s' H; apply eq_leibniz; exact H. Qed.

  Lemma is_empty_iff : forall s : t, is_empty s = true <-> s = empty.
  Proof.
    intro s; rewrite is_empty_spec; split.
    - intro H; apply ext; intro x; split; intro Hx.
      + destruct (H x Hx).
      + destruct (empty_spec Hx).
    - intros -> x Hx; exact (empty_spec Hx).
  Qed.

  Lemma empty_subset : forall s : t, Subset empty s.
  Proof. intros s x Hx; destruct (empty_spec Hx). Qed.

  Lemma choose_nonempty : forall s : t, is_empty s = false -> exists x, In x s.
  Proof.
    intros s E.
    destruct (choose s) as [x | ] eqn:C.
    - exists x; exact (choose_spec1 C).
    - apply choose_spec2 in C.
      rewrite <- is_empty_spec in C; congruence.
  Qed.

  (* Sets as elements of other sets need their own order. The set module
     itself does not match UsualOrderedType -- its eq field is Equal, not
     Logic.eq, even though eq_leibniz makes them coincide -- so AsUOT
     repackages the same components with eq := Logic.eq. *)
  Module AsUOT <: UsualOrderedType.
    Definition t := t.
    Definition eq := @Logic.eq t.
    Definition eq_equiv : Equivalence eq := eq_equivalence.
    Definition lt := lt.

    #[global] Instance lt_strorder : StrictOrder lt.
    Proof.
      split.
      - intros s H. exact (StrictOrder_Irreflexive s H).
      - intros s1 s2 s3 H12 H23. exact (StrictOrder_Transitive _ _ _ H12 H23).
    Qed.

    #[global] Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof. intros x x' -> y y' ->; reflexivity. Qed.

    Definition compare := compare.

    Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
    Proof.
      intros x y; unfold compare, eq, lt.
      destruct (compare_spec x y) as [E | L | G].
      - constructor; apply eq_leibniz; exact E.
      - constructor; exact L.
      - constructor; exact G.
    Qed.

    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct (eq_dec x y) as [E | Hn].
      - left; apply eq_leibniz; exact E.
      - right; intro H; apply Hn; subst; reflexivity.
    Defined.
  End AsUOT.
End FSetUOT.

(* A relation read as a set of directed edges from tail T to head H: the
   functor equips it with the fibres of its tail projection -- one tail's
   edges as a sub-relation -- which is what the lookup theorems compute
   over. *)
Module FibredRel (T H : UsualOrderedType)
    (* the with-constraint exposes E's pair structure, so edges of an existing
       relation can be destructured here *)
    (E : UsualOrderedType with Definition t := (T.t * H.t)%type)
    (S : SetsOn E).
  Module SS := SetSpecs E S.

  Definition tail '((q, _) : E.t) : T.t := q.

  (* The fibre of p under the tail projection. *)
  Definition tailFibre (D : S.t) (p : T.t) : S.t :=
    S.filter (fun e => if T.eq_dec (tail e) p then true else false) D.

  Lemma mem_tailFibre : forall D (p q : T.t) (h : H.t),
      S.In (q, h) (tailFibre D p) <-> S.In (q, h) D /\ q = p.
  Proof.
    intros D p q h; unfold tailFibre.
    rewrite SS.filter_spec'.
    simpl.
    destruct (T.eq_dec q p); intuition congruence.
  Qed.

  Lemma tailFibre_subset : forall D (p : T.t), S.Subset (tailFibre D p) D.
  Proof.
    intros D p [q h] Hin; apply mem_tailFibre in Hin; destruct Hin as [Hin _];
      exact Hin.
  Qed.

  Definition head '((_, h) : E.t) : H.t := h.

  (* The fibre of h under the head projection. *)
  Definition headFibre (D : S.t) (h : H.t) : S.t :=
    S.filter (fun e => if H.eq_dec (head e) h then true else false) D.

  Lemma mem_headFibre : forall D (q : T.t) (h g : H.t),
      S.In (q, g) (headFibre D h) <-> S.In (q, g) D /\ g = h.
  Proof.
    intros D q h g; unfold headFibre.
    rewrite SS.filter_spec'.
    simpl.
    destruct (H.eq_dec g h); intuition congruence.
  Qed.

  Lemma headFibre_subset : forall D (h : H.t), S.Subset (headFibre D h) D.
  Proof.
    intros D h [q g] Hin; apply mem_headFibre in Hin; destruct Hin as [Hin _];
      exact Hin.
  Qed.

  (* The fibre of x under the identity projection. *)
  Definition idFibre (D : S.t) (x : E.t) : S.t :=
    S.filter (fun e => if E.eq_dec e x then true else false) D.

  Lemma mem_idFibre : forall D (x y : E.t),
      S.In y (idFibre D x) <-> S.In y D /\ y = x.
  Proof.
    intros D x y; unfold idFibre.
    rewrite SS.filter_spec'.
    destruct (E.eq_dec y x); intuition congruence.
  Qed.

  Lemma idFibre_subset : forall D (x : E.t), S.Subset (idFibre D x) D.
  Proof.
    intros D x y Hin; apply mem_idFibre in Hin; destruct Hin as [Hin _];
      exact Hin.
  Qed.
End FibredRel.

(* The labelled reading: the head factors into a node N and a label L, so an
   edge runs from tail T to node N with L riding along. The factoring makes
   ends = (tail, node) coarser than the whole edge, so a second fibre exists:
   endsFibre, the parallel edges between two endpoints differing only in
   label, which is what the lookup theorems keyed by both endpoints compute
   over. *)
Module FibredLabelledRel (T N L : UsualOrderedType)
    (E : UsualOrderedType with Definition t := (T.t * (N.t * L.t))%type)
    (S : SetsOn E).
  Module H := PairUOT N L.
  Include FibredRel T H E S.

  Definition ends '((q, (m, _)) : E.t) : (T.t * N.t)%type := (q, m).

  (* The fibre of (p, n) under the ends projection. *)
  Definition endsFibre (D : S.t) (p : T.t) (n : N.t) : S.t :=
    S.filter (fun e => let '(q, m) := ends e in
        if T.eq_dec q p
        then if N.eq_dec m n then true else false
        else false)
      D.

  Lemma mem_endsFibre : forall D (p q : T.t) (n m : N.t) (l : L.t),
      S.In (q, (m, l)) (endsFibre D p n) <->
      S.In (q, (m, l)) D /\ q = p /\ m = n.
  Proof.
    intros D p q n m l; unfold endsFibre.
    rewrite SS.filter_spec'.
    simpl.
    destruct (T.eq_dec q p); [destruct (N.eq_dec m n) |];
      intuition congruence.
  Qed.

  Lemma endsFibre_subset : forall D (p : T.t) (n : N.t),
      S.Subset (endsFibre D p n) D.
  Proof.
    intros D p n [q [m l]] Hin; apply mem_endsFibre in Hin;
      destruct Hin as [Hin _]; exact Hin.
  Qed.

  Definition node '((_, (n, _)) : E.t) : N.t := n.

  (* The fibre of n under the head-node projection. *)
  Definition nodeFibre (D : S.t) (n : N.t) : S.t :=
    S.filter (fun e => if N.eq_dec (node e) n then true else false) D.

  Lemma mem_nodeFibre : forall D (q : T.t) (n m : N.t) (l : L.t),
      S.In (q, (m, l)) (nodeFibre D n) <-> S.In (q, (m, l)) D /\ m = n.
  Proof.
    intros D q n m l; unfold nodeFibre.
    rewrite SS.filter_spec'.
    simpl.
    destruct (N.eq_dec m n); intuition congruence.
  Qed.

  Lemma nodeFibre_subset : forall D (n : N.t), S.Subset (nodeFibre D n) D.
  Proof.
    intros D n [q [m l]] Hin; apply mem_nodeFibre in Hin;
      destruct Hin as [Hin _]; exact Hin.
  Qed.
End FibredLabelledRel.

(* The other way a lookup theorem cuts a set down: its elements carry a key --
   a package set read as a name-to-version relation projects to names -- and
   the preimage of the wanted keys under that projection is all of the set a
   computation that consults only those keys can see. Which keys are wanted
   arrives as a test rather than as a set, so that the two entry points share
   this one definition: keys already materialized (PreimageOfKeys.ofKeys), and
   the keys a relation's edges point at (RelKeys.hasKey), which stays a
   semijoin and never materializes them. *)
Module Preimage (A : UsualOrderedType) (S : SetsOn A).
  Module SS := SetSpecs A S.

  Section OfTest.
    Context {K : Type}.
    Variables (key : A.t -> K) (test : K -> bool).

    Definition preimage (s : S.t) : S.t :=
      S.filter (fun x => test (key x)) s.

    Lemma mem_preimage : forall (s : S.t) (x : A.t),
        S.In x (preimage s) <-> S.In x s /\ test (key x) = true.
    Proof. intros s x; unfold preimage; apply SS.filter_spec'. Qed.

    Lemma preimage_subset : forall s : S.t, S.Subset (preimage s) s.
    Proof. intros s x Hx; apply mem_preimage in Hx; exact (proj1 Hx). Qed.
  End OfTest.
End Preimage.

Module PreimageOfKeys (K A : UsualOrderedType) (SK : SetsOn K) (SA : SetsOn A).
  Include Preimage A SA.

  Definition ofKeys (key : A.t -> K.t) (ks : SK.t) (s : SA.t) : SA.t :=
    preimage key (fun k => SK.mem k ks) s.

  Lemma mem_ofKeys : forall key ks (s : SA.t) (x : A.t),
      SA.In x (ofKeys key ks s) <-> SA.In x s /\ SK.In (key x) ks.
  Proof.
    intros key ks s x; unfold ofKeys.
    rewrite mem_preimage, SK.mem_spec; reflexivity.
  Qed.

  Lemma ofKeys_subset : forall key ks (s : SA.t),
      SA.Subset (ofKeys key ks s) s.
  Proof. intros key ks s; apply preimage_subset. Qed.

End PreimageOfKeys.

(* Asking the relation one key at a time is what keeps the preimage along it a
   semijoin; the key set it stands for is never built. *)
Module RelKeys (K B : UsualOrderedType) (SB : SetsOn B).
  Module SS := SetSpecs B SB.
  Module KEqb := UOTEqb K.

  Definition hasKey (tgt : B.t -> K.t) (D : SB.t) (k : K.t) : bool :=
    SB.exists_ (fun e => KEqb.eqb (tgt e) k) D.

  Lemma hasKey_iff : forall tgt (D : SB.t) (k : K.t),
      hasKey tgt D k = true <-> exists e : B.t, SB.In e D /\ tgt e = k.
  Proof.
    intros tgt D k; unfold hasKey; rewrite SS.exists_spec'.
    split; (intros [e [He Hk]]; exists e;
            split; [exact He | apply KEqb.eqb_true_iff; exact Hk]).
  Qed.
End RelKeys.

(* MSets provide no cross-type map; SetOps reifies the missing combinators
   (map, filterMap, unionMap, filterExists, ofList) together with their
   membership specs. The comprehensions list their images and hand the list
   to SetBuild, so each is one merge sort; [in_fold] remains the tool for
   hand-written folds that fit none of them. *)
Module SetOps (A B : UsualOrderedType) (SA : SetsOn A) (SB : SetsOn B).
  Module SSA := SetSpecs A SA.
  Module SSB := SetSpecs B SB.
  Include SetBuild B SB.

  Lemma add_in : forall (x : B.t) (s : SB.t) (y : B.t),
      SB.In y (SB.add x s) <-> y = x \/ SB.In y s.
  Proof.
    intros x s y; rewrite SB.add_spec;
      split; (intros [H | H]; [left; exact H | right; exact H]).
  Qed.

  Lemma singleton_in : forall (x y : B.t),
      SB.In y (SB.singleton x) <-> y = x.
  Proof.
    intros x y; rewrite SB.singleton_spec;
      split; intro H; exact H.
  Qed.

  Lemma empty_in : forall y : B.t, ~ SB.In y SB.empty.
  Proof. intros y H; exact (SB.empty_spec H). Qed.

  Lemma union_subset : forall a a' b b' : SB.t,
      SB.Subset a a' -> SB.Subset b b' ->
      SB.Subset (SB.union a b) (SB.union a' b').
  Proof.
    intros a a' b b' Ha Hb y Hy; apply SB.union_spec in Hy.
    apply SB.union_spec; destruct Hy as [Hy | Hy];
      [left; exact (Ha _ Hy) | right; exact (Hb _ Hy)].
  Qed.

  Lemma elements_in : forall (s : SA.t) (x : A.t),
      List.In x (SA.elements s) <-> SA.In x s.
  Proof.
    intros s x; rewrite <- SA.elements_spec1, SetoidList.InA_alt.
    split.
    - intro H; exists x; split; [reflexivity | exact H].
    - intros [y [E H]]; assert (x = y) as -> by exact E; exact H.
  Qed.

  Lemma in_fold_list :
    forall (step : A.t -> SB.t -> SB.t) (h : A.t -> SB.t),
      (forall e a y, SB.In y (step e a) <-> SB.In y (h e) \/ SB.In y a) ->
      forall (l : list A.t) (i : SB.t) (y : B.t),
        SB.In y (List.fold_left (fun a e => step e a) l i) <->
        SB.In y i \/ exists e, List.In e l /\ SB.In y (h e).
  Proof.
    intros step h Hstep l; induction l as [ | e l IH ]; intros i y; simpl.
    - split; [tauto | intros [H | [e [[] _]]]; exact H].
    - rewrite IH, Hstep; split.
      + intros [[Hh | Hi] | [e' [He' Hh']]].
        * right; exists e; auto.
        * left; exact Hi.
        * right; exists e'; auto.
      + intros [Hi | [e' [[-> | He'] Hh']]].
        * left; right; exact Hi.
        * left; left; exact Hh'.
        * right; exists e'; auto.
  Qed.

  Lemma in_fold :
    forall (step : A.t -> SB.t -> SB.t) (h : A.t -> SB.t),
      (forall e a y, SB.In y (step e a) <-> SB.In y (h e) \/ SB.In y a) ->
      forall (s : SA.t) (i : SB.t) (y : B.t),
        SB.In y (SA.fold step s i) <->
        SB.In y i \/ exists e, SA.In e s /\ SB.In y (h e).
  Proof.
    intros step h Hstep s i y.
    rewrite SA.fold_spec, (in_fold_list step h Hstep).
    split.
    - intros [Hi | [e [He Hh]]]; [left; exact Hi |].
      right; exists e; split; [apply elements_in in He; exact He | exact Hh].
    - intros [Hi | [e [He Hh]]]; [left; exact Hi |].
      right; exists e; split; [apply elements_in; exact He | exact Hh].
  Qed.

  Lemma in_fold_add :
    forall (mk : A.t -> B.t) (s : SA.t) (i : SB.t) (y : B.t),
      SB.In y (SA.fold (fun x acc => SB.add (mk x) acc) s i) <->
      SB.In y i \/ exists x, SA.In x s /\ y = mk x.
  Proof.
    intros mk s i y.
    rewrite (in_fold _ (fun x => SB.singleton (mk x)))
      by (intros ? ? ?; rewrite add_in, singleton_in; tauto).
    setoid_rewrite singleton_in; reflexivity.
  Qed.

  (* Tactic-level matching on fold guards is brittle when pair components
     elaborate at definitionally-equal but distinct types; abstracting the
     guard and payload keeps every match on [g x] instead. *)
  Lemma in_guarded_fold :
    forall (g : A.t -> bool) (mk : A.t -> B.t) (s : SA.t) (i : SB.t) (y : B.t),
      SB.In y
        (SA.fold (fun x acc => if g x then SB.add (mk x) acc else acc) s i)
      <->
      SB.In y i \/ exists x, SA.In x s /\ g x = true /\ y = mk x.
  Proof.
    intros g mk s i y.
    rewrite (in_fold _
      (fun x => if g x then SB.singleton (mk x) else SB.empty)).
    2:{ intros x a y0; destruct (g x).
        - rewrite add_in, singleton_in; tauto.
        - split; [tauto | intros [H | H];
            [exfalso; exact (empty_in _ H) | exact H]]. }
    split.
    - intros [H | [x [Hx Hy]]]; [left; exact H | right].
      destruct (g x) eqn:Hg; [| exfalso; exact (empty_in _ Hy)].
      apply singleton_in in Hy.
      exists x; repeat split; assumption.
    - intros [H | [x [Hx [Hg ->]]]]; [left; exact H | right].
      exists x; rewrite Hg.
      split; [exact Hx | exact (proj2 (singleton_in _ _) eq_refl)].
  Qed.

  (* The comprehensions go through ofList/unions rather than a fold of add or
     union, so that each builds its result with one merge sort instead of n
     quadratic insertions; the specs are extensional, so nothing downstream
     sees the change. *)
  Definition map (f : A.t -> B.t) (s : SA.t) : SB.t :=
    ofList (List.map f (SA.elements s)).

  (* The witness is annotated at A.t rather than left to unify at SA.elt:
     tactics downstream build the witness out of pieces typed at A.t, and the
     two spellings, though convertible, are not syntactically equal, so
     destruct/rewrite would miss the occurrence. *)
  Lemma mem_map : forall f s y,
      SB.In y (map f s) <-> exists x : A.t, SA.In x s /\ y = f x.
  Proof.
    intros f s y; unfold map; rewrite mem_ofList, List.in_map_iff.
    split.
    - intros [x [Hf Hx]]; exists x;
        split; [apply elements_in; exact Hx | symmetry; exact Hf].
    - intros [x [Hx Hy]]; exists x;
        split; [symmetry; exact Hy | apply elements_in; exact Hx].
  Qed.

  (* Containment transfers through each combinator pointwise, so callers do
     not have to round-trip through the mem_ characterisations and name the
     witness a second time. *)
  Lemma map_mono : forall (f g : A.t -> B.t) (s s' : SA.t),
      SA.Subset s s' -> (forall x, f x = g x) ->
      SB.Subset (map f s) (map g s').
  Proof.
    intros f g s s' Hs Hfg y Hy; apply mem_map in Hy.
    destruct Hy as [x [Hx ->]]; apply mem_map.
    exists x; split; [exact (Hs _ Hx) | exact (Hfg x)].
  Qed.

  Definition filterMap (f : A.t -> option B.t) (s : SA.t) : SB.t :=
    ofList (List.flat_map
              (fun x => match f x with Some y => y :: nil | None => nil end)
              (SA.elements s)).

  Lemma mem_filterMap : forall f s y,
      SB.In y (filterMap f s) <-> exists x : A.t, SA.In x s /\ f x = Some y.
  Proof.
    intros f s y; unfold filterMap; rewrite mem_ofList, List.in_flat_map.
    split; intros [x [Hx Hy]]; exists x.
    - apply elements_in in Hx; split; [exact Hx |].
      destruct (f x) as [z | ];
        [destruct Hy as [-> | []]; reflexivity | destruct Hy].
    - split; [apply elements_in; exact Hx | rewrite Hy; left; reflexivity].
  Qed.

  Lemma filterMap_mono : forall (f g : A.t -> option B.t) (s s' : SA.t),
      SA.Subset s s' -> (forall x y, f x = Some y -> g x = Some y) ->
      SB.Subset (filterMap f s) (filterMap g s').
  Proof.
    intros f g s s' Hs Hfg y Hy; apply mem_filterMap in Hy.
    destruct Hy as [x [Hx Hf]]; apply mem_filterMap.
    exists x; split; [exact (Hs _ Hx) | exact (Hfg _ _ Hf)].
  Qed.

  Definition unionMap (f : A.t -> SB.t) (s : SA.t) : SB.t :=
    unions (List.map f (SA.elements s)).

  Lemma mem_unionMap : forall f s y,
      SB.In y (unionMap f s) <-> exists x : A.t, SA.In x s /\ SB.In y (f x).
  Proof.
    intros f s y; unfold unionMap; rewrite mem_unions.
    split.
    - intros [t [Ht Hy]]; apply List.in_map_iff in Ht;
        destruct Ht as [x [<- Hx]].
      exists x; split; [apply elements_in; exact Hx | exact Hy].
    - intros [x [Hx Hy]]; exists (f x); split; [| exact Hy].
      apply List.in_map_iff; exists x;
        split; [reflexivity | apply elements_in; exact Hx].
  Qed.

  Lemma unionMap_mono : forall (f g : A.t -> SB.t) (s s' : SA.t),
      SA.Subset s s' -> (forall x, SB.Subset (f x) (g x)) ->
      SB.Subset (unionMap f s) (unionMap g s').
  Proof.
    intros f g s s' Hs Hfg y Hy; apply mem_unionMap in Hy.
    destruct Hy as [x [Hx Hf]]; apply mem_unionMap.
    exists x; split; [exact (Hs _ Hx) | exact (Hfg _ _ Hf)].
  Qed.

  Definition filterExists (p : A.t -> B.t -> bool) (s2 : SB.t) (s1 : SA.t)
      : SA.t :=
    SA.filter (fun x => SB.exists_ (p x) s2) s1.

  Lemma mem_filterExists : forall p s2 s1 (x : A.t),
      SA.In x (filterExists p s2 s1) <->
      SA.In x s1 /\ exists y : B.t, SB.In y s2 /\ p x y = true.
  Proof.
    intros p s2 s1 x; unfold filterExists.
    rewrite SSA.filter_spec', SSB.exists_spec'; reflexivity.
  Qed.

  (* The combinator half of the restriction kit (SetSpecs holds the mem and
     exists_ halves): dropping source elements that contribute nothing to y
     leaves y's membership alone. *)
  Lemma map_restrict : forall (f : A.t -> B.t) (s s' : SA.t) (y : B.t),
      SA.Subset s' s -> (forall x, SA.In x s -> y = f x -> SA.In x s') ->
      (SB.In y (map f s') <-> SB.In y (map f s)).
  Proof.
    intros f s s' y Hsub Hkeep; rewrite !mem_map; split.
    - intros [x [Hx ->]]; exists x; split; [exact (Hsub _ Hx) | reflexivity].
    - intros [x [Hx Hy]]; exists x; split; [exact (Hkeep _ Hx Hy) | exact Hy].
  Qed.

  Lemma filterMap_restrict : forall (f : A.t -> option B.t) (s s' : SA.t) y,
      SA.Subset s' s -> (forall x, SA.In x s -> f x = Some y -> SA.In x s') ->
      (SB.In y (filterMap f s') <-> SB.In y (filterMap f s)).
  Proof.
    intros f s s' y Hsub Hkeep; rewrite !mem_filterMap; split.
    - intros [x [Hx Hf]]; exists x; split; [exact (Hsub _ Hx) | exact Hf].
    - intros [x [Hx Hf]]; exists x; split; [exact (Hkeep _ Hx Hf) | exact Hf].
  Qed.

  (* Decoders read a set of encoded elements back: an inverse that is defined
     exactly on the image of an embedding turns filterMap into a membership
     test against the embedding, and makes the embedding injective for free. *)
  Section PartialInverse.
    Variables (inv : A.t -> option B.t) (emb : B.t -> A.t).
    Hypothesis inv_emb : forall b, inv (emb b) = Some b.
    Hypothesis inv_sound : forall a b, inv a = Some b -> emb b = a.

    Lemma mem_filterMap_inv : forall (s : SA.t) (b : B.t),
        SB.In b (filterMap inv s) <-> SA.In (emb b) s.
    Proof.
      intros s b; rewrite mem_filterMap; split.
      - intros [a [Ha Hf]]; rewrite (inv_sound _ _ Hf); exact Ha.
      - intro H; exists (emb b); split; [exact H | apply inv_emb].
    Qed.

    Lemma emb_injective : forall b b', emb b = emb b' -> b = b'.
    Proof.
      intros b b' H.
      assert (Some b = Some b') as E by (rewrite <- !inv_emb, H; reflexivity).
      injection E as ->; reflexivity.
    Qed.
  End PartialInverse.

  Lemma mem_map_inj : forall (f : A.t -> B.t) (s : SA.t) (x : A.t),
      (forall x y, f x = f y -> x = y) ->
      (SB.In (f x) (map f s) <-> SA.In x s).
  Proof.
    intros f s x Hinj; rewrite mem_map; split.
    - intros [z [Hz Hf]]; rewrite (Hinj _ _ Hf); exact Hz.
    - intro H; exists x; split; [exact H | reflexivity].
  Qed.

  Lemma unionMap_restrict : forall (f : A.t -> SB.t) (s s' : SA.t) y,
      SA.Subset s' s ->
      (forall x, SA.In x s -> SB.In y (f x) -> SA.In x s') ->
      (SB.In y (unionMap f s') <-> SB.In y (unionMap f s)).
  Proof.
    intros f s s' y Hsub Hkeep; rewrite !mem_unionMap; split.
    - intros [x [Hx Hf]]; exists x; split; [exact (Hsub _ Hx) | exact Hf].
    - intros [x [Hx Hf]]; exists x; split; [exact (Hkeep _ Hx Hf) | exact Hf].
  Qed.
End SetOps.
