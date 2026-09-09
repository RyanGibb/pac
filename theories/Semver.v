From Stdlib Require Import MSets List Bool.
From PackageCalculus Require Import Prelude Versions.

(* The semver range language, shared by every ecosystem that resolves by
   node-semver's rules.  npm writes || alternatives and cargo writes one
   comma-separated conjunction, but both desugar to the same comparator
   sets under the same prerelease admission rule, so the syntax and its
   evaluation are stated once rather than once per ecosystem. *)

(* The prerelease admission rule is not expressible through V.compare:
   whether a prerelease candidate is admitted depends on the release core
   it shares with a comparator's constant.  Both tests arrive as opaque
   predicates and only ever build version sets, so no laws are demanded
   of them. *)
Module Type SemverMatch (V : UsualOrderedType).
  Parameter isPre : V.t -> bool.
  Parameter sameCore : V.t -> V.t -> bool.
End SemverMatch.

(* The version set is a parameter rather than built here because module
   application is generative: an ecosystem evaluates ranges into the same
   set instance its calculus already uses. *)
Module Semver (V : UsualOrderedType) (VSet : SetsOn V) (PM : SemverMatch V).
  Module VSS := SetSpecs V VSet.
  Module VCF := UOTCompareFacts V.

  (* A range is a disjunction of comparator sets -- npm's || alternatives,
     each an implicit conjunction, of which cargo only ever writes one.
     The nesting is kept rather than flattened into Versions.Formula
     because the prerelease rule below is scoped to one comparator set,
     which a free formula tree cannot say. *)
  Inductive Comparator : Type :=
  | CAny
  | COp (op : CmpOp) (c : V.t).

  Definition CompSet := list Comparator.
  Definition Range := list CompSet.

  Definition compMatch (ct : Comparator) (v : V.t) : bool :=
    match ct with
    | CAny => true
    | COp op c => cmpOpEvalBy V.compare op v c
    end.

  (* node-semver admits a prerelease candidate only when some comparator
     of the same set names a prerelease at the same release core. *)
  Definition csAdmits (cs : CompSet) (v : V.t) : bool :=
    orb (negb (PM.isPre v))
      (existsb (fun ct =>
           match ct with
           | CAny => false
           | COp _ c => andb (PM.isPre c) (PM.sameCore v c)
           end) cs).

  Definition csHolds (cs : CompSet) (v : V.t) : bool :=
    andb (forallb (fun ct => compMatch ct v) cs) (csAdmits cs v).

  Definition rgHolds (rg : Range) (v : V.t) : bool :=
    existsb (fun cs => csHolds cs v) rg.

  Definition rangeEval (rg : Range) (Vn : VSet.t) : VSet.t :=
    VSet.filter (rgHolds rg) Vn.

  Lemma mem_rangeEval : forall rg Vn v,
      VSet.In v (rangeEval rg Vn) <-> VSet.In v Vn /\ rgHolds rg v = true.
  Proof. intros rg Vn v; apply VSS.filter_spec'. Qed.

  (* An ecosystem that keys its dependency rows on the requirement itself
     carries a range inside a set element, which wants an order on the
     syntax; the two list layers take theirs from ListComp. *)
  Module CtComp <: ComparableType.
    Definition t := Comparator.
    Definition rank (ct : t) : nat :=
      match ct with CAny => 0 | COp _ _ => 1 end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | COp o1 c1, COp o2 c2 =>
              lex (OpComp.compare o1 o2) (V.compare c1 c2)
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof.
      intros x y; destruct x as [| o1 c1], y as [| o2 c2]; cbn;
        try (split; intro H; congruence).
      rewrite lex_eq_iff, OpComp.compare_eq_iff, VCF.compare_eq_iff.
      split;
        [intros [-> ->]; reflexivity | intro H; injection H as -> ->; auto].
    Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof.
      intros x y; destruct x as [| o1 c1], y as [| o2 c2]; cbn;
        try reflexivity.
      rewrite lex_opp, OpComp.compare_antisym, VCF.compare_antisym;
        reflexivity.
    Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof.
      intros x y z; destruct x as [| o1 c1], y as [| o2 c2], z as [| o3 c3];
        cbn; intros H1 H2; try congruence.
      exact (lex_lt_trans OpComp.compare_eq_iff
               (OpComp.compare_lt_trans _ _ _) (VCF.compare_lt_trans _ _ _)
               H1 H2).
    Qed.
  End CtComp.
  Module CtOT := UOTFromCompare CtComp.
  Module CsComp := ListComp CtComp.
  Module RgComp := ListComp CsComp.
  Module RangeOT := UOTFromCompare RgComp.
End Semver.
