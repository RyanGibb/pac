From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude.

(* Module application is generative: two instantiations of Core at equal
   parameters have incompatible types. Instantiate once and share. *)
Module Core (N V : UsualOrderedType).
  Module Pkg := PairUOT N V.
  Module PkgSet := FSetUOT Pkg.
  Module VSet := FSetUOT V.
  Module Dependees := PairUOT N VSet.AsUOT.
  Module DependeesSet := FSetUOT Dependees.
  Module DepElt := PairUOT Pkg Dependees.
  Module DepRel := FSetUOT DepElt.

  Definition dependees (D : DepRel.t) (p : Pkg.t) : DependeesSet.t :=
    DepRel.fold (fun '(q, h) acc =>
        if Pkg.eq_dec q p then DependeesSet.add h acc else acc)
      D DependeesSet.empty.

  Module SOdh := SetOps DepElt Dependees DepRel DependeesSet.
  Lemma mem_dependees : forall D (p : Pkg.t) (h : Dependees.t),
      DependeesSet.In h (dependees D p) <-> DepRel.In (p, h) D.
  Proof.
    intros D p h; unfold dependees.
    rewrite (SOdh.in_fold _
      (fun e => if Pkg.eq_dec (fst e) p
                then DependeesSet.singleton (snd e) else DependeesSet.empty)).
    2:{ intros [q d] a y; simpl.
        destruct (Pkg.eq_dec q p).
        - rewrite SOdh.add_in, SOdh.singleton_in; tauto.
        - split; [tauto | intros [H | H];
            [exfalso; exact (SOdh.empty_in _ H) | exact H]]. }
    split.
    - intros [H | [e [HeD He]]].
      + exfalso; exact (SOdh.empty_in _ H).
      + destruct e as [q d]; simpl in He.
        destruct (Pkg.eq_dec q p) as [-> | NE].
        * rewrite SOdh.singleton_in in He; subst d; exact HeD.
        * exfalso; exact (SOdh.empty_in _ He).
    - intro H; right; exists (p, h); split; [exact H | simpl].
      destruct (Pkg.eq_dec p p) as [_ | NE];
        [rewrite SOdh.singleton_in; reflexivity
        | contradiction NE; reflexivity].
  Qed.

  (* The lookup theorems all compare two dependees computations at one
     package, and the empty-dependees ones deny every edge out of it. *)
  Lemma dependees_ext : forall D D' (p : Pkg.t),
      (forall h, DepRel.In (p, h) D <-> DepRel.In (p, h) D') ->
      dependees D p = dependees D' p.
  Proof.
    intros D D' p H; apply DependeesSet.ext; intro h.
    rewrite !mem_dependees; exact (H h).
  Qed.

  Lemma dependees_empty_iff : forall D (p : Pkg.t),
      dependees D p = DependeesSet.empty <->
      forall h, ~ DepRel.In (p, h) D.
  Proof.
    intros D p; split.
    - intros He h Hin; rewrite <- mem_dependees, He in Hin.
      exact (DependeesSet.empty_spec Hin).
    - intro H; apply DependeesSet.ext; intro h.
      rewrite mem_dependees; split;
        [intro Hin; destruct (H h Hin) | intro Hin;
         destruct (DependeesSet.empty_spec Hin)].
  Qed.

  Definition VersionUnique (S : PkgSet.t) : Prop :=
    forall (n : N.t) (v v' : V.t),
      PkgSet.In (n, v) S -> PkgSet.In (n, v') S -> v = v'.

  Definition FunctionalInName (D : DepRel.t) : Prop :=
    forall (p : Pkg.t) (n : N.t) (vs1 vs2 : VSet.t),
      DepRel.In (p, (n, vs1)) D -> DepRel.In (p, (n, vs2)) D -> vs1 = vs2.

  Record IsResolution
      (R : PkgSet.t) (D : DepRel.t) (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_dep_closure :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          DepRel.In (p, (n, vs)) D ->
          exists v, VSet.In v vs /\ PkgSet.In (n, v) S
    ; res_version_unique : VersionUnique S }.
End Core.
