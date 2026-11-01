From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_cplx.
Create Rewrite HintDb cmp_cplx.

Module Complexity (N V : UsualOrderedType) (X : UsualOrderedType).
  Module Source := Core N V.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.

  Definition LitSat {A : Type} (sigma : A -> bool) (l : A * bool) : Prop :=
    sigma (fst l) = snd l.

  Definition ClauseSat {A : Type} (sigma : A -> bool) (c : list (A * bool))
    : Prop :=
    exists l, List.In l c /\ LitSat sigma l.

  Definition CnfSat {A : Type} (sigma : A -> bool)
      (cs : list (list (A * bool))) : Prop :=
    forall c, List.In c cs -> ClauseSat sigma c.

  Module LiteralOT := PairUOT X BoolOT.
  Module ClauseOT := TripleUOT LiteralOT LiteralOT LiteralOT.

  Definition lits (c : ClauseOT.t) : list LiteralOT.t :=
    fst c :: fst (snd c) :: snd (snd c) :: nil.

  Definition cnf (cs : list ClauseOT.t) : list (list LiteralOT.t) :=
    List.map lits cs.

  Module Encoding.
    Module VF := UOTCompareFacts V.
    Module SOp := SetOps Package Package PackageSet PackageSet.
    Module SOv := SetOps V V VSet VSet.
    Module SOd := SetOps Source.DependencyElt Source.DependencyElt Source.DependencyRel Source.DependencyRel.

    Definition ltb (v v' : V.t) : bool :=
      match V.compare v v' with Lt => true | _ => false end.

    Lemma ltb_lt : forall v v', ltb v v' = true <-> V.lt v v'.
    Proof.
      intros v v'; unfold ltb; rewrite <- VF.Facts.compare_lt_iff.
      destruct (V.compare v v'); split; intro H; congruence.
    Qed.

    Definition depClause (R : PackageSet.t) (p : Package.t) (n : N.t) (vs : VSet.t)
      : list (Package.t * bool) :=
      (p, false) ::
      List.map (fun v => ((n, v), true))
        (List.filter (fun v => PackageSet.mem (n, v) R) (VSet.elements vs)).

    Definition depClauses (R : PackageSet.t) (D : Source.DependencyRel.t)
      : list (list (Package.t * bool)) :=
      List.map (fun '(p, (n, vs)) => depClause R p n vs) (Source.DependencyRel.elements D).

    Definition uniqueClauses (R : PackageSet.t) : list (list (Package.t * bool)) :=
      List.flat_map
        (fun p =>
           List.map (fun v' => (p, false) :: ((fst p, v'), false) :: nil)
             (List.filter (ltb (snd p))
                (VSet.elements (Source.versions R (fst p)))))
        (PackageSet.elements R).

    Definition satEncoding (R : PackageSet.t) (D : Source.DependencyRel.t) (r : Package.t)
      : list (list (Package.t * bool)) :=
      ((r, true) :: nil) :: depClauses R D ++ uniqueClauses R.

    Lemma in_depClauses : forall R D c,
        List.In c (depClauses R D) <->
        exists p n vs, Source.DependencyRel.In (p, (n, vs)) D /\ c = depClause R p n vs.
    Proof.
      intros R D c; unfold depClauses; rewrite List.in_map_iff.
      split.
      - intros [[p [n vs]] [Hc HD]]; cbn beta iota in Hc.
        exists p, n, vs; split; [apply SOd.elements_in; exact HD
                                | symmetry; exact Hc].
      - intros [p [n [vs [HD ->]]]].
        exists (p, (n, vs)); split; [reflexivity | apply SOd.elements_in; exact HD].
    Qed.

    Lemma in_depClause_pos : forall R p n vs (v : V.t),
        List.In ((n, v), true) (depClause R p n vs) <->
        VSet.In v vs /\ PackageSet.In (n, v) R.
    Proof.
      intros R p n vs v; unfold depClause; cbn [List.In].
      rewrite List.in_map_iff.
      split.
      - intros [E | [v' [E Hv']]]; [discriminate E |].
        injection E as <-.
        apply List.filter_In in Hv'; destruct Hv' as [Hv' HR].
        split; [apply SOv.elements_in; exact Hv' | apply PackageSet.mem_spec; exact HR].
      - intros [Hv HR]; right; exists v; split; [reflexivity |].
        apply List.filter_In; split;
          [apply SOv.elements_in; exact Hv | apply PackageSet.mem_spec; exact HR].
    Qed.

    Lemma in_uniqueClauses : forall R c,
        List.In c (uniqueClauses R) <->
        exists n v v', PackageSet.In (n, v) R /\ PackageSet.In (n, v') R /\
          V.lt v v' /\ c = ((n, v), false) :: ((n, v'), false) :: nil.
    Proof.
      intros R c; unfold uniqueClauses; rewrite List.in_flat_map.
      split.
      - intros [[n v] [Hp Hc]]; apply List.in_map_iff in Hc.
        destruct Hc as [v' [<- Hv']]; cbn [fst snd] in Hv' |- *.
        apply List.filter_In in Hv'; destruct Hv' as [Hv' Hlt].
        apply SOv.elements_in, Source.mem_versions in Hv'.
        exists n, v, v'.
        split; [apply SOp.elements_in; exact Hp |].
        split; [exact Hv' |].
        split; [apply ltb_lt; exact Hlt | reflexivity].
      - intros [n [v [v' [Hv [Hv' [Hlt ->]]]]]].
        exists (n, v); split; [apply SOp.elements_in; exact Hv |].
        apply List.in_map_iff; exists v'; split; [reflexivity |].
        apply List.filter_In; split;
          [apply SOv.elements_in, Source.mem_versions; exact Hv'
          | apply ltb_lt; exact Hlt].
    Qed.

    Theorem sat_encoding_soundness : forall R D r (sigma : Package.t -> bool),
        PackageSet.In r R ->
        CnfSat sigma (satEncoding R D r) ->
        Source.IsResolution R D r (PackageSet.filter sigma R).
    Proof.
      intros R D r sigma Hr Hsat.
      assert (Hin : forall p, PackageSet.In p (PackageSet.filter sigma R) <->
                              PackageSet.In p R /\ sigma p = true)
        by (intro p; apply PackageSet.filter_spec').
      assert (Huc : forall n v v', PackageSet.In (n, v) R -> PackageSet.In (n, v') R ->
                      V.lt v v' ->
                      sigma (n, v) = false \/ sigma (n, v') = false).
      { intros n v v' Hv Hv' Hlt.
        destruct (Hsat (((n, v), false) :: ((n, v'), false) :: nil))
          as [l [Hl Hls]].
        { right; apply List.in_or_app; right.
          apply in_uniqueClauses; exists n, v, v'; auto. }
        destruct Hl as [<- | [<- | []]]; [left | right]; exact Hls. }
      constructor.
      - intros p Hp; apply Hin in Hp; exact (proj1 Hp).
      - apply Hin; split; [exact Hr |].
        destruct (Hsat ((r, true) :: nil)) as [l [[<- | []] Hl]];
          [left; reflexivity | exact Hl].
      - intros p Hp n vs HD; apply Hin in Hp; destruct Hp as [_ Hps].
        destruct (Hsat (depClause R p n vs)) as [[q b] [Hl Hls]].
        { right; apply List.in_or_app; left.
          apply in_depClauses; exists p, n, vs; auto. }
        unfold LitSat in Hls; cbn [fst snd] in Hls.
        destruct Hl as [E | Hl].
        + injection E as <- <-; congruence.
        + apply List.in_map_iff in Hl; destruct Hl as [v [E Hv]].
          injection E as <- <-.
          apply List.filter_In in Hv; destruct Hv as [Hv HR].
          exists v; split; [apply SOv.elements_in; exact Hv |].
          apply Hin; split; [apply PackageSet.mem_spec; exact HR | exact Hls].
      - intros n v v' Hv Hv'; apply Hin in Hv, Hv'.
        destruct Hv as [HvR Hvs], Hv' as [Hv'R Hv's].
        destruct (V.compare_spec v v') as [E | L | G]; [exact E | |];
          exfalso.
        + destruct (Huc n v v' HvR Hv'R L); congruence.
        + destruct (Huc n v' v Hv'R HvR G); congruence.
    Qed.

    Theorem sat_encoding_completeness : forall R D r S,
        Source.IsResolution R D r S ->
        CnfSat (fun p => PackageSet.mem p S) (satEncoding R D r).
    Proof.
      intros R D r S [Hsub Hroot Hdep Huniq] c Hc.
      destruct Hc as [<- | Hc].
      - exists (r, true); split; [left; reflexivity |].
        apply PackageSet.mem_spec; exact Hroot.
      - apply List.in_app_or in Hc; destruct Hc as [Hc | Hc].
        + apply in_depClauses in Hc; destruct Hc as [p [n [vs [HD ->]]]].
          destruct (PackageSet.mem p S) eqn:Ep.
          * apply PackageSet.mem_spec in Ep.
            destruct (Hdep p Ep n vs HD) as [v [Hv HvS]].
            exists ((n, v), true); split.
            -- apply in_depClause_pos; split; [exact Hv | apply Hsub; exact HvS].
            -- apply PackageSet.mem_spec; exact HvS.
          * exists (p, false); split; [left; reflexivity | exact Ep].
        + apply in_uniqueClauses in Hc.
          destruct Hc as [n [v [v' [_ [_ [Hlt ->]]]]]].
          destruct (PackageSet.mem (n, v) S) eqn:E1;
            [destruct (PackageSet.mem (n, v') S) eqn:E2 |].
          * exfalso; apply PackageSet.mem_spec in E1, E2.
            rewrite (Huniq n v v' E1 E2) in Hlt.
            exact (StrictOrder_Irreflexive v' Hlt).
          * exists ((n, v'), false); split;
              [right; left; reflexivity | exact E2].
          * exists ((n, v), false); split; [left; reflexivity | exact E1].
    Qed.
  End Encoding.

  Module Reduction.
    Module XF := UOTCompareFacts X.
    Module BF := UOTCompareFacts BoolOT.
    Module LF := UOTCompareFacts LiteralOT.
    Module CF := UOTCompareFacts ClauseOT.
    #[local] Hint Rewrite XF.compare_eq_iff BF.compare_eq_iff LF.compare_eq_iff
      CF.compare_eq_iff : cmp_cplx.
    #[local] Hint Extern 1 => cmp_by XF.compare_antisym : cmp_cplx.
    #[local] Hint Extern 1 => cmp_by XF.compare_lt_trans : cmp_cplx.
    #[local] Hint Extern 1 => cmp_by BF.compare_antisym : cmp_cplx.
    #[local] Hint Extern 1 => cmp_by BF.compare_lt_trans : cmp_cplx.
    #[local] Hint Extern 1 => cmp_by LF.compare_antisym : cmp_cplx.
    #[local] Hint Extern 1 => cmp_by LF.compare_lt_trans : cmp_cplx.
    #[local] Hint Extern 1 => cmp_by CF.compare_antisym : cmp_cplx.
    #[local] Hint Extern 1 => cmp_by CF.compare_lt_trans : cmp_cplx.

    Module Name.
      Inductive name : Type :=
      | Root
      | Var (x : X.t)
      | Clause (c : ClauseOT.t).
      Definition t := name.

      Definition rank (x : t) : nat :=
        match x with Root => 0 | Var _ => 1 | Clause _ => 2 end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq => match x, y with
                | Var a, Var b => X.compare a b
                | Clause a, Clause b => ClauseOT.compare a b
                | _, _ => Eq
                end
        | c => c
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_cplx. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_cplx. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_cplx. Qed.
    End Name.

    Module Version.
      Inductive version : Type :=
      | Eps
      | Truth (b : bool)
      | Lit (l : LiteralOT.t).
      Definition t := version.

      Definition rank (x : t) : nat :=
        match x with Eps => 0 | Truth _ => 1 | Lit _ => 2 end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq => match x, y with
                | Truth a, Truth b => BoolOT.compare a b
                | Lit a, Lit b => LiteralOT.compare a b
                | _, _ => Eq
                end
        | c => c
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_cplx. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_cplx. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_cplx. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module Reduced := Core NameOT VersionOT.

    Definition root : Reduced.Package.t := (Name.Root, Version.Eps).

    Definition clauseReal (c : ClauseOT.t) : list Reduced.Package.t :=
      List.flat_map
        (fun l => (Name.Var (fst l), Version.Truth true) ::
                  (Name.Var (fst l), Version.Truth false) ::
                  (Name.Clause c, Version.Lit l) :: nil)
        (lits c).

    Definition reduceReal (cs : list ClauseOT.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.ofList (root :: List.flat_map clauseReal cs).

    Definition litVersions (c : ClauseOT.t) : Reduced.VSet.t :=
      Reduced.VSet.ofList (List.map Version.Lit (lits c)).

    Definition clauseDeps (c : ClauseOT.t) : list Reduced.DependencyElt.t :=
      (root, (Name.Clause c, litVersions c)) ::
      List.map
        (fun l => ((Name.Clause c, Version.Lit l),
                   (Name.Var (fst l), Reduced.VSet.singleton (Version.Truth (snd l)))))
        (lits c).

    Definition reduceDeps (cs : list ClauseOT.t) : Reduced.DependencyRel.t :=
      Reduced.DependencyRel.ofList (List.flat_map clauseDeps cs).

    Lemma mem_reduceReal : forall cs (p : Reduced.Package.t),
        Reduced.PackageSet.In p (reduceReal cs) <->
        p = root \/
        exists c l, List.In c cs /\ List.In l (lits c) /\
          ((exists b, p = (Name.Var (fst l), Version.Truth b)) \/
           p = (Name.Clause c, Version.Lit l)).
    Proof.
      intros cs p; unfold reduceReal.
      rewrite Reduced.PackageSet.mem_ofList; cbn [List.In]; rewrite List.in_flat_map.
      split.
      - intros [<- | [c [Hc Hy]]]; [left; reflexivity | right].
        unfold clauseReal in Hy; apply List.in_flat_map in Hy.
        destruct Hy as [l [Hl Hy]].
        exists c, l; split; [exact Hc | split; [exact Hl |]].
        destruct Hy as [<- | [<- | [<- | []]]];
          [left; exists true | left; exists false | right]; reflexivity.
      - intros [-> | [c [l [Hc [Hl Hy]]]]]; [left; reflexivity | right].
        exists c; split; [exact Hc |].
        unfold clauseReal; apply List.in_flat_map; exists l.
        split; [exact Hl |].
        destruct Hy as [[[|] ->] | ->]; cbn [List.In]; tauto.
    Qed.

    Lemma mem_litVersions : forall c v,
        Reduced.VSet.In v (litVersions c) <->
        exists l, List.In l (lits c) /\ v = Version.Lit l.
    Proof.
      intros c v; unfold litVersions.
      rewrite Reduced.VSet.mem_ofList, List.in_map_iff.
      split; intros [l [H1 H2]]; exists l; split; auto.
    Qed.

    Lemma mem_reduceDeps : forall cs (e : Reduced.DependencyElt.t),
        Reduced.DependencyRel.In e (reduceDeps cs) <->
        exists c, List.In c cs /\
          (e = (root, (Name.Clause c, litVersions c)) \/
           exists l, List.In l (lits c) /\
             e = ((Name.Clause c, Version.Lit l),
                  (Name.Var (fst l),
                   Reduced.VSet.singleton (Version.Truth (snd l))))).
    Proof.
      intros cs e; unfold reduceDeps.
      rewrite Reduced.DependencyRel.mem_ofList, List.in_flat_map.
      split.
      - intros [c [Hc He]]; exists c; split; [exact Hc |].
        unfold clauseDeps in He; destruct He as [<- | He]; [left; reflexivity |].
        right; apply List.in_map_iff in He; destruct He as [l [<- Hl]].
        exists l; split; [exact Hl | reflexivity].
      - intros [c [Hc He]]; exists c; split; [exact Hc |].
        unfold clauseDeps; destruct He as [-> | [l [Hl ->]]];
          [left; reflexivity |].
        right; apply List.in_map_iff; exists l; split; [reflexivity | exact Hl].
    Qed.

    Theorem reduceDeps_functionalInName : forall cs,
        Reduced.FunctionalInName (reduceDeps cs).
    Proof.
      intros cs p n vs1 vs2 H1 H2; apply mem_reduceDeps in H1, H2.
      unfold root in *.
      destruct H1 as [c1 [_ [E1 | [l1 [_ E1]]]]],
               H2 as [c2 [_ [E2 | [l2 [_ E2]]]]];
        congruence.
    Qed.

    Definition assignment (S : Reduced.PackageSet.t) (x : X.t) : bool :=
      Reduced.PackageSet.mem (Name.Var x, Version.Truth true) S.

    Lemma assignment_spec : forall S x b,
        Reduced.VersionUnique S -> Reduced.PackageSet.In (Name.Var x, Version.Truth b) S ->
        assignment S x = b.
    Proof.
      intros S x b Huniq Hin; unfold assignment.
      destruct b; [apply Reduced.PackageSet.mem_spec; exact Hin |].
      destruct (Reduced.PackageSet.mem (Name.Var x, Version.Truth true) S) eqn:E;
        [| reflexivity].
      apply Reduced.PackageSet.mem_spec in E.
      discriminate (Huniq _ _ _ E Hin).
    Qed.

    Theorem three_sat_soundness : forall cs S,
        Reduced.IsResolution (reduceReal cs) (reduceDeps cs) root S ->
        CnfSat (assignment S) (cnf cs).
    Proof.
      intros cs S [_ Hroot Hdep Huniq] c Hc.
      unfold cnf in Hc; apply List.in_map_iff in Hc.
      destruct Hc as [c0 [<- Hc0]].
      destruct (Hdep _ Hroot (Name.Clause c0) (litVersions c0)) as [w [Hw HwS]].
      { apply mem_reduceDeps; exists c0; split; [exact Hc0 | left; reflexivity]. }
      apply mem_litVersions in Hw; destruct Hw as [l [Hl ->]].
      destruct (Hdep _ HwS (Name.Var (fst l))
                  (Reduced.VSet.singleton (Version.Truth (snd l))))
        as [w [Hw HwS']].
      { apply mem_reduceDeps; exists c0; split; [exact Hc0 |].
        right; exists l; split; [exact Hl | reflexivity]. }
      apply Reduced.VSet.singleton_spec in Hw; subst w.
      exists l; split; [exact Hl |].
      apply assignment_spec; assumption.
    Qed.

    Definition litSatb (sigma : X.t -> bool) (l : LiteralOT.t) : bool :=
      Bool.eqb (sigma (fst l)) (snd l).

    Definition firstSatisfied (sigma : X.t -> bool) (c : ClauseOT.t)
      : LiteralOT.t :=
      if litSatb sigma (fst c) then fst c
      else if litSatb sigma (fst (snd c)) then fst (snd c)
      else snd (snd c).

    Lemma firstSatisfied_in : forall sigma c,
        List.In (firstSatisfied sigma c) (lits c).
    Proof.
      intros sigma c; unfold firstSatisfied, lits.
      destruct (litSatb sigma (fst c)); [left; reflexivity |].
      destruct (litSatb sigma (fst (snd c))); cbn [List.In]; tauto.
    Qed.

    Lemma litSatb_true : forall sigma l,
        litSatb sigma l = true <-> LitSat sigma l.
    Proof. intros sigma l; unfold litSatb, LitSat; apply Bool.eqb_true_iff. Qed.

    Lemma firstSatisfied_sat : forall sigma c,
        ClauseSat sigma (lits c) -> LitSat sigma (firstSatisfied sigma c).
    Proof.
      intros sigma c [l [Hl Hs]]; unfold firstSatisfied.
      destruct (litSatb sigma (fst c)) eqn:E1;
        [apply litSatb_true; exact E1 |].
      destruct (litSatb sigma (fst (snd c))) eqn:E2;
        [apply litSatb_true; exact E2 |].
      unfold lits in Hl; destruct Hl as [<- | [<- | [<- | []]]];
        [apply litSatb_true in Hs; congruence
        | apply litSatb_true in Hs; congruence
        | exact Hs].
    Qed.

    Definition coreResolution (cs : list ClauseOT.t) (sigma : X.t -> bool)
      : Reduced.PackageSet.t :=
      Reduced.PackageSet.ofList
        (root ::
         List.flat_map
           (fun c => (Name.Clause c, Version.Lit (firstSatisfied sigma c)) ::
                     List.map
                       (fun l => (Name.Var (fst l),
                                  Version.Truth (sigma (fst l))))
                       (lits c))
           cs).

    Lemma mem_coreResolution : forall sigma cs (p : Reduced.Package.t),
        Reduced.PackageSet.In p (coreResolution cs sigma) <->
        p = root \/
        exists c, List.In c cs /\
          (p = (Name.Clause c, Version.Lit (firstSatisfied sigma c)) \/
           exists l, List.In l (lits c) /\
             p = (Name.Var (fst l), Version.Truth (sigma (fst l)))).
    Proof.
      intros sigma cs p; unfold coreResolution.
      rewrite Reduced.PackageSet.mem_ofList; cbn [List.In]; rewrite List.in_flat_map.
      split.
      - intros [<- | [c [Hc Hy]]]; [left; reflexivity | right].
        exists c; split; [exact Hc |].
        destruct Hy as [<- | Hy]; [left; reflexivity | right].
        apply List.in_map_iff in Hy; destruct Hy as [l [<- Hl]].
        exists l; split; [exact Hl | reflexivity].
      - intros [-> | [c [Hc Hy]]]; [left; reflexivity | right].
        exists c; split; [exact Hc |].
        destruct Hy as [-> | [l [Hl ->]]]; [left; reflexivity | right].
        apply List.in_map_iff; exists l; split; [reflexivity | exact Hl].
    Qed.

    Theorem three_sat_completeness : forall cs sigma,
        CnfSat sigma (cnf cs) ->
        Reduced.IsResolution (reduceReal cs) (reduceDeps cs) root
          (coreResolution cs sigma).
    Proof.
      intros cs sigma Hsat; constructor.
      - intros p Hy; apply mem_coreResolution in Hy; apply mem_reduceReal.
        destruct Hy as [-> | [c [Hc [-> | [l [Hl ->]]]]]];
          [left; reflexivity | right | right].
        + exists c, (firstSatisfied sigma c).
          split; [exact Hc | split; [apply firstSatisfied_in | right; reflexivity]].
        + exists c, l; split; [exact Hc | split; [exact Hl |]].
          left; exists (sigma (fst l)); reflexivity.
      - apply mem_coreResolution; left; reflexivity.
      - intros p Hp n vs Hd; apply mem_reduceDeps in Hd.
        destruct Hd as [c [Hc [E | [l [Hl E]]]]]; injection E as -> -> ->.
        + exists (Version.Lit (firstSatisfied sigma c)); split.
          * apply mem_litVersions; exists (firstSatisfied sigma c).
            split; [apply firstSatisfied_in | reflexivity].
          * apply mem_coreResolution; right; exists c.
            split; [exact Hc | left; reflexivity].
        + apply mem_coreResolution in Hp; unfold root in Hp.
          destruct Hp as [E | [c' [_ [E | [l' [_ E]]]]]]; try discriminate E.
          injection E as <- El.
          assert (Hs : LitSat sigma l).
          { rewrite El; apply firstSatisfied_sat, Hsat.
            unfold cnf; apply List.in_map; exact Hc. }
          exists (Version.Truth (snd l)).
          split; [apply Reduced.VSet.singleton_spec; reflexivity |].
          apply mem_coreResolution; right; exists c; split; [exact Hc |].
          right; exists l; split; [exact Hl |].
          assert (Et : Version.Truth (sigma (fst l)) = Version.Truth (snd l))
            by (f_equal; exact Hs).
          rewrite Et; reflexivity.
      - intros n v v' Hv Hv'; apply mem_coreResolution in Hv, Hv'.
        unfold root in *.
        destruct Hv as [E | [c [_ [E | [l [_ E]]]]]],
                 Hv' as [E' | [c' [_ [E' | [l' [_ E']]]]]];
          congruence.
    Qed.

    Theorem three_sat_correct : forall cs,
        (exists sigma, CnfSat sigma (cnf cs)) <->
        exists S, Reduced.IsResolution (reduceReal cs) (reduceDeps cs) root S.
    Proof.
      intro cs; split.
      - intros [sigma Hs]; exists (coreResolution cs sigma).
        exact (three_sat_completeness cs sigma Hs).
      - intros [S HS]; exists (assignment S).
        exact (three_sat_soundness cs S HS).
    Qed.
  End Reduction.
End Complexity.
