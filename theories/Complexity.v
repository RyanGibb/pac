From Stdlib Require Import MSets List.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_cplx.
Create Rewrite HintDb cmp_cplx.

Module Complexity (N V : UsualOrderedType) (X : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Definition LitSat {A : Type} (sigma : A -> bool) (l : A * bool) : Prop :=
    sigma (fst l) = snd l.

  Definition ClauseSat {A : Type} (sigma : A -> bool) (c : list (A * bool))
    : Prop :=
    exists l, List.In l c /\ LitSat sigma l.

  Definition CnfSat {A : Type} (sigma : A -> bool)
      (f : list (list (A * bool))) : Prop :=
    forall c, List.In c f -> ClauseSat sigma c.

  Module LitOT := PairUOT X BoolOT.
  Module ClauseOT := TripleUOT LitOT LitOT LitOT.

  Definition lits (c : ClauseOT.t) : list LitOT.t :=
    fst c :: fst (snd c) :: snd (snd c) :: nil.

  Definition cnf (phi : list ClauseOT.t) : list (list LitOT.t) :=
    List.map lits phi.

  Module Encoding.
    Module VF := UOTCompareFacts V.
    Module SOp := SetOps Pkg Pkg PkgSet PkgSet.
    Module SOv := SetOps V V VSet VSet.
    Module SOd := SetOps C.DepElt C.DepElt C.DepRel C.DepRel.

    Definition ltb (v v' : V.t) : bool :=
      match V.compare v v' with Lt => true | _ => false end.

    Lemma ltb_lt : forall v v', ltb v v' = true <-> V.lt v v'.
    Proof.
      intros v v'; unfold ltb; rewrite <- VF.F.compare_lt_iff.
      destruct (V.compare v v'); split; intro H; congruence.
    Qed.

    Definition depClause (R : PkgSet.t) (p : Pkg.t) (n : N.t) (vs : VSet.t)
      : list (Pkg.t * bool) :=
      (p, false) ::
      List.map (fun v => ((n, v), true))
        (List.filter (fun v => PkgSet.mem (n, v) R) (VSet.elements vs)).

    Definition depClauses (R : PkgSet.t) (D : C.DepRel.t)
      : list (list (Pkg.t * bool)) :=
      List.map (fun '(p, (n, vs)) => depClause R p n vs) (C.DepRel.elements D).

    Definition uniqueClauses (R : PkgSet.t) : list (list (Pkg.t * bool)) :=
      List.flat_map
        (fun p =>
           List.map (fun v' => (p, false) :: ((fst p, v'), false) :: nil)
             (List.filter (ltb (snd p))
                (VSet.elements (C.versions R (fst p)))))
        (PkgSet.elements R).

    Definition satEncoding (R : PkgSet.t) (D : C.DepRel.t) (r : Pkg.t)
      : list (list (Pkg.t * bool)) :=
      ((r, true) :: nil) :: depClauses R D ++ uniqueClauses R.

    Lemma in_depClauses : forall R D c,
        List.In c (depClauses R D) <->
        exists p n vs, C.DepRel.In (p, (n, vs)) D /\ c = depClause R p n vs.
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
        VSet.In v vs /\ PkgSet.In (n, v) R.
    Proof.
      intros R p n vs v; unfold depClause; cbn [List.In].
      rewrite List.in_map_iff.
      split.
      - intros [E | [v' [E Hv']]]; [discriminate E |].
        injection E as <-.
        apply List.filter_In in Hv'; destruct Hv' as [Hv' HR].
        split; [apply SOv.elements_in; exact Hv' | apply PkgSet.mem_spec; exact HR].
      - intros [Hv HR]; right; exists v; split; [reflexivity |].
        apply List.filter_In; split;
          [apply SOv.elements_in; exact Hv | apply PkgSet.mem_spec; exact HR].
    Qed.

    Lemma in_uniqueClauses : forall R c,
        List.In c (uniqueClauses R) <->
        exists n v v', PkgSet.In (n, v) R /\ PkgSet.In (n, v') R /\
          V.lt v v' /\ c = ((n, v), false) :: ((n, v'), false) :: nil.
    Proof.
      intros R c; unfold uniqueClauses; rewrite List.in_flat_map.
      split.
      - intros [[n v] [Hp Hc]]; apply List.in_map_iff in Hc.
        destruct Hc as [v' [<- Hv']]; cbn [fst snd] in Hv' |- *.
        apply List.filter_In in Hv'; destruct Hv' as [Hv' Hlt].
        apply SOv.elements_in, C.mem_versions in Hv'.
        exists n, v, v'.
        split; [apply SOp.elements_in; exact Hp |].
        split; [exact Hv' |].
        split; [apply ltb_lt; exact Hlt | reflexivity].
      - intros [n [v [v' [Hv [Hv' [Hlt ->]]]]]].
        exists (n, v); split; [apply SOp.elements_in; exact Hv |].
        apply List.in_map_iff; exists v'; split; [reflexivity |].
        apply List.filter_In; split;
          [apply SOv.elements_in, C.mem_versions; exact Hv'
          | apply ltb_lt; exact Hlt].
    Qed.

    Theorem sat_encoding_soundness : forall R D r (sigma : Pkg.t -> bool),
        PkgSet.In r R ->
        CnfSat sigma (satEncoding R D r) ->
        C.IsResolution R D r (PkgSet.filter sigma R).
    Proof.
      intros R D r sigma Hr Hsat.
      assert (Hin : forall p, PkgSet.In p (PkgSet.filter sigma R) <->
                              PkgSet.In p R /\ sigma p = true)
        by (intro p; apply PkgSet.filter_spec').
      assert (Huc : forall n v v', PkgSet.In (n, v) R -> PkgSet.In (n, v') R ->
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
          apply Hin; split; [apply PkgSet.mem_spec; exact HR | exact Hls].
      - intros n v v' Hv Hv'; apply Hin in Hv, Hv'.
        destruct Hv as [HvR Hvs], Hv' as [Hv'R Hv's].
        destruct (V.compare_spec v v') as [E | L | G]; [exact E | |];
          exfalso.
        + destruct (Huc n v v' HvR Hv'R L); congruence.
        + destruct (Huc n v' v Hv'R HvR G); congruence.
    Qed.

    Theorem sat_encoding_completeness : forall R D r S,
        C.IsResolution R D r S ->
        CnfSat (fun p => PkgSet.mem p S) (satEncoding R D r).
    Proof.
      intros R D r S [Hsub Hroot Hdep Huniq] c Hc.
      destruct Hc as [<- | Hc].
      - exists (r, true); split; [left; reflexivity |].
        apply PkgSet.mem_spec; exact Hroot.
      - apply List.in_app_or in Hc; destruct Hc as [Hc | Hc].
        + apply in_depClauses in Hc; destruct Hc as [p [n [vs [HD ->]]]].
          destruct (PkgSet.mem p S) eqn:Ep.
          * apply PkgSet.mem_spec in Ep.
            destruct (Hdep p Ep n vs HD) as [v [Hv HvS]].
            exists ((n, v), true); split.
            -- apply in_depClause_pos; split; [exact Hv | apply Hsub; exact HvS].
            -- apply PkgSet.mem_spec; exact HvS.
          * exists (p, false); split; [left; reflexivity | exact Ep].
        + apply in_uniqueClauses in Hc.
          destruct Hc as [n [v [v' [_ [_ [Hlt ->]]]]]].
          destruct (PkgSet.mem (n, v) S) eqn:E1;
            [destruct (PkgSet.mem (n, v') S) eqn:E2 |].
          * exfalso; apply PkgSet.mem_spec in E1, E2.
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
    Module LF := UOTCompareFacts LitOT.
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
      | Lit (l : LitOT.t).
      Definition t := version.

      Definition rank (x : t) : nat :=
        match x with Eps => 0 | Truth _ => 1 | Lit _ => 2 end.

      Definition compare (x y : t) : comparison :=
        match Nat.compare (rank x) (rank y) with
        | Eq => match x, y with
                | Truth a, Truth b => BoolOT.compare a b
                | Lit a, Lit b => LitOT.compare a b
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
    Module T := Core NameOT VersionOT.

    Definition root : T.Pkg.t := (Name.Root, Version.Eps).

    Definition clauseReal (c : ClauseOT.t) : list T.Pkg.t :=
      List.flat_map
        (fun l => (Name.Var (fst l), Version.Truth true) ::
                  (Name.Var (fst l), Version.Truth false) ::
                  (Name.Clause c, Version.Lit l) :: nil)
        (lits c).

    Definition reduceReal (phi : list ClauseOT.t) : T.PkgSet.t :=
      T.PkgSet.ofList (root :: List.flat_map clauseReal phi).

    Definition litVersions (c : ClauseOT.t) : T.VSet.t :=
      T.VSet.ofList (List.map Version.Lit (lits c)).

    Definition clauseDeps (c : ClauseOT.t) : list T.DepElt.t :=
      (root, (Name.Clause c, litVersions c)) ::
      List.map
        (fun l => ((Name.Clause c, Version.Lit l),
                   (Name.Var (fst l), T.VSet.singleton (Version.Truth (snd l)))))
        (lits c).

    Definition reduceDeps (phi : list ClauseOT.t) : T.DepRel.t :=
      T.DepRel.ofList (List.flat_map clauseDeps phi).

    Lemma mem_reduceReal : forall phi (y : T.Pkg.t),
        T.PkgSet.In y (reduceReal phi) <->
        y = root \/
        exists c l, List.In c phi /\ List.In l (lits c) /\
          ((exists b, y = (Name.Var (fst l), Version.Truth b)) \/
           y = (Name.Clause c, Version.Lit l)).
    Proof.
      intros phi y; unfold reduceReal.
      rewrite T.PkgSet.mem_ofList; cbn [List.In]; rewrite List.in_flat_map.
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

    Lemma mem_litVersions : forall c w,
        T.VSet.In w (litVersions c) <->
        exists l, List.In l (lits c) /\ w = Version.Lit l.
    Proof.
      intros c w; unfold litVersions.
      rewrite T.VSet.mem_ofList, List.in_map_iff.
      split; intros [l [H1 H2]]; exists l; split; auto.
    Qed.

    Lemma mem_reduceDeps : forall phi (e : T.DepElt.t),
        T.DepRel.In e (reduceDeps phi) <->
        exists c, List.In c phi /\
          (e = (root, (Name.Clause c, litVersions c)) \/
           exists l, List.In l (lits c) /\
             e = ((Name.Clause c, Version.Lit l),
                  (Name.Var (fst l),
                   T.VSet.singleton (Version.Truth (snd l))))).
    Proof.
      intros phi e; unfold reduceDeps.
      rewrite T.DepRel.mem_ofList, List.in_flat_map.
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

    Theorem reduceDeps_functionalInName : forall phi,
        T.FunctionalInName (reduceDeps phi).
    Proof.
      intros phi p n vs1 vs2 H1 H2; apply mem_reduceDeps in H1, H2.
      unfold root in *.
      destruct H1 as [c1 [_ [E1 | [l1 [_ E1]]]]],
               H2 as [c2 [_ [E2 | [l2 [_ E2]]]]];
        congruence.
    Qed.

    Definition extractAssignment (S : T.PkgSet.t) (x : X.t) : bool :=
      T.PkgSet.mem (Name.Var x, Version.Truth true) S.

    Lemma extractAssignment_spec : forall S x b,
        T.VersionUnique S -> T.PkgSet.In (Name.Var x, Version.Truth b) S ->
        extractAssignment S x = b.
    Proof.
      intros S x b Huniq Hin; unfold extractAssignment.
      destruct b; [apply T.PkgSet.mem_spec; exact Hin |].
      destruct (T.PkgSet.mem (Name.Var x, Version.Truth true) S) eqn:E;
        [| reflexivity].
      apply T.PkgSet.mem_spec in E.
      discriminate (Huniq _ _ _ E Hin).
    Qed.

    Theorem three_sat_soundness : forall phi S,
        T.IsResolution (reduceReal phi) (reduceDeps phi) root S ->
        CnfSat (extractAssignment S) (cnf phi).
    Proof.
      intros phi S [_ Hroot Hdep Huniq] c Hc.
      unfold cnf in Hc; apply List.in_map_iff in Hc.
      destruct Hc as [c0 [<- Hc0]].
      destruct (Hdep _ Hroot (Name.Clause c0) (litVersions c0)) as [w [Hw HwS]].
      { apply mem_reduceDeps; exists c0; split; [exact Hc0 | left; reflexivity]. }
      apply mem_litVersions in Hw; destruct Hw as [l [Hl ->]].
      destruct (Hdep _ HwS (Name.Var (fst l))
                  (T.VSet.singleton (Version.Truth (snd l))))
        as [w [Hw HwS']].
      { apply mem_reduceDeps; exists c0; split; [exact Hc0 |].
        right; exists l; split; [exact Hl | reflexivity]. }
      apply T.VSet.singleton_spec in Hw; subst w.
      exists l; split; [exact Hl |].
      apply extractAssignment_spec; assumption.
    Qed.

    Definition litSatb (sigma : X.t -> bool) (l : LitOT.t) : bool :=
      Bool.eqb (sigma (fst l)) (snd l).

    Definition firstSatisfied (sigma : X.t -> bool) (c : ClauseOT.t)
      : LitOT.t :=
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

    Definition coreResolution (sigma : X.t -> bool) (phi : list ClauseOT.t)
      : T.PkgSet.t :=
      T.PkgSet.ofList
        (root ::
         List.flat_map
           (fun c => (Name.Clause c, Version.Lit (firstSatisfied sigma c)) ::
                     List.map
                       (fun l => (Name.Var (fst l),
                                  Version.Truth (sigma (fst l))))
                       (lits c))
           phi).

    Lemma mem_coreResolution : forall sigma phi (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution sigma phi) <->
        y = root \/
        exists c, List.In c phi /\
          (y = (Name.Clause c, Version.Lit (firstSatisfied sigma c)) \/
           exists l, List.In l (lits c) /\
             y = (Name.Var (fst l), Version.Truth (sigma (fst l)))).
    Proof.
      intros sigma phi y; unfold coreResolution.
      rewrite T.PkgSet.mem_ofList; cbn [List.In]; rewrite List.in_flat_map.
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

    Theorem three_sat_completeness : forall phi sigma,
        CnfSat sigma (cnf phi) ->
        T.IsResolution (reduceReal phi) (reduceDeps phi) root
          (coreResolution sigma phi).
    Proof.
      intros phi sigma Hsat; constructor.
      - intros y Hy; apply mem_coreResolution in Hy; apply mem_reduceReal.
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
          split; [apply T.VSet.singleton_spec; reflexivity |].
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

    Theorem three_sat_correct : forall phi,
        (exists sigma, CnfSat sigma (cnf phi)) <->
        exists S, T.IsResolution (reduceReal phi) (reduceDeps phi) root S.
    Proof.
      intro phi; split.
      - intros [sigma Hs]; exists (coreResolution sigma phi).
        exact (three_sat_completeness phi sigma Hs).
      - intros [S HS]; exists (extractAssignment S).
        exact (three_sat_soundness phi S HS).
    Qed.
  End Reduction.
End Complexity.
