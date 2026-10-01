From Stdlib Require Import MSets MSetRBT Sorted.
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
    2:{ intros [q d] a y; simpl; pose proof (SOdh.empty_in y).
        destruct (Pkg.eq_dec q p); rewrite ?SOdh.add_in, ?SOdh.singleton_in;
          tauto. }
    pose proof (SOdh.empty_in h) as E0; split.
    - intros [H | [[q d] [HeD He]]]; [tauto | simpl in He].
      destruct (Pkg.eq_dec q p) as [-> | _]; [| tauto].
      apply SOdh.singleton_in in He; subst d; exact HeD.
    - intro H; right; exists (p, h); simpl.
      rewrite dec_refl, SOdh.singleton_in; auto.
  Qed.

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

  Module SOpv := SetOps Pkg V PkgSet VSet.
  Definition versions (R : PkgSet.t) (n : N.t) : VSet.t :=
    SOpv.filterMap (fun '(m, v) => if N.eq_dec m n then Some v else None) R.

  Lemma mem_versions : forall R (n : N.t) (v : V.t),
      VSet.In v (versions R n) <-> PkgSet.In (n, v) R.
  Proof.
    intros R n v; unfold versions; rewrite SOpv.mem_filterMap.
    split.
    - intros [[m u] [HR Hm]]; cbn beta iota in Hm.
      destruct (N.eq_dec m n) as [-> | NE]; [| discriminate].
      injection Hm as <-; exact HR.
    - intro H; exists (n, v); split; [exact H | cbn beta iota].
      rewrite dec_refl; reflexivity.
  Qed.

  Lemma versions_ext : forall R R' (n : N.t),
      (forall v, PkgSet.In (n, v) R <-> PkgSet.In (n, v) R') ->
      versions R n = versions R' n.
  Proof.
    intros R R' n H; apply VSet.ext; intro v.
    rewrite !mem_versions; exact (H v).
  Qed.

  Module NSet := FSetUOT N.

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
      cbn [fst]; apply dec_refl.
  Qed.

  Lemma hasNameb_false : forall S n,
      hasNameb S n = false <-> forall v, ~ PkgSet.In (n, v) S.
  Proof.
    intros S n; split.
    - intros E v Hv.
      assert (Ht : hasNameb S n = true)
        by (apply hasNameb_true; exists v; exact Hv).
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

  Module PkgPreimage := PreimageOfKeys N Pkg NSet PkgSet.
  Definition namePreimage (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
    PkgPreimage.ofKeys fst ns R.

  Lemma mem_namePreimage : forall R ns n v,
      PkgSet.In (n, v) (namePreimage R ns) <->
      PkgSet.In (n, v) R /\ NSet.In n ns.
  Proof. intros R ns n v; apply PkgPreimage.mem_ofKeys. Qed.

  Lemma versions_namePreimage : forall R ns n,
      NSet.In n ns -> versions (namePreimage R ns) n = versions R n.
  Proof.
    intros R ns n Hn; apply versions_ext; intro v.
    rewrite mem_namePreimage; cbn [fst]; tauto.
  Qed.

  Definition VersionUnique (S : PkgSet.t) : Prop :=
    forall (n : N.t) (v v' : V.t),
      PkgSet.In (n, v) S -> PkgSet.In (n, v') S -> v = v'.

  Definition FunctionalInName (D : DepRel.t) : Prop :=
    forall (p : Pkg.t) (n : N.t) (vs vs' : VSet.t),
      DepRel.In (p, (n, vs)) D -> DepRel.In (p, (n, vs')) D -> vs = vs'.

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

  Inductive Reached (dependees : Pkg.t -> DependeesSet.t) (Q : DependeesSet.t)
      (S : PkgSet.t) : Pkg.t -> Prop :=
  | reached_query : forall (n : N.t) (vs : VSet.t) (v : V.t),
      DependeesSet.In (n, vs) Q -> VSet.In v vs -> PkgSet.In (n, v) S ->
      Reached dependees Q S (n, v)
  | reached_dependee : forall p (n : N.t) (vs : VSet.t) (v : V.t),
      Reached dependees Q S p -> DependeesSet.In (n, vs) (dependees p) ->
      VSet.In v vs -> PkgSet.In (n, v) S -> Reached dependees Q S (n, v).

  Definition rootQuery '((n, v) : Pkg.t) : DependeesSet.t :=
    DependeesSet.singleton (n, VSet.singleton v).

  Inductive CheckFailure : Type :=
  | CheckSubset (p : Pkg.t)
  | CheckVersionUnique (p : Pkg.t)
  | CheckRootMem (h : Dependees.t)
  | CheckDepClosure (p : Pkg.t) (h : Dependees.t)
  | CheckReached (p : Pkg.t).

  (* PkgSet is a sorted list, so a membership test walks it; the check asks
     one per dependee version, which a tree answers in logarithmic time. *)
  Module PkgTree := MSetRBT.Make Pkg.
  Module PkgTreeP := WPropertiesOn Pkg PkgTree.

  Definition subsetFailure (versions : N.t -> VSet.t) (S : PkgSet.t)
    : option Pkg.t :=
    List.find (fun '(n, v) => negb (VSet.mem v (versions n)))
      (PkgSet.elements S).

  Fixpoint adjacentFailure (l : list Pkg.t) : option Pkg.t :=
    match l with
    | (n, _) :: (((m, w) :: _) as l') =>
        if N.eq_dec n m then Some (m, w) else adjacentFailure l'
    | _ => None
    end.

  Definition treeOf (S : PkgSet.t) : PkgTree.t :=
    PkgSet.fold PkgTree.add S PkgTree.empty.

  Definition witness (t : PkgTree.t) '((n, vs) : Dependees.t) : option Pkg.t :=
    match List.find (fun v => PkgTree.mem (n, v) t) (VSet.elements vs) with
    | Some v => Some (n, v)
    | None => None
    end.

  Definition rootFailure (t : PkgTree.t) (Q : DependeesSet.t)
    : option Dependees.t :=
    List.find
      (fun h => match witness t h with Some _ => false | None => true end)
      (DependeesSet.elements Q).

  Fixpoint edgesOf (t : PkgTree.t) (hs : list Dependees.t)
    : Dependees.t + list Pkg.t :=
    match hs with
    | nil => inr nil
    | h :: hs' =>
        match witness t h with
        | None => inl h
        | Some q =>
            match edgesOf t hs' with
            | inl h' => inl h'
            | inr qs => inr (q :: qs)
            end
        end
    end.

  Fixpoint closureFailure (t : PkgTree.t) (dependees : Pkg.t -> DependeesSet.t)
      (ps : list Pkg.t) : (Pkg.t * Dependees.t) + list (Pkg.t * Pkg.t) :=
    match ps with
    | nil => inr nil
    | p :: ps' =>
        match edgesOf t (DependeesSet.elements (dependees p)) with
        | inl h => inl (p, h)
        | inr qs =>
            match closureFailure t dependees ps' with
            | inl f => inl f
            | inr es => inr (List.map (fun q => (p, q)) qs ++ es)
            end
        end
    end.

  Fixpoint step (es : list (Pkg.t * Pkg.t)) (seen : PkgTree.t) (changed : bool)
    : PkgTree.t * bool :=
    match es with
    | nil => (seen, changed)
    | (p, q) :: es' =>
        if andb (PkgTree.mem p seen) (negb (PkgTree.mem q seen))
        then step es' (PkgTree.add q seen) true
        else step es' seen changed
    end.

  Fixpoint closeUnder (fuel : nat) (es : list (Pkg.t * Pkg.t))
      (seen : PkgTree.t) : PkgTree.t :=
    match fuel with
    | O => seen
    | Datatypes.S k =>
        let '(seen', changed) := step es seen false in
        if changed then closeUnder k es seen' else seen'
    end.

  Definition queryWitnesses (t : PkgTree.t) (Q : DependeesSet.t) : PkgTree.t :=
    DependeesSet.fold
      (fun h acc =>
         match witness t h with Some q => PkgTree.add q acc | None => acc end)
      Q PkgTree.empty.

  Definition check (versions : N.t -> VSet.t)
      (dependees : Pkg.t -> DependeesSet.t) (Q : DependeesSet.t)
      (S : PkgSet.t) : option CheckFailure :=
    match subsetFailure versions S with
    | Some p => Some (CheckSubset p)
    | None =>
        match adjacentFailure (PkgSet.elements S) with
        | Some p => Some (CheckVersionUnique p)
        | None =>
            let t := treeOf S in
            match rootFailure t Q with
            | Some h => Some (CheckRootMem h)
            | None =>
                match closureFailure t dependees (PkgSet.elements S) with
                | inl (p, h) => Some (CheckDepClosure p h)
                | inr es =>
                    let seen :=
                      closeUnder (PkgSet.cardinal S + 1) es
                        (queryWitnesses t Q) in
                    match List.find (fun p => negb (PkgTree.mem p seen))
                            (PkgSet.elements S) with
                    | Some p => Some (CheckReached p)
                    | None => None
                    end
                end
            end
        end
    end.

  Section CheckProofs.
    Lemma find_none_iff : forall {A} (f : A -> bool) l,
        List.find f l = None <-> forall x, List.In x l -> f x = false.
    Proof.
      intros A f l; split; [apply List.find_none |].
      induction l as [| a l IH]; intro H; [reflexivity |]; cbn.
      rewrite (H a (or_introl eq_refl)).
      apply IH; intros x Hx; apply H; right; exact Hx.
    Qed.

    Lemma in_elements_pkg : forall S p,
        List.In p (PkgSet.elements S) <-> PkgSet.In p S.
    Proof. intros S p; apply SOpv.elements_in. Qed.

    Lemma in_elements_vset : forall vs v,
        List.In v (VSet.elements vs) <-> VSet.In v vs.
    Proof.
      intros vs v; rewrite <- VSet.elements_spec1, SetoidList.InA_alt.
      split; [intro H; exists v; auto | intros [w [-> H]]; exact H].
    Qed.

    Lemma in_elements_hset : forall hs h,
        List.In h (DependeesSet.elements hs) <-> DependeesSet.In h hs.
    Proof.
      intros hs h; rewrite <- DependeesSet.elements_spec1, SetoidList.InA_alt.
      split; [intro H; exists h; auto | intros [g [-> H]]; exact H].
    Qed.

    Lemma in_elements_tree : forall t p,
        List.In p (PkgTree.elements t) <-> PkgTree.In p t.
    Proof.
      intros t p; rewrite <- PkgTree.elements_spec1, SetoidList.InA_alt.
      split; [intro H; exists p; auto | intros [q [-> H]]; exact H].
    Qed.

    Lemma mem_tree : forall t p, PkgTree.mem p t = true <-> PkgTree.In p t.
    Proof. intros t p; apply PkgTree.mem_spec. Qed.

    Lemma mem_tree_false : forall t p,
        PkgTree.mem p t = false <-> ~ PkgTree.In p t.
    Proof.
      intros t p; rewrite <- mem_tree; destruct (PkgTree.mem p t);
        split; congruence.
    Qed.

    Lemma in_add_tree : forall t p q,
        PkgTree.In q (PkgTree.add p t) <-> q = p \/ PkgTree.In q t.
    Proof. intros t p q; apply PkgTree.add_spec. Qed.

    Lemma mem_treeOf : forall S p, PkgTree.In p (treeOf S) <-> PkgSet.In p S.
    Proof.
      intros S p; unfold treeOf; rewrite PkgSet.fold_spec, <- in_elements_pkg.
      assert (H : forall l t,
          PkgTree.In p (List.fold_left (fun a e => PkgTree.add e a) l t) <->
          PkgTree.In p t \/ List.In p l).
      { induction l as [| a l IH]; intro t; cbn; [tauto |].
        rewrite IH, in_add_tree; split;
          [intros [[-> | H] | H]; auto | intros [H | [-> | H]]; auto]. }
      rewrite H; pose proof (PkgTree.empty_spec (a := p)); tauto.
    Qed.

    Lemma witness_some : forall t (n : N.t) (vs : VSet.t) q,
        witness t (n, vs) = Some q ->
        exists v, q = (n, v) /\ VSet.In v vs /\ PkgTree.In (n, v) t.
    Proof.
      intros t n vs q; unfold witness; cbn beta iota.
      destruct (List.find _ _) as [v |] eqn:E; [| discriminate].
      intro H; injection H as <-; apply List.find_some in E.
      destruct E as [Hv Hm]; exists v; split; [reflexivity |].
      split; [apply in_elements_vset; exact Hv | apply mem_tree; exact Hm].
    Qed.

    Lemma witness_none : forall t (n : N.t) (vs : VSet.t),
        witness t (n, vs) = None ->
        forall v, VSet.In v vs -> ~ PkgTree.In (n, v) t.
    Proof.
      intros t n vs; unfold witness; cbn beta iota.
      destruct (List.find _ _) as [v |] eqn:E; [discriminate |].
      intros _ v Hv Ht; rewrite find_none_iff in E.
      apply in_elements_vset in Hv; specialize (E v Hv); cbn beta in E.
      apply mem_tree_false in E; exact (E Ht).
    Qed.

    Lemma witness_met : forall t (n : N.t) (vs : VSet.t) (v : V.t),
        VSet.In v vs -> PkgTree.In (n, v) t ->
        exists q, witness t (n, vs) = Some q.
    Proof.
      intros t n vs v Hv Ht; destruct (witness t (n, vs)) as [q |] eqn:E;
        [exists q; reflexivity |].
      destruct (witness_none t n vs E v Hv Ht).
    Qed.

    Lemma adjacentFailure_none : forall l, Sorted Pkg.lt l ->
        adjacentFailure l = None <->
        (forall (n : N.t) (v v' : V.t),
            List.In (n, v) l -> List.In (n, v') l -> v = v').
    Proof.
      intros l Hs; apply Sorted_StronglySorted in Hs;
        [| intros x y z; apply StrictOrder_Transitive].
      induction Hs as [| [n v] l Hs IH Hall]; [cbn; split; [tauto | reflexivity] |].
      destruct l as [| [m w] l].
      - cbn; split; [| reflexivity].
        intros _ n' u u' [Hu | []] [Hu' | []]; congruence.
      - pose proof (List.Forall_inv Hall) as Hlt.
        destruct Hlt as [Hlt | [Heq Hlt]]; cbn [fst snd] in *.
        + assert (Hne : n <> m)
            by (intros ->; exact (StrictOrder_Irreflexive m Hlt)).
          cbn [adjacentFailure]; destruct (N.eq_dec n m) as [| _];
            [contradiction |].
          rewrite IH; split.
          * intros Hu n' u u' Hu1 Hu2.
            assert (Hh : forall u'', List.In (n', u'') ((m, w) :: l) ->
                       n' <> n).
            { intros u'' Hin ->.
              apply Sorted.StronglySorted_inv in Hs; destruct Hs as [_ Hs'].
              destruct Hin as [Hin | Hin]; [congruence |].
              rewrite List.Forall_forall in Hs'.
              destruct (Hs' _ Hin) as [Hc | [Hc _]]; cbn [fst] in Hc;
                [exact (StrictOrder_Irreflexive n
                          (StrictOrder_Transitive _ _ _ Hlt Hc)) | congruence]. }
            destruct Hu1 as [Hu1 | Hu1]; destruct Hu2 as [Hu2 | Hu2].
            -- congruence.
            -- injection Hu1 as -> ->; destruct (Hh u' Hu2 eq_refl).
            -- injection Hu2 as -> ->; destruct (Hh u Hu1 eq_refl).
            -- exact (Hu n' u u' Hu1 Hu2).
          * intros Hu n' u u' Hu1 Hu2; apply (Hu n' u u'); right; assumption.
        + subst m; cbn [adjacentFailure]; rewrite dec_refl; split;
            [discriminate |].
          intro Hu; assert (v = w) as ->
            by (apply (Hu n); [left | right; left]; reflexivity).
          destruct (StrictOrder_Irreflexive w Hlt).
    Qed.

    Lemma adjacentFailure_unique : forall S,
        adjacentFailure (PkgSet.elements S) = None <-> VersionUnique S.
    Proof.
      intro S; rewrite adjacentFailure_none by exact (PkgSet.elements_spec2 S).
      unfold VersionUnique; setoid_rewrite in_elements_pkg; reflexivity.
    Qed.

    Lemma edgesOf_inl : forall t hs h,
        edgesOf t hs = inl h -> List.In h hs /\ witness t h = None.
    Proof.
      intros t hs; induction hs as [| g hs IH]; intros h; cbn; [discriminate |].
      destruct (witness t g) as [q |] eqn:Eg.
      - destruct (edgesOf t hs) as [h' | qs] eqn:E; [| discriminate].
        intro H; injection H as ->; destruct (IH h eq_refl) as [Hin Hw].
        split; [right; exact Hin | exact Hw].
      - intro H; injection H as ->; split; [left; reflexivity | exact Eg].
    Qed.

    Lemma edgesOf_inr : forall t hs qs,
        edgesOf t hs = inr qs ->
        (forall h, List.In h hs -> exists q, witness t h = Some q /\ List.In q qs)
        /\ (forall q, List.In q qs ->
            exists h, List.In h hs /\ witness t h = Some q).
    Proof.
      intros t hs; induction hs as [| g hs IH]; intros qs; cbn.
      - intro H; injection H as <-; split; [intros _ [] | intros _ []].
      - destruct (witness t g) as [q |] eqn:Eg; [| discriminate].
        destruct (edgesOf t hs) as [h' | qs'] eqn:E; [discriminate |].
        intro H; injection H as <-; destruct (IH qs' eq_refl) as [H1 H2].
        split.
        + intros h Hh; destruct Hh as [Hg | Hh];
            [subst h; exists q; split; [exact Eg | left; reflexivity] |].
          destruct (H1 h Hh) as [q' [Hq' Hin]]; exists q'.
          split; [exact Hq' | right; exact Hin].
        + intros q' Hq'; destruct Hq' as [Hq | Hq'];
            [subst q'; exists g; split; [left; reflexivity | exact Eg] |].
          destruct (H2 q' Hq') as [h [Hh Hw]]; exists h.
          split; [right; exact Hh | exact Hw].
    Qed.

    Lemma closureFailure_inl : forall t dependees ps p h,
        closureFailure t dependees ps = inl (p, h) ->
        List.In p ps /\ DependeesSet.In h (dependees p) /\ witness t h = None.
    Proof.
      intros t dependees ps; induction ps as [| p0 ps IH]; intros p h; cbn;
        [discriminate |].
      destruct (edgesOf t _) as [h0 | qs] eqn:E.
      - intro H; injection H as Hp Hh; subst p h; apply edgesOf_inl in E.
        destruct E as [Hin Hw]; apply in_elements_hset in Hin.
        split; [left; reflexivity | split; [exact Hin | exact Hw]].
      - destruct (closureFailure t dependees ps) as [[p' h'] | es] eqn:E';
          [| discriminate].
        intro H; injection H as Hp Hh; subst p' h'.
        destruct (IH p h eq_refl) as [Hp [Hd Hw]].
        split; [right; exact Hp | split; [exact Hd | exact Hw]].
    Qed.

    Lemma closureFailure_inr : forall t dependees ps es,
        closureFailure t dependees ps = inr es ->
        (forall p h, List.In p ps -> DependeesSet.In h (dependees p) ->
         exists q, witness t h = Some q /\ List.In (p, q) es) /\
        (forall p q, List.In (p, q) es ->
         exists h, DependeesSet.In h (dependees p) /\ witness t h = Some q).
    Proof.
      intros t dependees ps; induction ps as [| p0 ps IH]; intros es; cbn.
      - intro H; injection H as <-; split; [intros _ _ [] | intros _ _ []].
      - destruct (edgesOf t _) as [h0 | qs] eqn:E; [discriminate |].
        destruct (closureFailure t dependees ps) as [f | es'] eqn:E';
          [discriminate |].
        intro H; injection H as <-; destruct (IH es' eq_refl) as [H1 H2].
        destruct (edgesOf_inr t _ qs E) as [G1 G2]; split.
        + intros p h Hp Hh; destruct Hp as [Hp | Hp].
          * subst p; apply in_elements_hset in Hh.
            destruct (G1 h Hh) as [q [Hw Hq]].
            exists q; split; [exact Hw |].
            apply List.in_or_app; left; apply List.in_map_iff.
            exists q; split; [reflexivity | exact Hq].
          * destruct (H1 p h Hp Hh) as [q [Hw Hq]]; exists q; split;
              [exact Hw | apply List.in_or_app; right; exact Hq].
        + intros p q Hpq; apply List.in_app_or in Hpq; destruct Hpq as [Hpq | Hpq].
          * apply List.in_map_iff in Hpq; destruct Hpq as [q' [Heq Hq']].
            injection Heq as Hp Hq; subst p q.
            destruct (G2 q' Hq') as [h [Hh Hw]].
            apply in_elements_hset in Hh; exists h; split; [exact Hh | exact Hw].
          * exact (H2 p q Hpq).
    Qed.

    Lemma step_true : forall es seen, snd (step es seen true) = true.
    Proof.
      intro es; induction es as [| [p q] es IH]; intro seen; cbn; [reflexivity |].
      destruct (andb _ _); apply IH.
    Qed.

    Lemma step_mono : forall es seen c x,
        PkgTree.In x seen -> PkgTree.In x (fst (step es seen c)).
    Proof.
      intro es; induction es as [| [p q] es IH]; intros seen c x Hx; cbn;
        [exact Hx |].
      destruct (andb _ _); apply IH; [apply in_add_tree; right |]; exact Hx.
    Qed.

    Lemma step_sound : forall (P : Pkg.t -> Prop) es seen c,
        (forall p q, List.In (p, q) es -> P p -> P q) ->
        (forall x, PkgTree.In x seen -> P x) ->
        forall x, PkgTree.In x (fst (step es seen c)) -> P x.
    Proof.
      intros P es; induction es as [| [p q] es IH]; intros seen c Hes Hs;
        cbn; [exact Hs |].
      destruct (andb _ _) eqn:E; apply IH;
        try (intros p' q' Hin; apply Hes; right; exact Hin); [| exact Hs].
      apply Bool.andb_true_iff in E; destruct E as [Hp _].
      apply mem_tree in Hp.
      intros x Hx; apply in_add_tree in Hx; destruct Hx as [-> | Hx];
        [exact (Hes p q (or_introl eq_refl) (Hs p Hp)) | exact (Hs x Hx)].
    Qed.

    Lemma step_false : forall es seen c,
        snd (step es seen c) = false ->
        c = false /\ fst (step es seen c) = seen /\
        (forall p q, List.In (p, q) es ->
         PkgTree.In p seen -> PkgTree.In q seen).
    Proof.
      intro es; induction es as [| [p q] es IH]; intros seen c; cbn.
      - intros ->; split; [reflexivity | split; [reflexivity | intros _ _ []]].
      - destruct (andb _ _) eqn:E; [rewrite step_true; discriminate |].
        intro H; destruct (IH seen c H) as [Hc [Hf Hcl]].
        split; [exact Hc | split; [exact Hf |]].
        intros p' q' [Heq | Hin] Hp'; [| exact (Hcl p' q' Hin Hp')].
        injection Heq as <- <-.
        apply mem_tree in Hp'; rewrite Hp' in E; cbn in E.
        apply Bool.negb_false_iff, mem_tree in E; exact E.
    Qed.

    Lemma step_card : forall es seen c,
        PkgTree.cardinal seen <= PkgTree.cardinal (fst (step es seen c)) /\
        (c = false -> snd (step es seen c) = true ->
         PkgTree.cardinal seen < PkgTree.cardinal (fst (step es seen c))).
    Proof.
      intro es; induction es as [| [p q] es IH]; intros seen c; cbn.
      - split; [reflexivity | intros -> H; discriminate].
      - destruct (andb _ _) eqn:E; [| exact (IH seen c)].
        apply Bool.andb_true_iff in E; destruct E as [_ Hq].
        apply Bool.negb_true_iff, mem_tree_false in Hq.
        destruct (IH (PkgTree.add q seen) true) as [Hle _].
        rewrite (PkgTreeP.add_cardinal_2 Hq) in Hle.
        split; [| intros _ _]; Lia.lia.
    Qed.

    Lemma nodup_tree : forall t, List.NoDup (PkgTree.elements t).
    Proof.
      intro t; pose proof (PkgTree.elements_spec2w t) as H.
      induction H as [| x l Hx _ IH]; constructor; [| exact IH].
      intro Hin; apply Hx; apply SetoidList.In_InA; [exact eq_equivalence |].
      exact Hin.
    Qed.

    Lemma cardinal_within : forall (t : PkgTree.t) S,
        (forall x, PkgTree.In x t -> PkgSet.In x S) ->
        PkgTree.cardinal t <= PkgSet.cardinal S.
    Proof.
      intros t S H; rewrite PkgTree.cardinal_spec, PkgSet.cardinal_spec.
      apply List.NoDup_incl_length; [apply nodup_tree |].
      intros x Hx; apply in_elements_pkg, H, in_elements_tree; exact Hx.
    Qed.

    Lemma closeUnder_mono : forall fuel es seen x,
        PkgTree.In x seen -> PkgTree.In x (closeUnder fuel es seen).
    Proof.
      intro fuel; induction fuel as [| k IH]; intros es seen x Hx; cbn;
        [exact Hx |].
      pose proof (step_mono es seen false x Hx) as Hm.
      destruct (step es seen false) as [seen' c]; cbn in Hm.
      destruct c; [apply IH |]; exact Hm.
    Qed.

    Lemma closeUnder_sound : forall (P : Pkg.t -> Prop) fuel es seen,
        (forall p q, List.In (p, q) es -> P p -> P q) ->
        (forall x, PkgTree.In x seen -> P x) ->
        forall x, PkgTree.In x (closeUnder fuel es seen) -> P x.
    Proof.
      intros P fuel; induction fuel as [| k IH]; intros es seen Hes Hs; cbn;
        [exact Hs |].
      pose proof (step_sound P es seen false Hes Hs) as Hst.
      destruct (step es seen false) as [seen' c]; cbn in Hst.
      destruct c; [apply IH; assumption | exact Hst].
    Qed.

    Lemma closeUnder_closed : forall S fuel es seen,
        (forall p q, List.In (p, q) es -> PkgSet.In q S) ->
        (forall x, PkgTree.In x seen -> PkgSet.In x S) ->
        PkgSet.cardinal S < PkgTree.cardinal seen + fuel ->
        forall p q, List.In (p, q) es ->
        PkgTree.In p (closeUnder fuel es seen) ->
        PkgTree.In q (closeUnder fuel es seen).
    Proof.
      intros S fuel; induction fuel as [| k IH]; intros es seen Hes Hs Hc.
      - pose proof (cardinal_within seen S Hs); Lia.lia.
      - cbn.
        pose proof (step_sound (fun x => PkgSet.In x S) es seen false
                      (fun p q Hin _ => Hes p q Hin) Hs) as Hst.
        pose proof (step_card es seen false) as [_ Hlt].
        pose proof (step_false es seen false) as Hf.
        destruct (step es seen false) as [seen' c]; cbn in Hst, Hlt, Hf.
        destruct c.
        + apply IH; [exact Hes | exact Hst |].
          specialize (Hlt eq_refl eq_refl); Lia.lia.
        + destruct (Hf eq_refl) as [_ [-> Hcl]]; exact Hcl.
    Qed.

    Lemma mem_queryWitnesses : forall t Q q,
        PkgTree.In q (queryWitnesses t Q) <->
        exists h, DependeesSet.In h Q /\ witness t h = Some q.
    Proof.
      intros t Q q; unfold queryWitnesses; rewrite DependeesSet.fold_spec.
      setoid_rewrite <- in_elements_hset.
      assert (H : forall l acc,
          PkgTree.In q
            (List.fold_left
               (fun a h => match witness t h with
                           | Some q' => PkgTree.add q' a
                           | None => a
                           end) l acc) <->
          PkgTree.In q acc \/ exists h, List.In h l /\ witness t h = Some q).
      { induction l as [| h l IH]; intro acc; cbn.
        - split; [tauto | intros [H | [_ [[] _]]]; exact H].
        - rewrite IH; destruct (witness t h) as [q' |] eqn:E.
          + rewrite in_add_tree; split.
            * intros [[Hq | H] | [h' [Hh' Hw]]].
              -- subst q'; right; exists h; split; [left; reflexivity | exact E].
              -- left; exact H.
              -- right; exists h'; split; [right; exact Hh' | exact Hw].
            * intros [H | [h' [[Hh | Hh'] Hw]]].
              -- left; right; exact H.
              -- subst h'; rewrite E in Hw; injection Hw as ->.
                 left; left; reflexivity.
              -- right; exists h'; split; [exact Hh' | exact Hw].
          + split.
            * intros [H | [h' [Hh' Hw]]]; [left; exact H |].
              right; exists h'; split; [right; exact Hh' | exact Hw].
            * intros [H | [h' [[Hh | Hh'] Hw]]].
              -- left; exact H.
              -- subst h'; rewrite E in Hw; discriminate.
              -- right; exists h'; split; [exact Hh' | exact Hw]. }
      rewrite H; pose proof (PkgTree.empty_spec (a := q)); split;
        [intros [? | ?]; tauto | intro; right; assumption].
    Qed.

    Lemma reached_in : forall dependees Q S p,
        Reached dependees Q S p -> PkgSet.In p S.
    Proof. intros dependees Q S p H; destruct H; assumption. Qed.

    Lemma witness_unique : forall S (n : N.t) (vs : VSet.t) (v : V.t) q,
        VersionUnique S -> PkgSet.In (n, v) S ->
        witness (treeOf S) (n, vs) = Some q -> q = (n, v).
    Proof.
      intros S n vs v q Hu Hv Hw; apply witness_some in Hw.
      destruct Hw as [v' [-> [_ Hv']]]; apply mem_treeOf in Hv'.
      rewrite (Hu n v' v Hv' Hv); reflexivity.
    Qed.
  End CheckProofs.

  Theorem check_spec : forall versions dependees Q S,
      check versions dependees Q S = None <->
      (forall (n : N.t) (v : V.t), PkgSet.In (n, v) S -> VSet.In v (versions n)) /\
      VersionUnique S /\
      (forall (n : N.t) (vs : VSet.t), DependeesSet.In (n, vs) Q ->
       exists v, VSet.In v vs /\ PkgSet.In (n, v) S) /\
      (forall p, PkgSet.In p S ->
       forall (n : N.t) (vs : VSet.t), DependeesSet.In (n, vs) (dependees p) ->
       exists v, VSet.In v vs /\ PkgSet.In (n, v) S) /\
      (forall p, PkgSet.In p S -> Reached dependees Q S p).
  Proof.
    intros versions dependees Q S; unfold check.
    set (t := treeOf S).
    assert (Hsub : subsetFailure versions S = None <->
                   forall (n : N.t) (v : V.t), PkgSet.In (n, v) S ->
                   VSet.In v (versions n)).
    { unfold subsetFailure; rewrite find_none_iff; split.
      - intros H n v Hin; apply in_elements_pkg in Hin; specialize (H _ Hin).
        apply Bool.negb_false_iff, VSet.mem_spec in H; exact H.
      - intros H [n v] Hin; apply in_elements_pkg in Hin.
        apply Bool.negb_false_iff, VSet.mem_spec, H; exact Hin. }
    assert (Hroot : rootFailure t Q = None <->
                    forall (n : N.t) (vs : VSet.t), DependeesSet.In (n, vs) Q ->
                    exists v, VSet.In v vs /\ PkgSet.In (n, v) S).
    { unfold rootFailure; rewrite find_none_iff; split.
      - intros H n vs Hin; apply in_elements_hset in Hin; specialize (H _ Hin).
        destruct (witness t (n, vs)) as [q |] eqn:E; [| discriminate].
        apply witness_some in E; destruct E as [v [_ [Hv Ht]]].
        exists v; split; [exact Hv | apply mem_treeOf; exact Ht].
      - intros H [n vs] Hin; apply in_elements_hset in Hin.
        destruct (H n vs Hin) as [v [Hv HS]].
        apply mem_treeOf in HS; fold t in HS.
        destruct (witness_met t n vs v Hv HS) as [q ->]; reflexivity. }
    split.
    - destruct (subsetFailure versions S) eqn:Es; [discriminate |].
      destruct (adjacentFailure (PkgSet.elements S)) eqn:Eu; [discriminate |].
      fold t; destruct (rootFailure t Q) eqn:Er; [discriminate |].
      destruct (closureFailure t dependees (PkgSet.elements S))
        as [[p h] | es] eqn:Ec; [discriminate |].
      destruct (List.find _ _) as [p |] eqn:Ef; [discriminate |].
      intros _.
      apply adjacentFailure_unique in Eu.
      destruct (closureFailure_inr _ _ _ _ Ec) as [Hc1 Hc2].
      split; [apply Hsub; reflexivity |]; split; [exact Eu |].
      split; [apply Hroot; reflexivity |]; split.
      + intros p Hp n vs Hd; apply in_elements_pkg in Hp.
        destruct (Hc1 p (n, vs) Hp Hd) as [q [Hw _]].
        apply witness_some in Hw; destruct Hw as [v [_ [Hv Ht]]].
        exists v; split; [exact Hv | apply mem_treeOf; exact Ht].
      + intros p Hp; rewrite find_none_iff in Ef.
        apply in_elements_pkg in Hp as Hp'; specialize (Ef p Hp').
        apply Bool.negb_false_iff, mem_tree in Ef.
        refine (closeUnder_sound (Reached dependees Q S) _ es _ _ _ p Ef).
        * intros p' q Hin Hr; destruct (Hc2 p' q Hin) as [[n vs] [Hd Hw]].
          apply witness_some in Hw; destruct Hw as [v [-> [Hv Ht]]].
          apply mem_treeOf in Ht.
          exact (reached_dependee dependees Q S p' n vs v Hr Hd Hv Ht).
        * intros x Hx; apply mem_queryWitnesses in Hx.
          destruct Hx as [[n vs] [HQ Hw]].
          apply witness_some in Hw; destruct Hw as [v [-> [Hv Ht]]].
          apply mem_treeOf in Ht; exact (reached_query dependees Q S n vs v HQ Hv Ht).
    - intros [Hv [Hu [HQ [Hclo Hreach]]]].
      rewrite (proj2 Hsub Hv), (proj2 (adjacentFailure_unique S) Hu).
      fold t; rewrite (proj2 Hroot HQ).
      destruct (closureFailure t dependees (PkgSet.elements S))
        as [[p h] | es] eqn:Ec.
      + apply closureFailure_inl in Ec; destruct Ec as [Hp [Hd Hw]].
        destruct h as [n vs]; apply in_elements_pkg in Hp.
        destruct (Hclo p Hp n vs Hd) as [v [Hvs HS]].
        apply mem_treeOf in HS; destruct (witness_none t n vs Hw v Hvs HS).
      + destruct (closureFailure_inr _ _ _ _ Ec) as [Hc1 Hc2].
        assert (Hes : forall p q, List.In (p, q) es -> PkgSet.In q S).
        { intros p q Hin; destruct (Hc2 p q Hin) as [[n vs] [_ Hw]].
          apply witness_some in Hw; destruct Hw as [v [-> [_ Ht]]].
          apply mem_treeOf; exact Ht. }
        assert (H0 : forall x, PkgTree.In x (queryWitnesses t Q) ->
                     PkgSet.In x S).
        { intros x Hx; apply mem_queryWitnesses in Hx.
          destruct Hx as [[n vs] [_ Hw]]; apply witness_some in Hw.
          destruct Hw as [v [-> [_ Ht]]]; apply mem_treeOf; exact Ht. }
        set (seen := closeUnder _ es (queryWitnesses t Q)).
        assert (Hcl : forall p q, List.In (p, q) es -> PkgTree.In p seen ->
                      PkgTree.In q seen).
        { apply (closeUnder_closed S); [exact Hes | exact H0 | Lia.lia]. }
        assert (Hall : forall p, Reached dependees Q S p -> PkgTree.In p seen).
        { intros p Hr; induction Hr as [n vs v HQn Hvs HS | p n vs v Hr IH Hd Hvs HS].
          - apply closeUnder_mono, mem_queryWitnesses.
            exists (n, vs); split; [exact HQn |].
            apply mem_treeOf in HS as Ht.
            destruct (witness_met t n vs v Hvs Ht) as [q Hw].
            rewrite (witness_unique S n vs v q Hu HS Hw) in Hw; exact Hw.
          - destruct (Hc1 p (n, vs)) as [q [Hw Hin]];
              [apply in_elements_pkg; exact (reached_in _ _ _ _ Hr) | exact Hd |].
            rewrite (witness_unique S n vs v q Hu HS Hw) in Hin.
            exact (Hcl p (n, v) Hin IH). }
        destruct (List.find _ _) as [p |] eqn:Ef; [| reflexivity].
        apply List.find_some in Ef; destruct Ef as [Hp Hn].
        apply in_elements_pkg in Hp.
        apply Bool.negb_true_iff, mem_tree_false in Hn.
        destruct (Hn (Hall p (Hreach p Hp))).
  Qed.

  Theorem check_resolution : forall R D versions dependees Q S,
      (forall p h, PkgSet.In p R ->
       DepRel.In (p, h) D <-> DependeesSet.In h (dependees p)) ->
      (forall (n : N.t) (vs : VSet.t) (v : V.t), DependeesSet.In (n, vs) Q ->
       VSet.In v vs -> VSet.In v (versions n) -> PkgSet.In (n, v) R) ->
      (forall p (n : N.t) (vs : VSet.t) (v : V.t), PkgSet.In p R ->
       DependeesSet.In (n, vs) (dependees p) -> VSet.In v vs ->
       VSet.In v (versions n) -> PkgSet.In (n, v) R) ->
      check versions dependees Q S = None ->
      PkgSet.Subset S R /\
      (forall (n : N.t) (vs : VSet.t), DependeesSet.In (n, vs) Q ->
       exists v, VSet.In v vs /\ PkgSet.In (n, v) S) /\
      (forall r, PkgSet.In r S -> IsResolution R D r S).
  Proof.
    intros R D versions dependees Q S HD HQ Hstep Hc.
    apply check_spec in Hc; destruct Hc as [Hv [Hu [Hroot [Hclo Hreach]]]].
    assert (Hsub : PkgSet.Subset S R).
    { intros p Hp; specialize (Hreach p Hp); clear Hp.
      induction Hreach as [n vs v Hn Hvs HS | p n vs v _ IH Hd Hvs HS].
      - exact (HQ n vs v Hn Hvs (Hv n v HS)).
      - exact (Hstep p n vs v IH Hd Hvs (Hv n v HS)). }
    split; [exact Hsub |]; split; [exact Hroot |].
    intros r Hr; constructor; [exact Hsub | exact Hr | | exact Hu].
    intros p Hp n vs Hd; apply (HD p _ (Hsub p Hp)) in Hd.
    exact (Hclo p Hp n vs Hd).
  Qed.

  Theorem check_iff : forall R D versions dependees r S,
      (forall p h, PkgSet.In p R ->
       DepRel.In (p, h) D <-> DependeesSet.In h (dependees p)) ->
      (forall (n : N.t) (v : V.t), PkgSet.In (n, v) R -> VSet.In v (versions n)) ->
      (forall p (n : N.t) (vs : VSet.t) (v : V.t), PkgSet.In p R ->
       DependeesSet.In (n, vs) (dependees p) -> VSet.In v vs ->
       VSet.In v (versions n) -> PkgSet.In (n, v) R) ->
      PkgSet.In r R ->
      check versions dependees (rootQuery r) S = None <->
      IsResolution R D r S /\
      (forall p, PkgSet.In p S -> Reached dependees (rootQuery r) S p).
  Proof.
    intros R D versions dependees [rn rv] S HD HR Hstep Hr.
    assert (Hq : forall (n : N.t) (vs : VSet.t),
               DependeesSet.In (n, vs) (rootQuery (rn, rv)) ->
               n = rn /\ forall v, VSet.In v vs <-> v = rv).
    { intros n vs H; cbn [rootQuery] in H; apply DependeesSet.singleton_spec in H.
      injection H as -> ->; split; [reflexivity |].
      intro v; apply VSet.singleton_spec. }
    split.
    - intro Hc; pose proof Hc as Hc'.
      apply check_spec in Hc'; destruct Hc' as [_ [_ [Hroot [_ Hreach]]]].
      apply (check_resolution R D) in Hc; [| exact HD | | exact Hstep].
      + destruct Hc as [_ [_ Hres]]; split; [| exact Hreach].
        apply Hres.
        destruct (Hroot rn (VSet.singleton rv)) as [v [Hv HS]];
          [apply DependeesSet.singleton_spec; reflexivity |].
        apply VSet.singleton_spec in Hv; subst v; exact HS.
      + intros n vs v Hn Hvs _; destruct (Hq n vs Hn) as [-> Hvs'].
        apply Hvs' in Hvs; subst v; exact Hr.
    - intros [[Hsub Hroot Hclo Hu] Hreach]; apply check_spec.
      split; [intros n v HS; exact (HR n v (Hsub _ HS)) |].
      split; [exact Hu |]; split.
      + intros n vs Hn; destruct (Hq n vs Hn) as [-> Hvs].
        exists rv; split; [apply Hvs; reflexivity | exact Hroot].
      + split; [| exact Hreach].
        intros p Hp n vs Hd; apply (HD p _ (Hsub p Hp)) in Hd.
        exact (Hclo p Hp n vs Hd).
  Qed.

  Theorem check_agree : forall versions dependees versions' dependees' Q S,
      (forall (n : N.t) (v : V.t), PkgSet.In (n, v) S ->
       VSet.In v (versions' n) -> VSet.In v (versions n)) ->
      (forall p, PkgSet.In p S -> dependees' p = dependees p) ->
      check versions' dependees' Q S = None ->
      check versions dependees Q S = None.
  Proof.
    intros versions dependees versions' dependees' Q S HV HD Hc.
    apply check_spec in Hc; destruct Hc as [Hv [Hu [Hroot [Hclo Hreach]]]].
    apply check_spec.
    split; [intros n v HS; exact (HV n v HS (Hv n v HS)) |].
    split; [exact Hu |]; split; [exact Hroot |]; split.
    - intros p Hp n vs Hd; rewrite <- (HD p Hp) in Hd; exact (Hclo p Hp n vs Hd).
    - intros p Hp; specialize (Hreach p Hp); clear Hp.
      induction Hreach as [n vs v Hn Hvs HS | p n vs v Hr IH Hd Hvs HS].
      + exact (reached_query dependees Q S n vs v Hn Hvs HS).
      + rewrite (HD p (reached_in _ _ _ _ Hr)) in Hd.
        exact (reached_dependee dependees Q S p n vs v IH Hd Hvs HS).
  Qed.

  Corollary check_iff_sets : forall R D r S,
      check (versions R) (dependees D) (rootQuery r) S = None <->
      IsResolution R D r S /\
      (forall p, PkgSet.In p S -> Reached (dependees D) (rootQuery r) S p).
  Proof.
    intros R D [rn rv] S.
    assert (HD : forall p h, PkgSet.In p R ->
                 DepRel.In (p, h) D <-> DependeesSet.In h (dependees D p))
      by (intros p h _; rewrite mem_dependees; reflexivity).
    assert (HR : forall (n : N.t) (v : V.t),
                 PkgSet.In (n, v) R -> VSet.In v (versions R n))
      by (intros n v H; apply mem_versions; exact H).
    assert (Hstep : forall p (n : N.t) (vs : VSet.t) (v : V.t), PkgSet.In p R ->
                    DependeesSet.In (n, vs) (dependees D p) -> VSet.In v vs ->
                    VSet.In v (versions R n) -> PkgSet.In (n, v) R)
      by (intros p n vs v _ _ _ H; apply mem_versions; exact H).
    split.
    - intro Hc; pose proof Hc as Hc'; apply check_spec in Hc'.
      destruct Hc' as [Hv [_ [Hroot _]]].
      destruct (Hroot rn (VSet.singleton rv)) as [v [Hvs HS]];
        [apply DependeesSet.singleton_spec; reflexivity |].
      apply VSet.singleton_spec in Hvs; subst v.
      refine (proj1 (check_iff R D _ _ (rn, rv) S HD HR Hstep _) Hc).
      apply mem_versions, Hv; exact HS.
    - intros [Hres Hreach].
      refine (proj2 (check_iff R D _ _ (rn, rv) S HD HR Hstep
                       (res_subset _ _ _ _ Hres _ (res_root_mem _ _ _ _ Hres)))
                _).
      split; [exact Hres | exact Hreach].
  Qed.

  Module Merge.
    Definition mergedVS (D : DepRel.t) (p : Pkg.t) (n : N.t) : VSet.t :=
      VSet.filter
        (fun v => DepRel.for_all
            (fun '(q, (m, vs)) =>
                      if Pkg.eq_dec q p
                      then if N.eq_dec m n then VSet.mem v vs else true
                      else true)
            D)
        (DepRel.fold (fun '(q, (m, vs)) acc =>
             if Pkg.eq_dec q p
             then if N.eq_dec m n then VSet.union vs acc else acc
             else acc)
           D VSet.empty).

    Module SOdv := SetOps DepElt V DepRel VSet.
    Lemma mergedVS_union_spec : forall D p n v,
        VSet.In v
          (DepRel.fold (fun '(q, (m, vs)) acc =>
               if Pkg.eq_dec q p
               then if N.eq_dec m n then VSet.union vs acc else acc
               else acc)
             D VSet.empty) <->
        exists vs, DepRel.In (p, (n, vs)) D /\ VSet.In v vs.
    Proof.
      intros D p n v.
      rewrite (SOdv.in_fold _
        (fun e => if Pkg.eq_dec (fst e) p
                  then if N.eq_dec (fst (snd e)) n
                       then snd (snd e) else VSet.empty
                  else VSet.empty)).
      2:{ intros [q [m vs]] a y; simpl; pose proof (SOdv.empty_in y).
          destruct (Pkg.eq_dec q p); [destruct (N.eq_dec m n) |];
            rewrite ?VSet.union_spec; tauto. }
      pose proof (SOdv.empty_in v) as E0; split.
      - intros [H | [[q [m vs]] [HeD He]]]; [tauto | simpl in He].
        destruct (Pkg.eq_dec q p) as [-> | _];
          [destruct (N.eq_dec m n) as [-> | _] |]; [| tauto | tauto].
        exists vs; split; assumption.
      - intros [vs [HD Hv]].
        right; exists (p, (n, vs)); simpl; rewrite !dec_refl; auto.
    Qed.

    Lemma mem_mergedVS : forall D p n v,
        VSet.In v (mergedVS D p n) <->
        (exists vs, DepRel.In (p, (n, vs)) D) /\
        (forall vs, DepRel.In (p, (n, vs)) D -> VSet.In v vs).
    Proof.
      intros D p n v; unfold mergedVS.
      rewrite VSet.filter_spec'.
      rewrite mergedVS_union_spec.
      rewrite DepRel.for_all_spec'.
      split.
      - intros [[vs [HD Hv]] Hall].
        split; [exists vs; exact HD |].
        intros vs' HD'.
        specialize (Hall _ HD'); simpl in Hall; rewrite !dec_refl in Hall.
        apply VSet.mem_spec; exact Hall.
      - intros [[vs0 H0] Hall].
        split.
        + exists vs0; split; [exact H0 | apply Hall; exact H0].
        + intros [q [m vs]] He; simpl.
          destruct (Pkg.eq_dec q p) as [-> | NE]; [| reflexivity].
          destruct (N.eq_dec m n) as [-> | NE]; [| reflexivity].
          apply VSet.mem_spec; apply Hall; exact He.
    Qed.

    Definition merge (D : DepRel.t) : DepRel.t :=
      DepRel.fold (fun '(q, (n, _)) acc =>
          DepRel.add (q, (n, mergedVS D q n)) acc)
        D DepRel.empty.

    Module SOdd := SetOps DepElt DepElt DepRel DepRel.
    Lemma mem_merge : forall D p n vs,
        DepRel.In (p, (n, vs)) (merge D) <->
        (exists vs0, DepRel.In (p, (n, vs0)) D) /\ vs = mergedVS D p n.
    Proof.
      intros D p n vs; unfold merge.
      rewrite (SOdd.in_fold _
        (fun e => DepRel.singleton
                    (fst e, (fst (snd e), mergedVS D (fst e) (fst (snd e)))))).
      2:{ intros [q [m ws]] a y; simpl.
          rewrite SOdd.add_in, SOdd.singleton_in; tauto. }
      split.
      - intros [H | [e [HeD He]]].
        + exfalso; exact (SOdd.empty_in _ H).
        + destruct e as [q [m ws]]; rewrite SOdd.singleton_in in He;
            simpl in He.
          injection He as -> -> ->.
          split; [exists ws; exact HeD | reflexivity].
      - intros [[vs0 H0] ->].
        right; exists (p, (n, vs0)); split; [exact H0 | simpl].
        rewrite SOdd.singleton_in; reflexivity.
    Qed.

    Theorem merge_functionalInName : forall D, FunctionalInName (merge D).
    Proof.
      intros D p n vs1 vs2 H1 H2.
      apply mem_merge in H1; apply mem_merge in H2.
      destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity.
    Qed.

    Theorem merge_resolution_iff : forall R D r S,
        IsResolution R (merge D) r S <-> IsResolution R D r S.
    Proof.
      intros R D r S; split; intros [Hsub Hroot Hdep Huniq]; constructor;
        try assumption.
      - intros p Hp m vs HD.
        destruct (Hdep p Hp m (mergedVS D p m)) as [v [Hv HvS]].
        + apply mem_merge; split; [exists vs; exact HD | reflexivity].
        + apply mem_mergedVS in Hv; destruct Hv as [_ Hall].
          exists v; split; [apply Hall; exact HD | exact HvS].
      - intros p Hp m ws Hmem.
        apply mem_merge in Hmem; destruct Hmem as [[vs0 H0] ->].
        destruct (Hdep p Hp m vs0 H0) as [v [Hv HvS]].
        exists v; split; [| exact HvS].
        apply mem_mergedVS; split; [exists vs0; exact H0 |].
        intros vs' HD'.
        destruct (Hdep p Hp m vs' HD') as [v' [Hv' Hv'S]].
        assert (v = v') as -> by (apply (Huniq m); assumption).
        exact Hv'.
    Qed.
  End Merge.
End Core.
