From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core.

Create HintDb cmp_virt.
Create Rewrite HintDb cmp_virt.

Module Virtual (N V : UsualOrderedType).
  Module C := Core N V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive VTop : Type :=
  | VTVal (v : V.t)
  | VTTop.

  Module VF := UOTCompareFacts V.
  #[local] Hint Rewrite VF.compare_eq_iff : cmp_virt.
  #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_virt.
  #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_virt.

  Module VTComp <: ComparableType.
    Definition t := VTop.
    Definition compare (x y : t) : comparison :=
      match x, y with
      | VTVal v1, VTVal v2 => V.compare v1 v2
      | VTVal _, VTTop => Lt
      | VTTop, VTVal _ => Gt
      | VTTop, VTTop => Eq
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_virt. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_virt. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_virt. Qed.
  End VTComp.
  Module VTOT := UOTFromCompare VTComp.

  Module Provided := PairUOT N VTOT.
  Module ProvElt := PairUOT Pkg Provided.
  Module ProvidesRel := FSetUOT ProvElt.

  Module Depender := PairUOT N Pkg.
  Module RhoElt := PairUOT Pkg Depender.
  Module RhoRel := FSetUOT RhoElt.

  Definition MemTop (v : VTop) (vs : VSet.t) : Prop :=
    match v with
    | VTTop => True
    | VTVal v' => VSet.In v' vs
    end.

  Definition memTopb (v : VTop) (vs : VSet.t) : bool :=
    match v with
    | VTTop => true
    | VTVal v' => VSet.mem v' vs
    end.

  Lemma memTopb_iff : forall v vs, memTopb v vs = true <-> MemTop v vs.
  Proof.
    intros [v' |] vs; simpl.
    - apply VSet.mem_spec.
    - split; [intros _; exact I | reflexivity].
  Qed.

  Record IsResolution
      (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t)
      (r : Pkg.t) (S : PkgSet.t) (rho : RhoRel.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_virtual_dep_closure :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          C.DepRel.In (p, (n, vs)) D ->
          (exists v, VSet.In v vs /\ PkgSet.In (n, v) S) \/
          (exists! q, PkgSet.In q S /\
             exists v, MemTop v vs /\ ProvidesRel.In (q, (n, v)) Pi /\
               RhoRel.In (q, (n, p)) rho)
    ; res_version_unique : C.VersionUnique S
    ; res_provider_subset :
        forall (q : Pkg.t) (n : N.t) (p : Pkg.t),
          RhoRel.In (q, (n, p)) rho -> PkgSet.In q S /\ PkgSet.In p S }.

  Module Reduction.

    Module PkgN := PairUOT Pkg N.
    Module PkgNF := UOTCompareFacts PkgN.
    Module NF := UOTCompareFacts N.
    #[local] Hint Rewrite PkgNF.compare_eq_iff NF.compare_eq_iff : cmp_virt.
    #[local] Hint Extern 1 => cmp_by PkgNF.compare_antisym : cmp_virt.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_virt.
    #[local] Hint Extern 1 => cmp_by PkgNF.compare_lt_trans : cmp_virt.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_virt.

    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Selector (p : Pkg.t) (m : N.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, Selector _ _ => Lt
        | Selector _ _, Orig _ => Gt
        | Selector p1 m1, Selector p2 m2 => PkgN.compare (p1, m1) (p2, m2)
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_virt. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_virt. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_virt. Qed.
    End Name.

    Module NV := PairUOT N V.
    Module NVF := UOTCompareFacts NV.
    #[local] Hint Rewrite NVF.compare_eq_iff : cmp_virt.
    #[local] Hint Extern 1 => cmp_by NVF.compare_antisym : cmp_virt.
    #[local] Hint Extern 1 => cmp_by NVF.compare_lt_trans : cmp_virt.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Provider (n : N.t) (w : V.t).
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, Provider _ _ => Lt
        | Provider _ _, Orig _ => Gt
        | Provider n1 w1, Provider n2 w2 => NV.compare (n1, w1) (n2, w2)
        end.

      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_virt. Qed.

      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_virt. Qed.

      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_virt. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module T := Core NameOT VersionOT.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      let '(n, v) := p in (Name.Orig n, Version.Orig v).

    Module SOsp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition embedSet (S : PkgSet.t) : T.PkgSet.t :=
      SOsp.map embedPkg S.

    Module SOvv := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvv.map Version.Orig vs.

    Definition HasProvider
        (Pi : ProvidesRel.t) (n : N.t) (vs : VSet.t) : Prop :=
      exists q v, ProvidesRel.In (q, (n, v)) Pi /\ MemTop v vs.

    Module NEqb := UOTEqb N.

    Definition hasProviderb
        (Pi : ProvidesRel.t) (n : N.t) (vs : VSet.t) : bool :=
      ProvidesRel.exists_ (fun '(_, (m, v)) =>
          andb (NEqb.eqb m n) (memTopb v vs))
        Pi.

    Lemma hasProviderb_iff : forall Pi n vs,
        hasProviderb Pi n vs = true <-> HasProvider Pi n vs.
    Proof.
      intros Pi n vs; unfold hasProviderb, HasProvider.
      rewrite ProvidesRel.exists_spec'.
      unfold ProvidesRel.Exists; split.
      - intros [t [Ht Hb]]; destruct t as [q [n' v]]; cbn beta iota in Hb.
        apply andb_prop in Hb; destruct Hb as [He Hm].
        apply NEqb.eqb_true_iff in He as ->.
        exists q, v; split; [exact Ht | apply memTopb_iff; exact Hm].
      - intros [q [v [Hin Hm]]].
        exists (q, (n, v)); split; [exact Hin | cbn beta iota].
        rewrite NEqb.eqb_refl; cbn [andb]; apply memTopb_iff; exact Hm.
    Qed.

    (* A guard inside a pattern-matching comprehension body is only exposed
       once the element is destructed, too late for mem_filterMap_if. *)
    Lemma if_some_iff : forall (A : Type) (b : bool) (x y : A),
        (if b then Some x else None) = Some y <-> b = true /\ x = y.
    Proof. intros A [|] x y; cbn; intuition congruence. Qed.

    Module SOpp := SetOps ProvElt T.Pkg ProvidesRel T.PkgSet.
    Definition realProviderBlock (Pi : ProvidesRel.t) (p : Pkg.t) (n : N.t)
        (vs : VSet.t) : T.PkgSet.t :=
      SOpp.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n) (memTopb v vs)
          then Some (Name.Selector p n, Version.Provider (fst q) (snd q))
          else None)
        Pi.

    Lemma mem_realProviderBlock :
      forall Pi (p : Pkg.t) (n : N.t) (vs : VSet.t) y,
        T.PkgSet.In y (realProviderBlock Pi p n vs) <->
        exists m u v, ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
          y = (Name.Selector p n, Version.Provider m u).
    Proof.
      intros Pi p n vs y; unfold realProviderBlock.
      rewrite SOpp.mem_filterMap.
      split.
      - intros [[[m u] [m0 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        apply if_some_iff in Hy; destruct Hy as [Hc <-].
        rewrite Bool.andb_true_iff, NEqb.eqb_true_iff, memTopb_iff in Hc.
        destruct Hc as [-> Hm]; exists m, u, v; auto.
      - intros (m & u & v & Hin & Hm & ->).
        exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        apply if_some_iff; rewrite Bool.andb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff; auto.
    Qed.

    Module SOvp := SetOps V T.Pkg VSet T.PkgSet.
    Definition realDirectBlock (R : PkgSet.t) (p : Pkg.t) (n : N.t)
        (vs : VSet.t) : T.PkgSet.t :=
      SOvp.filterMap (fun u =>
          if PkgSet.mem (n, u) R
          then Some (Name.Selector p n, Version.Provider n u)
          else None)
        vs.

    Lemma mem_realDirectBlock :
      forall R (p : Pkg.t) (n : N.t) (vs : VSet.t) y,
        T.PkgSet.In y (realDirectBlock R p n vs) <->
        exists u, VSet.In u vs /\ PkgSet.In (n, u) R /\
          y = (Name.Selector p n, Version.Provider n u).
    Proof.
      intros R p n vs y; unfold realDirectBlock.
      rewrite SOvp.mem_filterMap_if; cbn beta.
      setoid_rewrite PkgSet.mem_spec; reflexivity.
    Qed.

    Module SOdp := SetOps C.DepElt T.Pkg C.DepRel T.PkgSet.
    Definition reduceReal (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t) :
        T.PkgSet.t :=
      T.PkgSet.union (embedSet R)
        (T.PkgSet.union
           (SOdp.unionMap (fun '(p, (n, vs)) =>
                realProviderBlock Pi p n vs)
              D)
           (SOdp.unionMap (fun '(p, (n, vs)) =>
                if hasProviderb Pi n vs
                then realDirectBlock R p n vs
                else T.PkgSet.empty)
              D)).

    (* Provider and direct selector versions coincide when the provider is
       the depended-on name itself, so those two are chosen by name, not by
       the constructor tactic. *)
    Inductive RealSpec (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t)
        : T.Pkg.t -> Prop :=
    | RealOrig : forall n v,
        PkgSet.In (n, v) R -> RealSpec R D Pi (Name.Orig n, Version.Orig v)
    | RealProvider : forall p n vs m u v,
        C.DepRel.In (p, (n, vs)) D -> ProvidesRel.In ((m, u), (n, v)) Pi ->
        MemTop v vs ->
        RealSpec R D Pi (Name.Selector p n, Version.Provider m u)
    | RealDirect : forall p n vs u,
        C.DepRel.In (p, (n, vs)) D -> HasProvider Pi n vs -> VSet.In u vs ->
        PkgSet.In (n, u) R ->
        RealSpec R D Pi (Name.Selector p n, Version.Provider n u).

    Lemma mem_reduceReal : forall R D Pi y,
        T.PkgSet.In y (reduceReal R D Pi) <-> RealSpec R D Pi y.
    Proof.
      intros R D Pi y; unfold reduceReal, embedSet.
      rewrite !T.PkgSet.union_spec, SOsp.mem_map, !SOdp.mem_unionMap.
      split.
      - intros [([n v] & HR & ->) | [([p [n vs]] & HD & He)
                                   | ([p [n vs]] & HD & He)]].
        + exact (RealOrig R D Pi n v HR).
        + cbn beta iota in He; apply mem_realProviderBlock in He.
          mem_destruct; eapply RealProvider; eassumption.
        + cbn beta iota in He; apply SOdp.in_if_empty in He.
          destruct He as [Hb He]; apply hasProviderb_iff in Hb.
          apply mem_realDirectBlock in He; mem_destruct.
          eapply RealDirect; eassumption.
      - destruct 1 as [n v HR | p n vs m u v HD HP Hm | p n vs u HD Hb Hu HR].
        + left; exists (n, v); auto.
        + right; left; exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply mem_realProviderBlock; exists m, u, v; auto.
        + right; right; exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply SOdp.in_if_empty; rewrite hasProviderb_iff.
          split; [exact Hb | apply mem_realDirectBlock; exists u; auto].
    Qed.

    Module SOpv := SetOps ProvElt VersionOT ProvidesRel T.VSet.
    Definition selectorVersions (R : PkgSet.t) (Pi : ProvidesRel.t)
        (n : N.t) (vs : VSet.t) : T.VSet.t :=
      T.VSet.union
        (SOpv.filterMap (fun '(q, (n', v)) =>
             if andb (NEqb.eqb n' n) (memTopb v vs)
             then Some (Version.Provider (fst q) (snd q))
             else None)
           Pi)
        (SOvv.filterMap (fun u =>
             if PkgSet.mem (n, u) R
             then Some (Version.Provider n u)
             else None)
           vs).

    Lemma mem_selectorVersions : forall R Pi n vs y,
        T.VSet.In y (selectorVersions R Pi n vs) <->
        (exists m u v, ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
           y = Version.Provider m u) \/
        (exists u,
           VSet.In u vs /\ PkgSet.In (n, u) R /\ y = Version.Provider n u).
    Proof.
      intros R Pi n vs y; unfold selectorVersions.
      rewrite T.VSet.union_spec, SOpv.mem_filterMap, SOvv.mem_filterMap_if.
      cbn beta; setoid_rewrite PkgSet.mem_spec; apply or_iff_compat_r.
      split.
      - intros [[[m u] [n' v]] [Ht Hy]]; cbn [fst snd] in Hy.
        apply if_some_iff in Hy; destruct Hy as [Hc <-].
        rewrite Bool.andb_true_iff, NEqb.eqb_true_iff, memTopb_iff in Hc.
        destruct Hc as [-> Hm]; exists m, u, v; auto.
      - intros (m & u & v & Hin & Hm & ->).
        exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        apply if_some_iff; rewrite Bool.andb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff; auto.
    Qed.

    Module SOpd := SetOps ProvElt T.DepElt ProvidesRel T.DepRel.
    Definition depsProviderBlock (Pi : ProvidesRel.t) (p : Pkg.t) (n : N.t)
        (vs : VSet.t) : T.DepRel.t :=
      SOpd.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n) (memTopb v vs)
          then Some ((Name.Selector p n, Version.Provider (fst q) (snd q)),
                     (Name.Orig (fst q),
                      T.VSet.singleton (Version.Orig (snd q))))
          else None)
        Pi.

    Lemma mem_depsProviderBlock :
      forall Pi (p : Pkg.t) (n : N.t) (vs : VSet.t) y,
        T.DepRel.In y (depsProviderBlock Pi p n vs) <->
        exists m u v, ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
          y = ((Name.Selector p n, Version.Provider m u),
               (Name.Orig m, T.VSet.singleton (Version.Orig u))).
    Proof.
      intros Pi p n vs y; unfold depsProviderBlock.
      rewrite SOpd.mem_filterMap.
      split.
      - intros [[[m u] [m0 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        apply if_some_iff in Hy; destruct Hy as [Hc <-].
        rewrite Bool.andb_true_iff, NEqb.eqb_true_iff, memTopb_iff in Hc.
        destruct Hc as [-> Hm]; exists m, u, v; auto.
      - intros (m & u & v & Hin & Hm & ->).
        exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        apply if_some_iff; rewrite Bool.andb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff; auto.
    Qed.

    Module SOvd := SetOps V T.DepElt VSet T.DepRel.
    Definition depsDirectBlock (R : PkgSet.t) (p : Pkg.t) (n : N.t)
        (vs : VSet.t) : T.DepRel.t :=
      SOvd.filterMap (fun u =>
          if PkgSet.mem (n, u) R
          then Some ((Name.Selector p n, Version.Provider n u),
                     (Name.Orig n, T.VSet.singleton (Version.Orig u)))
          else None)
        vs.

    Lemma mem_depsDirectBlock :
      forall R (p : Pkg.t) (n : N.t) (vs : VSet.t) y,
        T.DepRel.In y (depsDirectBlock R p n vs) <->
        exists u, VSet.In u vs /\ PkgSet.In (n, u) R /\
          y = ((Name.Selector p n, Version.Provider n u),
               (Name.Orig n, T.VSet.singleton (Version.Orig u))).
    Proof.
      intros R p n vs y; unfold depsDirectBlock.
      rewrite SOvd.mem_filterMap_if; cbn beta.
      setoid_rewrite PkgSet.mem_spec; reflexivity.
    Qed.

    Module SOdd := SetOps C.DepElt T.DepElt C.DepRel T.DepRel.
    Definition reduceDeps (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t) :
        T.DepRel.t :=
      T.DepRel.union
        (SOdd.filterMap (fun '(p, (n, vs)) =>
             if hasProviderb Pi n vs then None
             else Some (embedPkg p, (Name.Orig n, embedVS vs)))
           D)
        (T.DepRel.union
           (SOdd.filterMap (fun '(p, (n, vs)) =>
                if hasProviderb Pi n vs
                then Some (embedPkg p,
                           (Name.Selector p n, selectorVersions R Pi n vs))
                else None)
              D)
           (T.DepRel.union
              (SOdd.unionMap (fun '(p, (n, vs)) =>
                   depsProviderBlock Pi p n vs)
                 D)
              (SOdd.unionMap (fun '(p, (n, vs)) =>
                   if hasProviderb Pi n vs
                   then depsDirectBlock R p n vs
                   else T.DepRel.empty)
                 D))).

    (* Embedded packages are written as pairs of constructors so that
       inversion can tell the four kinds of edge apart by their source. *)
    Inductive DepsSpec (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t)
        : T.DepElt.t -> Prop :=
    | DepsOrig : forall pn pv n vs,
        C.DepRel.In ((pn, pv), (n, vs)) D -> ~ HasProvider Pi n vs ->
        DepsSpec R D Pi
          ((Name.Orig pn, Version.Orig pv), (Name.Orig n, embedVS vs))
    | DepsSelector : forall pn pv n vs,
        C.DepRel.In ((pn, pv), (n, vs)) D -> HasProvider Pi n vs ->
        DepsSpec R D Pi
          ((Name.Orig pn, Version.Orig pv),
           (Name.Selector (pn, pv) n, selectorVersions R Pi n vs))
    | DepsProvider : forall p n vs m u v,
        C.DepRel.In (p, (n, vs)) D -> ProvidesRel.In ((m, u), (n, v)) Pi ->
        MemTop v vs ->
        DepsSpec R D Pi
          ((Name.Selector p n, Version.Provider m u),
           (Name.Orig m, T.VSet.singleton (Version.Orig u)))
    | DepsDirect : forall p n vs u,
        C.DepRel.In (p, (n, vs)) D -> HasProvider Pi n vs -> VSet.In u vs ->
        PkgSet.In (n, u) R ->
        DepsSpec R D Pi
          ((Name.Selector p n, Version.Provider n u),
           (Name.Orig n, T.VSet.singleton (Version.Orig u))).

    Lemma mem_reduceDeps : forall R D Pi y,
        T.DepRel.In y (reduceDeps R D Pi) <-> DepsSpec R D Pi y.
    Proof.
      intros R D Pi y; unfold reduceDeps.
      rewrite !T.DepRel.union_spec, !SOdd.mem_filterMap, !SOdd.mem_unionMap.
      split.
      - intros [([[pn pv] [n vs]] & HD & He)
               | [([[pn pv] [n vs]] & HD & He)
                 | [([p [n vs]] & HD & He) | ([p [n vs]] & HD & He)]]];
          cbn beta iota in He.
        + destruct (hasProviderb Pi n vs) eqn:Hb; [discriminate |].
          injection He as <-; apply DepsOrig; [exact HD |].
          rewrite <- hasProviderb_iff, Hb; discriminate.
        + destruct (hasProviderb Pi n vs) eqn:Hb; [| discriminate].
          injection He as <-; apply hasProviderb_iff in Hb.
          apply DepsSelector; assumption.
        + apply mem_depsProviderBlock in He; mem_destruct.
          eapply DepsProvider; eassumption.
        + apply SOdd.in_if_empty in He; destruct He as [Hb He].
          apply hasProviderb_iff in Hb; apply mem_depsDirectBlock in He.
          mem_destruct; eapply DepsDirect; eassumption.
      - destruct 1 as [pn pv n vs HD Hb | pn pv n vs HD Hb
                      | p n vs m u v HD HP Hm | p n vs u HD Hb Hu HR].
        + left; exists ((pn, pv), (n, vs)); split; [exact HD | cbn beta iota].
          destruct (hasProviderb Pi n vs) eqn:Hb'; [| reflexivity].
          apply hasProviderb_iff in Hb'; contradiction.
        + right; left; exists ((pn, pv), (n, vs)).
          split; [exact HD | cbn beta iota].
          apply hasProviderb_iff in Hb; rewrite Hb; reflexivity.
        + right; right; left; exists (p, (n, vs)).
          split; [exact HD | cbn beta iota].
          apply mem_depsProviderBlock; exists m, u, v; auto.
        + right; right; right; exists (p, (n, vs)).
          split; [exact HD | cbn beta iota].
          apply SOdd.in_if_empty; rewrite hasProviderb_iff.
          split; [exact Hb | apply mem_depsDirectBlock; exists u; auto].
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

    Definition virtualResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_virtualResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (virtualResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold virtualResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma embedPkg_mem_real : forall (p : Pkg.t) R D Pi,
        T.PkgSet.In (embedPkg p) (reduceReal R D Pi) -> PkgSet.In p R.
    Proof.
      intros [n v] R D Pi H; apply mem_reduceReal in H.
      cbn [embedPkg] in H; inversion H; assumption.
    Qed.

    Module SOpr := SetOps ProvElt RhoElt ProvidesRel RhoRel.
    Definition rhoBlock (Pi : ProvidesRel.t) (S : T.PkgSet.t) (p : Pkg.t)
        (n : N.t) (vs : VSet.t) : RhoRel.t :=
      SOpr.filterMap (fun '(q, (n', v)) =>
          if andb (NEqb.eqb n' n)
               (andb (memTopb v vs)
                  (andb (T.PkgSet.mem (embedPkg p) S)
                     (T.PkgSet.mem
                        (Name.Selector p n,
                         Version.Provider (fst q) (snd q)) S)))
          then Some (q, (n, p))
          else None)
        Pi.

    Lemma mem_rhoBlock :
      forall Pi (S : T.PkgSet.t) (p : Pkg.t) (n : N.t) (vs : VSet.t)
             (m : N.t) (u : V.t) (m' : N.t) (p' : Pkg.t),
        RhoRel.In ((m, u), (m', p')) (rhoBlock Pi S p n vs) <->
        (exists v, ProvidesRel.In ((m, u), (n, v)) Pi /\ MemTop v vs /\
           T.PkgSet.In (embedPkg p) S /\
           T.PkgSet.In (Name.Selector p n, Version.Provider m u) S /\
           m' = n /\ p' = p).
    Proof.
      intros Pi S p n vs m u m' p'; unfold rhoBlock.
      rewrite SOpr.mem_filterMap.
      split.
      - intros [[[m0 u0] [m1 v]] [Ht Hy]]; cbn [fst snd] in Hy.
        apply if_some_iff in Hy; destruct Hy as [Hc Hy].
        injection Hy as <- <- <- <-.
        rewrite !Bool.andb_true_iff, NEqb.eqb_true_iff, memTopb_iff,
          !T.PkgSet.mem_spec in Hc.
        destruct Hc as (-> & Hm & HpS & HselS); exists v; auto 8.
      - intros (v & Hin & Hm & HpS & HselS & -> & ->).
        exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        apply if_some_iff; rewrite !Bool.andb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff, !T.PkgSet.mem_spec; auto 8.
    Qed.

    Module SOdr := SetOps C.DepElt RhoElt C.DepRel RhoRel.
    Definition providers (D : C.DepRel.t) (Pi : ProvidesRel.t)
        (S : T.PkgSet.t) : RhoRel.t :=
      SOdr.unionMap (fun '(p, (n, vs)) => rhoBlock Pi S p n vs) D.

    Lemma mem_providers :
      forall D Pi S (m : N.t) (u : V.t) (p : Pkg.t) (n : N.t),
        RhoRel.In ((m, u), (n, p)) (providers D Pi S) <->
        exists vs, C.DepRel.In (p, (n, vs)) D /\
          exists v, MemTop v vs /\ ProvidesRel.In ((m, u), (n, v)) Pi /\
            T.PkgSet.In (embedPkg p) S /\
            T.PkgSet.In (Name.Selector p n, Version.Provider m u) S.
    Proof.
      intros D Pi S m u p n; unfold providers; rewrite SOdr.mem_unionMap.
      split.
      - intros [[p0 [n0 vs]] [HeD He]]; cbn beta iota in He.
        apply mem_rhoBlock in He.
        destruct He as [v [Hin [Hm [HpS [HselS [-> ->]]]]]].
        exists vs; split; [exact HeD |].
        exists v; repeat split; assumption.
      - intros [vs [HD [v [Hm [HP [HpS HselS]]]]]].
        exists (p, (n, vs)); split; [exact HD | cbn beta iota].
        apply mem_rhoBlock.
        exists v; split; [exact HP |].
        split; [exact Hm | split; [exact HpS | split; [exact HselS |]]].
        split; reflexivity.
    Qed.

    Theorem virtual_soundness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t)
             (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D Pi) (reduceDeps R D Pi)
          (embedPkg r) S ->
        IsResolution R D Pi r (virtualResolution S) (providers D Pi S).
    Proof.
      intros R D Pi r S [Hsub Hroot Hdep Huniq].
      assert (Hsel_emb : forall (m0 : N.t) (u0 : V.t) (p0 : Pkg.t)
                                (n0 : N.t) v0 vs0,
          C.DepRel.In (p0, (n0, vs0)) D ->
          ProvidesRel.In ((m0, u0), (n0, v0)) Pi -> MemTop v0 vs0 ->
          T.PkgSet.In (Name.Selector p0 n0, Version.Provider m0 u0) S ->
          T.PkgSet.In (embedPkg (m0, u0)) S).
      { intros m0 u0 p0 n0 v0 vs0 HD HP HM HselS.
        assert (Hd3 : T.DepRel.In
            ((Name.Selector p0 n0, Version.Provider m0 u0),
             (Name.Orig m0, T.VSet.singleton (Version.Orig u0)))
            (reduceDeps R D Pi))
          by (apply mem_reduceDeps; eapply DepsProvider; eassumption).
        destruct (Hdep _ HselS _ _ Hd3) as [w [Hw HwS]].
        apply T.VSet.singleton_spec in Hw; rewrite Hw in HwS.
        exact HwS. }
      constructor.
      - intros p Hp; apply mem_virtualResolution in Hp.
        exact (embedPkg_mem_real _ _ _ _ (Hsub _ Hp)).
      - apply mem_virtualResolution; exact Hroot.
      - intros [pn pv] Hp n vs HD.
        apply mem_virtualResolution in Hp.
        destruct (hasProviderb Pi n vs) eqn:Hb.
        + apply hasProviderb_iff in Hb.
          assert (Hd2 : T.DepRel.In
              (embedPkg (pn, pv),
               (Name.Selector (pn, pv) n, selectorVersions R Pi n vs))
              (reduceDeps R D Pi))
            by (apply mem_reduceDeps; apply DepsSelector; assumption).
          destruct (Hdep _ Hp _ _ Hd2) as [sv [Hsv HsvS]].
          apply mem_selectorVersions in Hsv.
          destruct Hsv as [[m [u [v [HP [Hm Hsv]]]]] | [u [Hu [HuR Hsv]]]].
          * subst sv; right.
            assert (HqS := Hsel_emb m u (pn, pv) n v vs HD HP Hm HsvS).
            exists (m, u); split.
            { split; [apply mem_virtualResolution; exact HqS |].
              exists v; split; [exact Hm |]; split; [exact HP |].
              apply mem_providers.
              exists vs; split; [exact HD |].
              exists v; repeat split; assumption. }
            { intros [m' u'] [Hq'S [v' [Hm' [HP' Hrho']]]].
              apply mem_providers in Hrho'.
              destruct Hrho' as [vs' [HD' [v0 [Hm0 [HP0 [HpS0 HselS0]]]]]].
              assert (Hveq := Huniq (Name.Selector (pn, pv) n)
                                (Version.Provider m u)
                                (Version.Provider m' u') HsvS HselS0).
              injection Hveq as H1 H2.
              rewrite H1, H2; reflexivity. }
          * subst sv.
            assert (Hd4 : T.DepRel.In
                ((Name.Selector (pn, pv) n, Version.Provider n u),
                 (Name.Orig n, T.VSet.singleton (Version.Orig u)))
                (reduceDeps R D Pi))
              by (apply mem_reduceDeps; eapply DepsDirect; eassumption).
            destruct (Hdep _ HsvS _ _ Hd4) as [w [Hw HwS]].
            apply T.VSet.singleton_spec in Hw; rewrite Hw in HwS.
            left; exists u; split;
              [exact Hu | apply mem_virtualResolution; exact HwS].
        + assert (Hd1 : T.DepRel.In
              (embedPkg (pn, pv), (Name.Orig n, embedVS vs))
              (reduceDeps R D Pi)).
          { apply mem_reduceDeps; apply DepsOrig; [exact HD |].
            rewrite <- hasProviderb_iff, Hb; discriminate. }
          destruct (Hdep _ Hp _ _ Hd1) as [w [Hw HwS]].
          unfold embedVS in Hw; apply SOvv.mem_map in Hw;
            destruct Hw as [u [Hu ->]].
          left; exists u; split;
            [exact Hu | apply mem_virtualResolution; exact HwS].
      - intros n v v' Hv Hv'.
        apply mem_virtualResolution in Hv; apply mem_virtualResolution in Hv'.
        assert (H := Huniq (Name.Orig n)
                       (Version.Orig v) (Version.Orig v') Hv Hv').
        injection H as H; exact H.
      - intros [m u] n p Hrho.
        apply mem_providers in Hrho.
        destruct Hrho as [vs [HD [v [Hm [HP [HpS HselS]]]]]].
        split; apply mem_virtualResolution.
        + exact (Hsel_emb m u p n v vs HD HP Hm HselS).
        + exact HpS.
    Qed.

    Module PkgEqb := UOTEqb Pkg.
    Module SOkp := SetOps Pkg ProvElt PkgSet ProvidesRel.
    Definition rhoProviders (S_Pi : PkgSet.t) (rho : RhoRel.t)
        (Pi : ProvidesRel.t) (p : Pkg.t) (n : N.t) (vs : VSet.t) : PkgSet.t :=
      SOkp.filterExists
        (fun q '(q', (m, v)) =>
            andb (PkgEqb.eqb q' q)
              (andb (NEqb.eqb m n)
                 (andb (memTopb v vs) (RhoRel.mem (q, (n, p)) rho))))
        Pi S_Pi.

    Lemma mem_rhoProviders :
      forall S_Pi rho Pi (p : Pkg.t) (n : N.t) vs (q : Pkg.t),
        PkgSet.In q (rhoProviders S_Pi rho Pi p n vs) <->
        PkgSet.In q S_Pi /\
        exists v, MemTop v vs /\ ProvidesRel.In (q, (n, v)) Pi /\
          RhoRel.In (q, (n, p)) rho.
    Proof.
      intros S_Pi rho Pi p n vs q; unfold rhoProviders.
      rewrite SOkp.mem_filterExists; apply and_iff_compat_l.
      split.
      - intros [[q' [m v]] [Ht Hb]]; cbn beta iota in Hb.
        rewrite !Bool.andb_true_iff, PkgEqb.eqb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff, RhoRel.mem_spec in Hb.
        destruct Hb as (-> & -> & Hm & Hr); exists v; auto.
      - intros (v & Hm & HP & Hr).
        exists (q, (n, v)); split; [exact HP | cbn beta iota].
        rewrite !Bool.andb_true_iff, PkgEqb.eqb_true_iff, NEqb.eqb_true_iff,
          memTopb_iff, RhoRel.mem_spec; auto.
    Qed.

    (* Any element of the first nonempty candidate class works; min_elt makes
       the choice deterministic and computable. *)
    Definition chooseSelector (S_Pi : PkgSet.t) (rho : RhoRel.t)
        (Pi : ProvidesRel.t) (p : Pkg.t) (n : N.t) (vs : VSet.t) :
        Version.t :=
      match PkgSet.min_elt (rhoProviders S_Pi rho Pi p n vs) with
      | Some q => Version.Provider (fst q) (snd q)
      | None =>
          let cand2 := VSet.filter (fun u => PkgSet.mem (n, u) S_Pi) vs in
          match VSet.min_elt cand2 with
          | Some u => Version.Provider n u
          | None => Version.Orig (snd p) (* unreachable under
                                            chooseSelector_spec's premise *)
          end
      end.

    Lemma chooseSelector_spec :
      forall S_Pi rho Pi (p : Pkg.t) (n : N.t) vs,
        ((exists q, PkgSet.In q S_Pi /\ exists v, MemTop v vs /\
            ProvidesRel.In (q, (n, v)) Pi /\ RhoRel.In (q, (n, p)) rho) \/
         (exists u, VSet.In u vs /\ PkgSet.In (n, u) S_Pi)) ->
        exists m w, chooseSelector S_Pi rho Pi p n vs = Version.Provider m w /\
          PkgSet.In (m, w) S_Pi /\
          ((exists v, MemTop v vs /\ ProvidesRel.In ((m, w), (n, v)) Pi) \/
           (m = n /\ VSet.In w vs)).
    Proof.
      intros S_Pi rho Pi p n vs Hcase; unfold chooseSelector.
      match goal with
      | |- context [PkgSet.min_elt ?c] =>
          destruct (PkgSet.min_elt c) as [q1 |] eqn:H1
      end.
      - apply PkgSet.min_elt_spec1 in H1.
        apply mem_rhoProviders in H1.
        destruct H1 as [Hq1S [v [Hm [HP Hr]]]].
        exists (fst q1), (snd q1).
        split; [reflexivity |].
        split; [rewrite <- surjective_pairing; exact Hq1S |].
        left; exists v; split; [exact Hm |].
        rewrite <- surjective_pairing; exact HP.
      - match goal with
        | |- context [VSet.min_elt ?c] =>
            destruct (VSet.min_elt c) as [u1 |] eqn:H2
        end.
        + apply VSet.min_elt_spec1 in H2.
          rewrite VSet.filter_spec' in H2.
          destruct H2 as [Hu1 Hmem]; apply PkgSet.mem_spec in Hmem.
          exists n, u1.
          split; [reflexivity |].
          split; [exact Hmem |].
          right; split; [reflexivity | exact Hu1].
        + exfalso.
          destruct Hcase as [[q [HqS [v [Hm [HP Hr]]]]] | [u [Hu HuS]]].
          * pose proof (PkgSet.min_elt_spec3 H1) as Hemp.
            apply (Hemp q).
            apply mem_rhoProviders.
            split; [exact HqS |].
            exists v; repeat split; assumption.
          * pose proof (VSet.min_elt_spec3 H2) as Hemp.
            apply (Hemp u).
            rewrite VSet.filter_spec'.
            split; [exact Hu | apply PkgSet.mem_spec; exact HuS].
    Qed.

    Definition coreResolution (D : C.DepRel.t) (Pi : ProvidesRel.t)
        (S_Pi : PkgSet.t) (rho : RhoRel.t) : T.PkgSet.t :=
      T.PkgSet.union (embedSet S_Pi)
        (SOdp.filterMap (fun '(p, (n, vs)) =>
             if andb (PkgSet.mem p S_Pi) (hasProviderb Pi n vs)
             then Some (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs)
             else None)
           D).

    Inductive CoreSpec (D : C.DepRel.t) (Pi : ProvidesRel.t)
        (S_Pi : PkgSet.t) (rho : RhoRel.t) : T.Pkg.t -> Prop :=
    | CoreOrig : forall n v,
        PkgSet.In (n, v) S_Pi ->
        CoreSpec D Pi S_Pi rho (Name.Orig n, Version.Orig v)
    | CoreSelector : forall p n vs,
        C.DepRel.In (p, (n, vs)) D -> PkgSet.In p S_Pi ->
        HasProvider Pi n vs ->
        CoreSpec D Pi S_Pi rho
          (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs).

    Lemma mem_coreResolution : forall D Pi S_Pi rho (y : T.Pkg.t),
        T.PkgSet.In y (coreResolution D Pi S_Pi rho) <->
        CoreSpec D Pi S_Pi rho y.
    Proof.
      intros D Pi S_Pi rho y; unfold coreResolution, embedSet.
      rewrite T.PkgSet.union_spec, SOsp.mem_map, SOdp.mem_filterMap.
      split.
      - intros [([n v] & HS & ->) | ([p [n vs]] & HD & He)].
        + exact (CoreOrig D Pi S_Pi rho n v HS).
        + cbn beta iota in He; apply if_some_iff in He.
          destruct He as [Hc <-].
          rewrite Bool.andb_true_iff, PkgSet.mem_spec, hasProviderb_iff in Hc.
          destruct Hc; constructor; assumption.
      - destruct 1 as [n v HS | p n vs HD HS Hb].
        + left; exists (n, v); auto.
        + right; exists (p, (n, vs)); split; [exact HD | cbn beta iota].
          apply if_some_iff; rewrite Bool.andb_true_iff, PkgSet.mem_spec,
            hasProviderb_iff; auto.
    Qed.

    Lemma mem_coreResolution_embed : forall D Pi S_Pi rho (p : Pkg.t),
        PkgSet.In p S_Pi ->
        T.PkgSet.In (embedPkg p) (coreResolution D Pi S_Pi rho).
    Proof.
      intros D Pi S_Pi rho [n v] Hp.
      apply mem_coreResolution; exact (CoreOrig D Pi S_Pi rho n v Hp).
    Qed.

    Lemma mem_coreResolution_selector :
      forall D Pi S_Pi rho (p : Pkg.t) n vs,
        PkgSet.In p S_Pi -> C.DepRel.In (p, (n, vs)) D -> HasProvider Pi n vs ->
        T.PkgSet.In (Name.Selector p n, chooseSelector S_Pi rho Pi p n vs)
          (coreResolution D Pi S_Pi rho).
    Proof. intros; apply mem_coreResolution; constructor; assumption. Qed.

    Theorem virtual_completeness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (Pi : ProvidesRel.t)
             (r : Pkg.t) (S_Pi : PkgSet.t) (rho : RhoRel.t),
        C.FunctionalInName D ->
        IsResolution R D Pi r S_Pi rho ->
        T.IsResolution (reduceReal R D Pi) (reduceDeps R D Pi)
          (embedPkg r) (coreResolution D Pi S_Pi rho).
    Proof.
      intros R D Pi r S_Pi rho Hfn [Hsub Hroot Hclo Huniq Hps].
      assert (Hsel : forall (p : Pkg.t) (n : N.t) vs,
          PkgSet.In p S_Pi -> C.DepRel.In (p, (n, vs)) D ->
          exists m w,
            chooseSelector S_Pi rho Pi p n vs = Version.Provider m w /\
            PkgSet.In (m, w) S_Pi /\
            ((exists v, MemTop v vs /\ ProvidesRel.In ((m, w), (n, v)) Pi) \/
             (m = n /\ VSet.In w vs))).
      { intros p n vs HpS HD.
        apply chooseSelector_spec.
        destruct (Hclo p HpS n vs HD)
          as [[v [Hv HvS]] | [q [[HqS [v [Hm [HP Hr]]]] _]]].
        - right; exists v; split; assumption.
        - left; exists q; split; [exact HqS |].
          exists v; repeat split; assumption. }
      constructor.
      - intros y Hy; apply mem_coreResolution in Hy; apply mem_reduceReal.
        destruct Hy as [n v HpS | p n vs HD HpS Hb].
        + constructor; apply Hsub; exact HpS.
        + destruct (Hsel p n vs HpS HD)
            as (m & w & -> & HmwS & [(v & Hm & HP) | (-> & Hw)]).
          * eapply RealProvider; eassumption.
          * eapply RealDirect;
              [exact HD | exact Hb | exact Hw | apply Hsub; exact HmwS].
      - apply mem_coreResolution_embed; exact Hroot.
      - intros y Hy; apply mem_coreResolution in Hy.
        destruct Hy as [pn pv HpS | p0 n0 vs0 HD0 HpS0 Hb0];
          intros m' ws Hd; apply mem_reduceDeps in Hd.
        + inversion Hd as [pn1 pv1 n vs HD Hb | pn1 pv1 n vs HD Hb | |];
            subst.
          * destruct (Hclo _ HpS _ _ HD)
              as [[v [Hv HvS]] | [q [[HqS [v [Hm [HP Hr]]]] _]]];
              [| exfalso; apply Hb; exists q, v; split; assumption].
            exists (Version.Orig v); split.
            -- unfold embedVS; apply SOvv.mem_map; exists v; auto.
            -- exact (mem_coreResolution_embed _ _ _ _ _ HvS).
          * eexists; split;
              [| exact (mem_coreResolution_selector _ _ _ _ _ _ _ HpS HD Hb)].
            destruct (Hsel _ _ _ HpS HD)
              as (m & w & -> & HmwS & [(v & Hm & HP) | (-> & Hw)]);
              apply mem_selectorVersions;
              [left; exists m, w, v; auto | right; exists w].
            split; [exact Hw | split; [apply Hsub; exact HmwS | reflexivity]].
        + destruct (Hsel p0 n0 vs0 HpS0 HD0) as (m0 & w & Heqv & HmwS & _).
          rewrite Heqv in Hd; inversion Hd; subst;
            (eexists; split; [apply SOvv.singleton_in; reflexivity |]);
            exact (mem_coreResolution_embed _ _ _ _ _ HmwS).
      - intros n cv1 cv2 H1 H2.
        apply mem_coreResolution in H1; apply mem_coreResolution in H2.
        inversion H1 as [n1 v1 HS1 | p1 n1 vs1 HD1 _ _]; subst;
          inversion H2 as [n2 v2 HS2 | p2 n2 vs2 HD2 _ _]; subst.
        + f_equal; exact (Huniq _ _ _ HS1 HS2).
        + rewrite (Hfn _ _ _ _ HD1 HD2); reflexivity.
    Qed.

    Module Lookup.
      Module ProvFibred := FibredLabelledRel Pkg N VTOT ProvElt ProvidesRel.
      Lemma hasProvider_nodeFibre : forall Pi n vs,
          HasProvider (ProvFibred.nodeFibre Pi n) n vs <-> HasProvider Pi n vs.
      Proof.
        intros Pi n vs; unfold HasProvider; split.
        - intros [q [v [Hin Hm]]]; exists q, v;
            split; [exact (ProvFibred.nodeFibre_subset _ _ _ Hin) | exact Hm].
        - intros [q [v [Hin Hm]]]; exists q, v; split; [| exact Hm].
          apply ProvFibred.mem_nodeFibre; split; [exact Hin | reflexivity].
      Qed.

      Module DepRelFibred :=
        FibredLabelledRel Pkg N C.VSet.AsUOT C.DepElt C.DepRel.
      Module DepKeys := RelKeys N C.DepElt C.DepRel.
      Definition hasDepNameb (Dp : C.DepRel.t) (n : N.t) : bool :=
        DepKeys.hasKey DepRelFibred.node Dp n.

      Lemma hasDepNameb_iff : forall Dp n,
          hasDepNameb Dp n = true <-> exists q vs, C.DepRel.In (q, (n, vs)) Dp.
      Proof.
        intros Dp n; unfold hasDepNameb; rewrite DepKeys.hasKey_iff; split.
        - intros [[q [m vs]] [He Hm]]; cbn [DepRelFibred.node] in Hm;
            subst m; exists q, vs; exact He.
        - intros [q [vs He]]; exists (q, (n, vs));
            split; [exact He | reflexivity].
      Qed.

      Module PkgPreimage := Preimage Pkg PkgSet.
      Definition realPreimage (R : PkgSet.t) (Dp : C.DepRel.t) : PkgSet.t :=
        PkgPreimage.preimage fst (hasDepNameb Dp) R.

      Lemma mem_realPreimage : forall R Dp (n : N.t) (v : V.t),
          PkgSet.In (n, v) (realPreimage R Dp) <->
          PkgSet.In (n, v) R /\ hasDepNameb Dp n = true.
      Proof. intros R Dp n v; apply PkgPreimage.mem_preimage. Qed.

      Module ProvPreimage := Preimage ProvElt ProvidesRel.
      Definition provPreimage (Pi : ProvidesRel.t) (Dp : C.DepRel.t) :
          ProvidesRel.t :=
        ProvPreimage.preimage ProvFibred.node (hasDepNameb Dp) Pi.

      Lemma mem_provPreimage : forall Pi Dp (q : Pkg.t) (n : N.t) (v : VTop),
          ProvidesRel.In (q, (n, v)) (provPreimage Pi Dp) <->
          ProvidesRel.In (q, (n, v)) Pi /\ hasDepNameb Dp n = true.
      Proof. intros Pi Dp q n v; apply ProvPreimage.mem_preimage. Qed.

      Lemma hasProvider_provPreimage : forall Pi Dp n vs,
          hasDepNameb Dp n = true ->
          (HasProvider (provPreimage Pi Dp) n vs <-> HasProvider Pi n vs).
      Proof.
        intros Pi Dp n vs Hn; unfold HasProvider; split.
        - intros [q [v [Hin Hm]]]; apply mem_provPreimage in Hin.
          destruct Hin as [Hin _]; exists q, v; split; assumption.
        - intros [q [v [Hin Hm]]]; exists q, v; split; [| exact Hm].
          apply mem_provPreimage; split; [exact Hin | exact Hn].
      Qed.

      Lemma selectorVersions_preimage : forall R Pi Dp n vs,
          hasDepNameb Dp n = true ->
          selectorVersions (realPreimage R Dp) (provPreimage Pi Dp) n vs =
          selectorVersions R Pi n vs.
      Proof.
        intros R Pi Dp n vs Hn; apply T.VSet.ext; intro y.
        rewrite !mem_selectorVersions; split.
        - intros [[m [u [v [Hin [Hm ->]]]]] | [u [Hu [HR ->]]]].
          + apply mem_provPreimage in Hin; destruct Hin as [Hin _].
            left; exists m, u, v;
              split; [exact Hin | split; [exact Hm | reflexivity]].
          + apply mem_realPreimage in HR; destruct HR as [HR _].
            right; exists u;
              split; [exact Hu | split; [exact HR | reflexivity]].
        - intros [[m [u [v [Hin [Hm ->]]]]] | [u [Hu [HR ->]]]].
          + left; exists m, u, v.
            split; [apply mem_provPreimage; split; [exact Hin | exact Hn] |].
            split; [exact Hm | reflexivity].
          + right; exists u; split; [exact Hu |].
            split;
              [apply mem_realPreimage; split; [exact HR | exact Hn]
              | reflexivity].
      Qed.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Theorem versions_lookupOrig : forall R D Pi (n : N.t),
          T.versions (reduceReal R D Pi) (Name.Orig n) =
          T.versions
            (reduceReal (PkgFibred.tailFibre R n) C.DepRel.empty
               ProvidesRel.empty)
            (Name.Orig n).
      Proof.
        intros R D Pi n; apply T.versions_ext; intro y.
        rewrite !mem_reduceReal.
        split; intro H; inversion H as [n1 v1 HR | |]; subst; constructor.
        - apply PkgFibred.mem_tailFibre; split; [exact HR | reflexivity].
        - exact (PkgFibred.tailFibre_subset _ _ _ HR).
      Qed.

      Theorem dependees_lookupOrig : forall D R Pi (p : Pkg.t),
          let Dp := DepRelFibred.tailFibre D p in
          T.dependees (reduceDeps R D Pi) (embedPkg p) =
          T.dependees (reduceDeps (realPreimage R Dp) Dp (provPreimage Pi Dp))
            (embedPkg p).
      Proof.
        intros D R Pi [pn pv]; cbv zeta; cbn [embedPkg].
        assert (Hn : forall n vs, C.DepRel.In ((pn, pv), (n, vs)) D ->
                  hasDepNameb (DepRelFibred.tailFibre D (pn, pv)) n = true).
        { intros n vs HD; apply hasDepNameb_iff; exists (pn, pv), vs.
          apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity]. }
        apply T.dependees_ext; intros [m ws]; rewrite !mem_reduceDeps.
        split; intro H;
          inversion H as [pn1 pv1 n vs HD Hb | pn1 pv1 n vs HD Hb | |]; subst.
        - apply DepsOrig;
            [apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity]
            |].
          rewrite (hasProvider_provPreimage Pi _ n vs (Hn _ _ HD)); exact Hb.
        - rewrite <- (selectorVersions_preimage R Pi _ n vs (Hn _ _ HD)).
          apply DepsSelector;
            [apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity]
            |].
          apply (hasProvider_provPreimage Pi _ n vs (Hn _ _ HD)); exact Hb.
        - pose proof (DepRelFibred.tailFibre_subset _ _ _ HD) as HD'.
          apply DepsOrig; [exact HD' |].
          rewrite <- (hasProvider_provPreimage Pi _ n vs (Hn _ _ HD')).
          exact Hb.
        - pose proof (DepRelFibred.tailFibre_subset _ _ _ HD) as HD'.
          rewrite (selectorVersions_preimage R Pi _ n vs (Hn _ _ HD')).
          apply DepsSelector; [exact HD' |].
          apply (hasProvider_provPreimage Pi _ n vs (Hn _ _ HD')); exact Hb.
      Qed.

      Theorem versions_lookupSelector : forall R D Pi (p : Pkg.t) (n : N.t),
          T.versions (reduceReal R D Pi) (Name.Selector p n) =
          T.versions
            (reduceReal (PkgFibred.tailFibre R n)
               (DepRelFibred.endsFibre D p n) (ProvFibred.nodeFibre Pi n))
            (Name.Selector p n).
      Proof.
        intros R D Pi p n; apply T.versions_ext; intro y.
        rewrite !mem_reduceReal.
        split; intro H;
          inversion H as [| q n' vs m u v HD HP Hm | q n' vs u HD Hb Hu HuR];
          subst.
        - eapply RealProvider; [| | exact Hm].
          + apply DepRelFibred.mem_endsFibre;
              split; [exact HD | split; reflexivity].
          + apply ProvFibred.mem_nodeFibre; split; [exact HP | reflexivity].
        - eapply RealDirect; [| | exact Hu |].
          + apply DepRelFibred.mem_endsFibre;
              split; [exact HD | split; reflexivity].
          + apply (proj2 (hasProvider_nodeFibre _ _ _)); exact Hb.
          + apply PkgFibred.mem_tailFibre; split; [exact HuR | reflexivity].
        - eapply RealProvider;
            [exact (DepRelFibred.endsFibre_subset _ _ _ _ HD)
            | exact (ProvFibred.nodeFibre_subset _ _ _ HP) | exact Hm].
        - eapply RealDirect;
            [exact (DepRelFibred.endsFibre_subset _ _ _ _ HD)
            | apply (proj1 (hasProvider_nodeFibre _ _ _)); exact Hb
            | exact Hu | exact (PkgFibred.tailFibre_subset _ _ _ HuR)].
      Qed.

      Theorem dependees_lookupSelector : forall D R Pi (p : Pkg.t) n m w,
          T.dependees (reduceDeps R D Pi)
            (Name.Selector p n, Version.Provider m w) =
          T.dependees
            (reduceDeps (PkgFibred.tailFibre R n) (DepRelFibred.tailFibre D p)
                        (ProvFibred.nodeFibre Pi n))
            (Name.Selector p n, Version.Provider m w).
      Proof.
        intros D R Pi p n m w; apply T.dependees_ext; intros [m0 ws];
          rewrite !mem_reduceDeps.
        split; intro H;
          inversion H as [| | q n' vs m' u v HD HP Hm
                         | q n' vs u HD Hb Hu HuR]; subst.
        - eapply DepsProvider; [| | exact Hm].
          + apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
          + apply ProvFibred.mem_nodeFibre; split; [exact HP | reflexivity].
        - eapply DepsDirect; [| | exact Hu |].
          + apply DepRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
          + apply (proj2 (hasProvider_nodeFibre _ _ _)); exact Hb.
          + apply PkgFibred.mem_tailFibre; split; [exact HuR | reflexivity].
        - eapply DepsProvider;
            [exact (DepRelFibred.tailFibre_subset _ _ _ HD)
            | exact (ProvFibred.nodeFibre_subset _ _ _ HP) | exact Hm].
        - eapply DepsDirect;
            [exact (DepRelFibred.tailFibre_subset _ _ _ HD)
            | apply (proj1 (hasProvider_nodeFibre _ _ _)); exact Hb
            | exact Hu | exact (PkgFibred.tailFibre_subset _ _ _ HuR)].
      Qed.

    End Lookup.
  End Reduction.

End Virtual.
