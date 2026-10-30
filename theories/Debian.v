From Stdlib Require Import MSets Lia PeanoNat.
From PackageCalculus Require Import Prelude Core Versions.

Create HintDb cmp_deb.
Create Rewrite HintDb cmp_deb.

Module Type NameGroup (N : UsualOrderedType).
  Parameter groupEq : N.t -> N.t -> bool.
  Axiom groupEq_refl : forall n, groupEq n n = true.
  Axiom groupEq_sym : forall m n, groupEq m n = groupEq n m.
  Axiom groupEq_trans : forall m n o,
      groupEq m n = true -> groupEq n o = true -> groupEq m o = true.
End NameGroup.

Module TrivialGroup (N : UsualOrderedType) <: NameGroup N.
  Definition groupEq (m n : N.t) : bool :=
    match N.compare m n with Eq => true | _ => false end.
  Module NGF := UOTCompareFacts N.

  Lemma groupEq_refl : forall n, groupEq n n = true.
  Proof.
    intro n; unfold groupEq.
    assert (H : N.compare n n = Eq) by (apply NGF.compare_eq_iff; reflexivity).
    rewrite H; reflexivity.
  Qed.
  Lemma groupEq_sym : forall m n, groupEq m n = groupEq n m.
  Proof.
    intros m n; unfold groupEq.
    rewrite (NGF.compare_antisym n m).
    destruct (N.compare n m); reflexivity.
  Qed.
  Lemma groupEq_trans : forall m n o,
      groupEq m n = true -> groupEq n o = true -> groupEq m o = true.
  Proof.
    intros m n o H1 H2; unfold groupEq in *.
    destruct (N.compare m n) eqn:E1; try discriminate.
    destruct (N.compare n o) eqn:E2; try discriminate.
    apply NGF.compare_eq_iff in E1; apply NGF.compare_eq_iff in E2; subst.
    assert (H : N.compare o o = Eq) by (apply NGF.compare_eq_iff; reflexivity).
    rewrite H; reflexivity.
  Qed.
End TrivialGroup.

Module Debian (N V : UsualOrderedType) (NG : NameGroup N).
  Module Ver := Versions N V.
  Module C := Ver.C.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Inductive DTop : Type :=
  | DTVal (v : V.t)
  | DTTop.

  Module VF := UOTCompareFacts V.
  #[local] Hint Rewrite VF.compare_eq_iff : cmp_deb.
  #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_deb.
  #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_deb.

  Module DTComp <: ComparableType.
    Definition t := DTop.
    Definition compare (x y : t) : comparison :=
      match x, y with
      | DTVal v1, DTVal v2 => V.compare v1 v2
      | DTVal _, DTTop => Lt
      | DTTop, DTVal _ => Gt
      | DTTop, DTTop => Eq
      end.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_deb. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_deb. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_deb. Qed.
  End DTComp.

  Module FEqb := UOTEqb Ver.FOT.
  Definition vtMatchb (v : DTop) (phi : Ver.Formula) : bool :=
    match v with
    | DTVal u => Ver.satisfiesb u phi
    | DTTop => FEqb.eqb phi Ver.FTop
    end.

  Module Atom := PairUOT N Ver.FOT.

  Definition aname (a : Atom.t) : N.t := fst a.
  Definition aform (a : Atom.t) : Ver.Formula := snd a.

  Module AtomSet := FSetUOT Atom.
  Module Clause := ListUOT Atom.
  Definition clauseAtoms (A : Clause.t) : AtomSet.t := AtomSet.ofList A.

  Lemma mem_clauseAtoms : forall A a,
      AtomSet.In a (clauseAtoms A) <-> List.In a A.
  Proof. intros A a; apply AtomSet.mem_ofList. Qed.

  Module ClauseElt := PairUOT Pkg Clause.
  Module Deps := FSetUOT ClauseElt.

  Module DTOT := UOTFromCompare DTComp.
  Module Provided := PairUOT N DTOT.
  Module ProvElt := PairUOT Pkg Provided.
  Module Prov := FSetUOT ProvElt.

  Module Conflictees := PairUOT Atom BoolOT.
  Module ConfElt := PairUOT Pkg Conflictees.
  Module Conf := FSetUOT ConfElt.

  Definition Match (Pi : Prov.t) '((m, u) : Pkg.t) '((n, phi) : Atom.t)
      : Prop :=
    (m = n /\ Ver.satisfiesb u phi = true) \/
    (exists v, Prov.In ((m, u), (n, v)) Pi /\ vtMatchb v phi = true).

  Module NEqb := UOTEqb N.
  Module PkgEqb := UOTEqb Pkg.

  Definition matchb (Pi : Prov.t) (q : Pkg.t) (a : Atom.t) : bool :=
    orb
      (andb (NEqb.eqb (fst q) (aname a)) (Ver.satisfiesb (snd q) (aform a)))
      (Prov.exists_ (fun '(p, (m, v)) =>
           andb (PkgEqb.eqb p q)
             (andb (NEqb.eqb m (aname a)) (vtMatchb v (aform a))))
         Pi).

  Lemma matchb_iff : forall Pi q a, matchb Pi q a = true <-> Match Pi q a.
  Proof.
    intros Pi [m u] [n phi]; unfold matchb, Match, aname, aform.
    cbn [fst snd].
    rewrite Bool.orb_true_iff, Bool.andb_true_iff.
    rewrite Prov.exists_spec'.
    unfold Prov.Exists; split.
    - intros [[He Hv] | [e [He Hb]]].
      + left; split; [apply NEqb.eqb_true_iff; exact He | exact Hv].
      + right; destruct e as [q' [n' v]]; cbn beta iota in Hb.
        apply andb_prop in Hb; destruct Hb as [Hq Hb].
        apply andb_prop in Hb; destruct Hb as [Hn Hm].
        apply PkgEqb.eqb_true_iff in Hq as ->.
        apply NEqb.eqb_true_iff in Hn as ->.
        exists v; split; assumption.
    - intros [[He Hv] | [v [Hin Hm]]].
      + left; split; [apply NEqb.eqb_true_iff; exact He | exact Hv].
      + right; exists ((m, u), (n, v)); split; [exact Hin | cbn [fst snd]].
        rewrite PkgEqb.eqb_refl, NEqb.eqb_refl; cbn [andb]; exact Hm.
  Qed.

  Record Inst : Type := MkInst
    { inst_repo : PkgSet.t
    ; inst_deps : Deps.t
    ; inst_rec : Deps.t
    ; inst_prov : Prov.t
    ; inst_conf : Conf.t
    ; inst_root : Pkg.t }.

  Record IsResolution (I : Inst) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S (inst_repo I)
    ; res_root_mem : PkgSet.In (inst_root I) S
    ; res_dep_closure :
        forall p, PkgSet.In p S ->
        forall A, Deps.In (p, A) (inst_deps I) ->
        exists a, List.In a A /\
          exists q, PkgSet.In q S /\ Match (inst_prov I) q a
    ; res_conflict_avoidance :
        forall n v, PkgSet.In (n, v) S ->
        forall a e, Conf.In ((n, v), (a, e)) (inst_conf I) ->
        ~ exists m u, PkgSet.In (m, u) S /\ (m, u) <> (n, v) /\
            (e = true -> NG.groupEq m n = false) /\
            Match (inst_prov I) (m, u) a
    ; res_version_unique : C.VersionUnique S }.

  Module Reduction.
    Module AtomF := UOTCompareFacts Atom.

    Module NF := UOTCompareFacts N.
    Module ClauseF := UOTCompareFacts Clause.
    Module ConfEltF := UOTCompareFacts ConfElt.
    #[local] Hint Rewrite AtomF.compare_eq_iff NF.compare_eq_iff
      ClauseF.compare_eq_iff ConfEltF.compare_eq_iff : cmp_deb.
    #[local] Hint Extern 1 => cmp_by AtomF.compare_antisym : cmp_deb.
    #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_deb.
    #[local] Hint Extern 1 => cmp_by ClauseF.compare_antisym : cmp_deb.
    #[local] Hint Extern 1 => cmp_by ConfEltF.compare_antisym : cmp_deb.
    #[local] Hint Extern 1 => cmp_by AtomF.compare_lt_trans : cmp_deb.
    #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_deb.
    #[local] Hint Extern 1 => cmp_by ClauseF.compare_lt_trans : cmp_deb.
    #[local] Hint Extern 1 => cmp_by ConfEltF.compare_lt_trans : cmp_deb.

    Module Name.
      Inductive name : Type :=
      | Orig (n : N.t)
      | Disjunct (A : Clause.t)
      | Soft (A : Clause.t)
      | Selector (a : Atom.t).
      Definition t := name.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig n1, Orig n2 => N.compare n1 n2
        | Orig _, _ => Lt
        | Disjunct _, Orig _ => Gt
        | Disjunct A1, Disjunct A2 => Clause.compare A1 A2
        | Disjunct _, _ => Lt
        | Soft _, Orig _ => Gt
        | Soft _, Disjunct _ => Gt
        | Soft A1, Soft A2 => Clause.compare A1 A2
        | Soft _, _ => Lt
        | Selector a1, Selector a2 => Atom.compare a1 a2
        | Selector _, _ => Gt
        end.
      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_deb. Qed.
      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_deb. Qed.
      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_deb. Qed.
    End Name.

    Module NV2 := PairUOT N V.
    Module NV2F := UOTCompareFacts NV2.
    #[local] Hint Rewrite NV2F.compare_eq_iff : cmp_deb.
    #[local] Hint Extern 1 => cmp_by NV2F.compare_antisym : cmp_deb.
    #[local] Hint Extern 1 => cmp_by NV2F.compare_lt_trans : cmp_deb.

    Module Version.
      Inductive version : Type :=
      | Orig (v : V.t)
      | Atom (a : Atom.t)
      | Ref (m : N.t) (w : V.t)
      | RefReal (u : V.t)
      | Zero
      | Bot.
      Definition t := version.

      Definition compare (x y : t) : comparison :=
        match x, y with
        | Orig v1, Orig v2 => V.compare v1 v2
        | Orig _, _ => Lt
        | Atom _, Orig _ => Gt
        | Atom a1, Atom a2 => Atom.compare a1 a2
        | Atom _, _ => Lt
        | Ref m1 w1, Ref m2 w2 => NV2.compare (m1, w1) (m2, w2)
        | Ref _ _, Orig _ => Gt
        | Ref _ _, Atom _ => Gt
        | Ref _ _, _ => Lt
        | RefReal w1, RefReal w2 => V.compare w1 w2
        | RefReal _, Zero => Lt
        | RefReal _, Bot => Lt
        | RefReal _, _ => Gt
        | Zero, Bot => Lt
        | Zero, Zero => Eq
        | Zero, _ => Gt
        | Bot, Bot => Eq
        | Bot, _ => Gt
        end.
      Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
      Proof. cmp_eq_iff cmp_deb. Qed.
      Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
      Proof. cmp_antisym cmp_deb. Qed.
      Lemma compare_lt_trans : forall x y z,
          compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
      Proof. cmp_lt_trans cmp_deb. Qed.
    End Version.

    Module NameOT := UOTFromCompare Name.
    Module VersionOT := UOTFromCompare Version.
    Module T := Core NameOT VersionOT.

    Module SOvw := SetOps V VersionOT VSet T.VSet.
    Definition embedVS (vs : VSet.t) : T.VSet.t :=
      SOvw.map Version.Orig vs.

    Definition evalAt (R : PkgSet.t) (a : Atom.t) : VSet.t :=
      Ver.eval (aform a) (C.versions R (aname a)).

    Definition provb (Pi : Prov.t) (a : Atom.t) : bool :=
      Prov.exists_ (fun '(_, (m, v)) =>
          andb (NEqb.eqb m (aname a)) (vtMatchb v (aform a)))
        Pi.

    Module SOew := SetOps ProvElt VersionOT Prov T.VSet.
    Definition us (R : PkgSet.t) (Pi : Prov.t) (a : Atom.t) : T.VSet.t :=
      T.VSet.union
        (SOvw.map (fun u => Version.RefReal u) (evalAt R a))
        (SOew.filterMap (fun e =>
             if andb (NEqb.eqb (fst (snd e)) (aname a))
                  (vtMatchb (snd (snd e)) (aform a))
             then Some (Version.Ref (fst (fst e)) (snd (fst e)))
             else None)
           Pi).

    Definition dependee (R : PkgSet.t) (Pi : Prov.t) (a : Atom.t) :
        Name.t * T.VSet.t :=
      if provb Pi a
      then (Name.Selector a, us R Pi a)
      else (Name.Orig (aname a), embedVS (evalAt R a)).

    Module NSet := C.NSet.
    Module SOan := SetOps Atom N AtomSet NSet.
    Definition clauseNames (A : Clause.t) : NSet.t :=
      SOan.map (fun '(n, _) => n) (clauseAtoms A).

    Module SOgn := SetOps ConfElt N Conf NSet.
    Module SOpin := SetOps ProvElt N Prov NSet.

    Module SOrn := SetOps Pkg N PkgSet NSet.
    Definition repoNames (R : PkgSet.t) : NSet.t := SOrn.map fst R.

    Module SOaw := SetOps Atom VersionOT AtomSet T.VSet.
    Definition versionsDisj (A : Clause.t) : T.VSet.t :=
      SOaw.map (fun a => Version.Atom a) (clauseAtoms A).

    Definition versionsSoft (A : Clause.t) : T.VSet.t :=
      T.VSet.add Version.Zero (versionsDisj A).

    Definition allClauses (D Dopt : Deps.t) : Deps.t := Deps.union D Dopt.

    Definition exemptb (e : bool) (m n : N.t) : bool :=
      andb e (NG.groupEq m n).

    Definition complementVS (R : PkgSet.t) (Pi : Prov.t) (a : Atom.t) (m : N.t)
      : T.VSet.t :=
      T.VSet.add Version.Bot
        (embedVS (VSet.filter (fun u => negb (matchb Pi (m, u) a))
                    (C.versions R m))).

    Definition confNames (R : PkgSet.t) (Pi : Prov.t) (a : Atom.t) : NSet.t :=
      SOrn.filterMap (fun q => if matchb Pi q a then Some (fst q) else None) R.

    Module ProvFibred := FibredLabelledRel Pkg N DTOT ProvElt Prov.
    Module SOnd := SetOps N T.Dependees NSet T.DependeesSet.
    Definition confEdges (R : PkgSet.t) (Pi : Prov.t) (p : Pkg.t) (a : Atom.t)
        (e : bool) : T.DependeesSet.t :=
      let Pi := ProvFibred.nodeFibre Pi (aname a) in
      SOnd.filterMap
        (fun m =>
           if orb (NEqb.eqb m (fst p)) (exemptb e m (fst p)) then None
           else Some (Name.Orig m, complementVS R Pi a m))
        (confNames R Pi a).

    Definition versions (I : Inst) (m : Name.t) : T.VSet.t :=
      match m with
      | Name.Orig n =>
          let vs := C.versions (inst_repo I) n in
          if VSet.is_empty vs then T.VSet.empty
          else T.VSet.add Version.Bot (embedVS vs)
      | Name.Disjunct A => versionsDisj A
      | Name.Soft A => versionsSoft A
      | Name.Selector a => us (inst_repo I) (inst_prov I) a
      end.

    Module SOde := SetOps ClauseElt T.Dependees Deps T.DependeesSet.
    Module SOge := SetOps ConfElt T.Dependees Conf T.DependeesSet.
    Definition dependees (I : Inst) (p : T.Pkg.t) : T.DependeesSet.t :=
      match p with
      | (Name.Orig n, Version.Orig v) =>
          T.DependeesSet.union
            (SOde.filterMap (fun c =>
                 if Pkg.eq_dec (fst c) (n, v)
                 then if AtomSet.cardinal (clauseAtoms (snd c)) =? 1
                      then match AtomSet.min_elt (clauseAtoms (snd c)) with
                           | Some a =>
                               Some (dependee (inst_repo I) (inst_prov I) a)
                           | None => None
                           end
                      else Some (Name.Disjunct (snd c), versionsDisj (snd c))
                 else None)
               (inst_deps I))
            (T.DependeesSet.union
               (SOde.filterMap (fun c =>
                    if Pkg.eq_dec (fst c) (n, v)
                    then Some (Name.Soft (snd c), versionsSoft (snd c))
                    else None)
                  (inst_rec I))
               (SOge.unionMap (fun e =>
                    if Pkg.eq_dec (fst e) (n, v)
                    then confEdges (inst_repo I) (inst_prov I) (n, v)
                           (fst (snd e)) (snd (snd e))
                    else T.DependeesSet.empty)
                  (inst_conf I)))
      | (Name.Disjunct _, Version.Atom a) =>
          T.DependeesSet.singleton (dependee (inst_repo I) (inst_prov I) a)
      | (Name.Soft _, Version.Atom a) =>
          T.DependeesSet.singleton (dependee (inst_repo I) (inst_prov I) a)
      | (Name.Selector _, Version.Ref m w) =>
          T.DependeesSet.singleton
            (Name.Orig m, T.VSet.singleton (Version.Orig w))
      | (Name.Selector a, Version.RefReal u) =>
          T.DependeesSet.singleton
            (Name.Orig (aname a), T.VSet.singleton (Version.Orig u))
      | _ => T.DependeesSet.empty
      end.

    Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
      (Name.Orig (fst p), Version.Orig (snd p)).

    Module SOrp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
    Definition realOrig (R : PkgSet.t) : T.PkgSet.t :=
      SOrp.map embedPkg R.

    Module SOap := SetOps Atom T.Pkg AtomSet T.PkgSet.
    Definition disjunctAtoms (A : Clause.t) : T.PkgSet.t :=
      SOap.map (fun a => (Name.Disjunct A, Version.Atom a)) (clauseAtoms A).

    Module SOcp := SetOps ClauseElt T.Pkg Deps T.PkgSet.
    Definition realDisjunct (D : Deps.t) : T.PkgSet.t :=
      SOcp.unionMap (fun '(_, A) =>
          if 2 <=? AtomSet.cardinal (clauseAtoms A)
          then disjunctAtoms A
          else T.PkgSet.empty)
        D.

    Definition softAtoms (A : Clause.t) : T.PkgSet.t :=
      SOap.map (fun a => (Name.Soft A, Version.Atom a)) (clauseAtoms A).

    Definition realSoft (Dopt : Deps.t) : T.PkgSet.t :=
      SOcp.unionMap (fun '(_, A) =>
          T.PkgSet.add (Name.Soft A, Version.Zero) (softAtoms A))
        Dopt.

    Module SOwp := SetOps VersionOT T.Pkg T.VSet T.PkgSet.
    Definition selectorVers (a : Atom.t) (vs : T.VSet.t) : T.PkgSet.t :=
      SOwp.map (fun v => (Name.Selector a, v)) vs.

    Definition selectorAtoms (R : PkgSet.t) (Pi : Prov.t) (A : Clause.t) :
        T.PkgSet.t :=
      SOap.unionMap (fun a =>
          if provb Pi a
          then selectorVers a (us R Pi a)
          else T.PkgSet.empty)
        (clauseAtoms A).

    Definition realSelector (R : PkgSet.t) (D : Deps.t) (Pi : Prov.t) :
        T.PkgSet.t :=
      SOcp.unionMap (fun '(_, A) => selectorAtoms R Pi A) D.

    Module SOnt := SetOps N T.Pkg NSet T.PkgSet.
    Definition absentPkgs (ns : NSet.t) : T.PkgSet.t :=
      SOnt.map (fun n => (Name.Orig n, Version.Bot)) ns.

    Definition reduceReal (I : Inst) : T.PkgSet.t :=
      T.PkgSet.union (realOrig (inst_repo I))
        (T.PkgSet.union (realDisjunct (inst_deps I))
           (T.PkgSet.union (realSoft (inst_rec I))
              (T.PkgSet.union
                 (realSelector (inst_repo I)
                    (allClauses (inst_deps I) (inst_rec I)) (inst_prov I))
                 (absentPkgs (repoNames (inst_repo I)))))).

    Module SOee := SetOps T.Dependees T.DepElt T.DependeesSet T.DepRel.
    Definition depEdges (p : T.Pkg.t) (es : T.DependeesSet.t) : T.DepRel.t :=
      SOee.map (fun e => (p, e)) es.

    Module SOse := SetOps T.Pkg T.DepElt T.PkgSet T.DepRel.
    Definition reduceDeps (I : Inst) : T.DepRel.t :=
      SOse.unionMap (fun p => depEdges p (dependees I p)) (reduceReal I).

    Lemma provb_iff : forall Pi (n : N.t) (phi : Ver.Formula),
        provb Pi (n, phi) = true <->
        exists q v, Prov.In (q, (n, v)) Pi /\ vtMatchb v phi = true.
    Proof.
      intros Pi n phi; unfold provb.
      rewrite Prov.exists_spec'.
      unfold Prov.Exists; split.
      - intros [e [He Hb]]; destruct e as [q [n' v]];
          cbn [aname aform fst snd] in Hb.
        apply andb_prop in Hb; destruct Hb as [Hn Hm].
        apply NEqb.eqb_true_iff in Hn as ->.
        exists q, v; split; assumption.
      - intros [q [v [Hin Hm]]].
        exists (q, (n, v)); split; [exact Hin | cbn [aname aform fst snd]].
        rewrite NEqb.eqb_refl; cbn [andb]; exact Hm.
    Qed.

    Lemma mem_us : forall R Pi (n : N.t) (phi : Ver.Formula) u',
        T.VSet.In u' (us R Pi (n, phi)) <->
        (exists u, VSet.In u (evalAt R (n, phi)) /\ u' = Version.RefReal u) \/
        (exists m w v, Prov.In ((m, w), (n, v)) Pi /\
           vtMatchb v phi = true /\ u' = Version.Ref m w).
    Proof.
      intros R Pi n phi u'; unfold us; cbn [aname aform fst snd].
      rewrite T.VSet.union_spec, SOvw.mem_map, SOew.mem_filterMap.
      split.
      - intros [[u [Hu Hy]] | [[[m w] [n' v]] [He Hy]]].
        + left; exists u; split; assumption.
        + cbn [fst snd] in Hy.
          destruct (andb (NEqb.eqb n' n) (vtMatchb v phi)) eqn:Hc;
            [| discriminate].
          apply andb_prop in Hc; destruct Hc as [Hn Hm].
          apply NEqb.eqb_true_iff in Hn as ->.
          injection Hy as <-.
          right; exists m, w, v; repeat split; assumption.
      - intros [[u [Hu ->]] | [m [w [v [Hin [Hm ->]]]]]].
        + left; exists u; split; [exact Hu | reflexivity].
        + right; exists ((m, w), (n, v)); split;
            [exact Hin | cbn [fst snd]].
          rewrite NEqb.eqb_refl, Hm; reflexivity.
    Qed.

    Lemma allClauses_inL : forall D Dopt (p : Pkg.t) A,
        Deps.In (p, A) D -> Deps.In (p, A) (allClauses D Dopt).
    Proof. intros D Dopt p A H; apply Deps.union_spec; left; exact H. Qed.

    Lemma allClauses_inR : forall D Dopt (p : Pkg.t) A,
        Deps.In (p, A) Dopt -> Deps.In (p, A) (allClauses D Dopt).
    Proof. intros D Dopt p A H; apply Deps.union_spec; right; exact H. Qed.

    Lemma mem_clauseNames : forall A (n : N.t),
        NSet.In n (clauseNames A) <->
          exists phi, AtomSet.In (n, phi) (clauseAtoms A).
    Proof.
      intros A n; unfold clauseNames; rewrite SOan.mem_map.
      split.
      - intros [[m phi] [Ha Hn]].
        cbn beta iota in Hn; subst m; exists phi; exact Ha.
      - intros [phi Ha].
        exists (n, phi); split; [exact Ha | reflexivity].
    Qed.

    Lemma mem_repoNames : forall R (n : N.t),
        NSet.In n (repoNames R) <-> exists v, PkgSet.In (n, v) R.
    Proof.
      intros R n; unfold repoNames; rewrite SOrn.mem_map.
      split; [intros [[m v] [HR Hm]]; cbn [fst] in Hm; subst m; eauto |].
      intros [v HR]; exists (n, v); auto.
    Qed.

    Lemma mem_absentPkgs : forall ns (p : T.Pkg.t),
        T.PkgSet.In p (absentPkgs ns) <->
        exists n, NSet.In n ns /\ p = (Name.Orig n, Version.Bot).
    Proof. intros ns p; unfold absentPkgs; apply SOnt.mem_map. Qed.

    Lemma mem_complementVS : forall R Pi a m (v : Version.t),
        T.VSet.In v (complementVS R Pi a m) <->
        v = Version.Bot \/
        exists u, PkgSet.In (m, u) R /\ matchb Pi (m, u) a = false /\
                  v = Version.Orig u.
    Proof.
      intros R Pi a m v; unfold complementVS.
      rewrite SOvw.add_in; unfold embedVS; rewrite SOvw.mem_map.
      split.
      - intros [-> | [u [Hu ->]]]; [left; reflexivity | right].
        apply VSet.filter_spec' in Hu; destruct Hu as [Hu Hm].
        apply Bool.negb_true_iff in Hm.
        exists u; split; [apply C.mem_versions; exact Hu | auto].
      - intros [-> | [u [HR [Hm ->]]]]; [left; reflexivity | right].
        exists u; split; [| reflexivity].
        apply VSet.filter_spec'; split;
          [apply C.mem_versions; exact HR
          | apply Bool.negb_true_iff; exact Hm].
    Qed.

    Lemma mem_confNames : forall R Pi a (m : N.t),
        NSet.In m (confNames R Pi a) <->
        exists u, PkgSet.In (m, u) R /\ matchb Pi (m, u) a = true.
    Proof.
      intros R Pi a m; unfold confNames; rewrite SOrn.mem_filterMap_if.
      split; [intros [[m' u] [HR [Hm ->]]]; exists u; auto |].
      intros [u [HR Hm]]; exists (m, u); auto.
    Qed.

    Lemma matchb_nodeFibre : forall Pi q (n : N.t) (phi : Ver.Formula),
        matchb (ProvFibred.nodeFibre Pi n) q (n, phi) = matchb Pi q (n, phi).
    Proof.
      intros Pi q n phi; unfold matchb; f_equal.
      apply Prov.exists_restrict; [apply ProvFibred.nodeFibre_subset |].
      intros [q' [m v]] Hin Hb; cbn beta iota in Hb.
      apply andb_prop in Hb; destruct Hb as [_ Hb].
      apply andb_prop in Hb; destruct Hb as [Hn _].
      apply ProvFibred.mem_nodeFibre; split;
        [exact Hin | apply NEqb.eqb_true_iff; exact Hn].
    Qed.

    Lemma mem_confEdges :
      forall R Pi (n : N.t) (v : V.t) a e (h : T.Dependees.t),
        T.DependeesSet.In h (confEdges R Pi (n, v) a e) <->
        exists m, NSet.In m (confNames R Pi a) /\ m <> n /\
                   exemptb e m n = false /\
                   h = (Name.Orig m, complementVS R Pi a m).
    Proof.
      intros R Pi n v a e h; unfold confEdges; cbv zeta; cbn [fst].
      assert (HN : confNames R (ProvFibred.nodeFibre Pi (aname a)) a =
                   confNames R Pi a).
      { destruct a as [an af]; cbn [aname fst].
        apply NSet.ext; intro m; rewrite !mem_confNames.
        split; intros [u [HR Hm]]; exists u; rewrite matchb_nodeFibre in *;
          auto. }
      assert (HC : forall m,
                 complementVS R (ProvFibred.nodeFibre Pi (aname a)) a m =
                 complementVS R Pi a m).
      { destruct a as [an af]; cbn [aname fst].
        intro m; apply T.VSet.ext; intro w; rewrite !mem_complementVS.
        apply or_iff_compat_l.
        split; intros [u [HR [Hm Hw]]]; exists u; rewrite matchb_nodeFibre in *;
          auto. }
      rewrite HN, SOnd.mem_filterMap.
      split.
      - intros [m [Hqn Hf]].
        destruct (orb (NEqb.eqb m n) (exemptb e m n)) eqn:Ho;
          [discriminate |].
        injection Hf as <-.
        apply Bool.orb_false_iff in Ho; destruct Ho as [Hn Hx].
        exists m; split; [exact Hqn |].
        split; [apply NEqb.eqb_false_iff; exact Hn |].
        split; [exact Hx | rewrite HC; reflexivity].
      - intros [m [Hqn [Hn [Hx ->]]]]; exists m; split; [exact Hqn |].
        replace (NEqb.eqb m n) with false
          by (symmetry; apply NEqb.eqb_false_iff; exact Hn).
        rewrite Hx, HC; reflexivity.
    Qed.

    Lemma mem_realOrig : forall R p,
        T.PkgSet.In p (realOrig R) <->
        exists n v, PkgSet.In (n, v) R /\ p = (Name.Orig n, Version.Orig v).
    Proof.
      intros R p; unfold realOrig; rewrite SOrp.mem_map.
      split.
      - intros [[n v] [Hp Hy]]; unfold embedPkg in Hy; cbn [fst snd] in Hy.
        exists n, v; split; assumption.
      - intros [n [v [Hp ->]]]; exists (n, v); split; [exact Hp | reflexivity].
    Qed.

    Lemma mem_disjunctAtoms : forall A p,
        T.PkgSet.In p (disjunctAtoms A) <->
        exists a, AtomSet.In a (clauseAtoms A) /\
          p = (Name.Disjunct A, Version.Atom a).
    Proof.
      intros A p; unfold disjunctAtoms; rewrite SOap.mem_map; tauto.
    Qed.

    Lemma mem_realDisjunct : forall D q,
        T.PkgSet.In q (realDisjunct D) <->
        exists p Al, Deps.In (p, Al) D /\
          (2 <=? AtomSet.cardinal (clauseAtoms Al)) = true /\
          exists a, AtomSet.In a (clauseAtoms Al) /\
            q = (Name.Disjunct Al, Version.Atom a).
    Proof.
      intros D q; unfold realDisjunct; rewrite SOcp.mem_unionMap.
      split.
      - intros [[p Al] [Hc Hy]]; cbn beta iota in Hy.
        apply SOcp.in_if_empty in Hy as [Hcard Hy].
        apply mem_disjunctAtoms in Hy; eauto.
      - intros [p [Al [Hc [Hcard Ha]]]].
        exists (p, Al); split; [exact Hc | cbn beta iota].
        apply SOcp.in_if_empty; rewrite mem_disjunctAtoms; auto.
    Qed.

    Lemma mem_versionsSoft : forall A v,
        T.VSet.In v (versionsSoft A) <->
        v = Version.Zero \/
        exists a, AtomSet.In a (clauseAtoms A) /\ v = Version.Atom a.
    Proof.
      intros A v; unfold versionsSoft, versionsDisj.
      rewrite SOvw.add_in, SOaw.mem_map; reflexivity.
    Qed.

    Lemma mem_softAtoms : forall A p,
        T.PkgSet.In p (softAtoms A) <->
        exists a, AtomSet.In a (clauseAtoms A) /\
          p = (Name.Soft A, Version.Atom a).
    Proof.
      intros A p; unfold softAtoms; rewrite SOap.mem_map; tauto.
    Qed.

    Lemma mem_realSoft : forall Dopt q,
        T.PkgSet.In q (realSoft Dopt) <->
        exists p Al, Deps.In (p, Al) Dopt /\
          (q = (Name.Soft Al, Version.Zero) \/
           exists a, AtomSet.In a (clauseAtoms Al) /\
             q = (Name.Soft Al, Version.Atom a)).
    Proof.
      intros Dopt q; unfold realSoft; rewrite SOcp.mem_unionMap.
      split.
      - intros [[p Al] [Hc Hy]]; cbn beta iota in Hy.
        rewrite SOcp.add_in, mem_softAtoms in Hy; eauto.
      - intros [p [Al [Hc Hy]]].
        exists (p, Al); split; [exact Hc | cbn beta iota].
        rewrite SOcp.add_in, mem_softAtoms; exact Hy.
    Qed.

    Lemma mem_selectorVers : forall a vs p,
        T.PkgSet.In p (selectorVers a vs) <->
        exists v, T.VSet.In v vs /\ p = (Name.Selector a, v).
    Proof.
      intros a vs p; unfold selectorVers; rewrite SOwp.mem_map; tauto.
    Qed.

    Lemma mem_selectorAtoms : forall R Pi A p,
        T.PkgSet.In p (selectorAtoms R Pi A) <->
        exists a, AtomSet.In a (clauseAtoms A) /\ provb Pi a = true /\
          exists v, T.VSet.In v (us R Pi a) /\ p = (Name.Selector a, v).
    Proof.
      intros R Pi A p; unfold selectorAtoms; rewrite SOap.mem_unionMap_if.
      split; intros [a [Ha [Hp Hy]]]; exists a; rewrite mem_selectorVers in *;
        auto.
    Qed.

    Lemma mem_realSelector : forall R D Pi q,
        T.PkgSet.In q (realSelector R D Pi) <->
        exists p Al, Deps.In (p, Al) D /\
          exists a, AtomSet.In a (clauseAtoms Al) /\ provb Pi a = true /\
            exists v, T.VSet.In v (us R Pi a) /\ q = (Name.Selector a, v).
    Proof.
      intros R D Pi q; unfold realSelector; rewrite SOcp.mem_unionMap.
      split; [intros [[p Al] [Hc Hy]] | intros [p [Al [Hc Hy]]];
              exists (p, Al)]; cbn beta iota in *;
        rewrite mem_selectorAtoms in *; eauto.
    Qed.

    Lemma versions_orig_spec : forall I n u,
        T.VSet.In u (versions I (Name.Orig n)) <->
        (exists v, PkgSet.In (n, v) (inst_repo I) /\ u = Version.Orig v) \/
        ((exists v, PkgSet.In (n, v) (inst_repo I)) /\ u = Version.Bot).
    Proof.
      intros I n u; cbn [versions].
      destruct (VSet.is_empty (C.versions (inst_repo I) n)) eqn:He.
      - apply VSet.is_empty_spec in He.
        split; [intro H; exfalso; exact (SOvw.empty_in _ H) |].
        intros [[v [Hv _]] | [[v Hv] _]];
          exfalso; apply (He v), C.mem_versions; exact Hv.
      - assert (Hne : exists v, PkgSet.In (n, v) (inst_repo I)).
        { destruct (VSet.choose (C.versions (inst_repo I) n)) as [v |] eqn:Hc.
          - exists v; apply C.mem_versions, VSet.choose_spec1; exact Hc.
          - apply VSet.choose_spec2, VSet.is_empty_spec in Hc; congruence. }
        rewrite SOvw.add_in; unfold embedVS; rewrite SOvw.mem_map.
        split.
        + intros [-> | [v [Hv ->]]]; [right; auto | left].
          exists v; split; [apply C.mem_versions; exact Hv | reflexivity].
        + intros [[v [Hv ->]] | [_ ->]]; [right | left; reflexivity].
          exists v; split; [apply C.mem_versions; exact Hv | reflexivity].
    Qed.

    Lemma mem_reduceReal : forall I (n : Name.t) (v : Version.t),
        T.PkgSet.In (n, v) (reduceReal I) -> T.VSet.In v (versions I n).
    Proof.
      intros I n v H; unfold reduceReal in H.
      rewrite !T.PkgSet.union_spec, mem_realOrig, mem_realDisjunct,
        mem_realSoft, mem_realSelector, mem_absentPkgs in H.
      setoid_rewrite mem_repoNames in H.
      destruct n; [apply versions_orig_spec | cbn [versions] ..];
        rewrite ?mem_versionsSoft;
        try (unfold versionsDisj; rewrite SOaw.mem_map);
        repeat match goal with
               | H : _ \/ _ |- _ => destruct H
               | H : exists _, _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
               end;
        mem_destruct; try discriminate; eauto 20.
    Qed.

    Lemma mem_reduceDeps : forall I (p : T.Pkg.t) (h : T.Dependees.t),
        T.DepRel.In (p, h) (reduceDeps I) <->
        T.PkgSet.In p (reduceReal I) /\
        T.DependeesSet.In h (dependees I p).
    Proof.
      intros I p [n vs]; unfold reduceDeps;
        rewrite SOse.mem_unionMap.
      split.
      - intros [p0 [Hs0 Hy]]; cbn beta iota in Hy.
        unfold depEdges in Hy; apply SOee.mem_map in Hy.
        destruct Hy as [e [He Hy]].
        injection Hy as -> He2.
        rewrite <- He2 in He.
        split; assumption.
      - intros [Hs He].
        exists p; split; [exact Hs | cbn beta iota].
        unfold depEdges; apply SOee.mem_map.
        exists (n, vs); split; [exact He | reflexivity].
    Qed.

    Definition tryInvPkg (p : T.Pkg.t) : option Pkg.t :=
      match p with
      | (Name.Orig n, Version.Orig v) => Some (n, v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof. intros [n v]; reflexivity. Qed.

    Lemma tryInvPkg_some : forall (q : T.Pkg.t) (p : Pkg.t),
        tryInvPkg q = Some p -> embedPkg p = q.
    Proof.
      intros [n' v'] p H; destruct n', v'; cbn [tryInvPkg] in H;
        try discriminate.
      injection H as <-; reflexivity.
    Qed.

    Module SOtp := SetOps T.Pkg Pkg T.PkgSet PkgSet.
    Definition debianResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtp.filterMap tryInvPkg S.

    Lemma mem_debianResolution : forall (S : T.PkgSet.t) (p : Pkg.t),
        PkgSet.In p (debianResolution S) <-> T.PkgSet.In (embedPkg p) S.
    Proof.
      unfold debianResolution.
      exact (SOtp.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma dependees_orig_spec : forall I (n : N.t) (v : V.t) y,
        T.DependeesSet.In y
          (dependees I (Name.Orig n, Version.Orig v)) <->
        (exists A, Deps.In ((n, v), A) (inst_deps I) /\
           (((AtomSet.cardinal (clauseAtoms A) =? 1) = true /\
             exists a, AtomSet.min_elt (clauseAtoms A) = Some a /\
               y = dependee (inst_repo I) (inst_prov I) a) \/
            ((AtomSet.cardinal (clauseAtoms A) =? 1) = false /\
             y = (Name.Disjunct A, versionsDisj A)))) \/
        (exists A, Deps.In ((n, v), A) (inst_rec I) /\
           y = (Name.Soft A, versionsSoft A)) \/
        (exists a e m, Conf.In ((n, v), (a, e)) (inst_conf I) /\
           NSet.In m (confNames (inst_repo I) (inst_prov I) a) /\ m <> n /\
           (e = true -> NG.groupEq m n = false) /\
           y = (Name.Orig m, complementVS (inst_repo I) (inst_prov I) a m)).
    Proof.
      intros I n v y; cbn [dependees].
      rewrite !T.DependeesSet.union_spec, !SOde.mem_filterMap,
        SOge.mem_unionMap.
      split.
      - intros [[[cp cA] [Hc Hy]] |
                [[[rp rA] [Hr Hy]] |
                 [[ep [ea ex]] [He Hy]]]];
          cbn [fst snd] in Hy.
        + destruct (Pkg.eq_dec cp (n, v)) as [-> | NE]; [| discriminate].
          destruct (AtomSet.cardinal (clauseAtoms cA) =? 1) eqn:Hcard.
          * destruct (AtomSet.min_elt (clauseAtoms cA)) as [a0 |] eqn:Hmin;
              [| discriminate].
            injection Hy as <-.
            left; exists cA; split; [exact Hc |].
            left; split; [exact Hcard |].
            exists a0; split; [exact Hmin | reflexivity].
          * injection Hy as <-.
            left; exists cA; split; [exact Hc |].
            right; split; [exact Hcard | reflexivity].
        + destruct (Pkg.eq_dec rp (n, v)) as [-> | NE]; [| discriminate].
          injection Hy as <-.
          right; left; exists rA; split; [exact Hr | reflexivity].
        + destruct (Pkg.eq_dec ep (n, v)) as [-> | NE];
            [| exfalso; exact (SOde.empty_in _ Hy)].
          apply mem_confEdges in Hy; destruct Hy as [m [Hqn [Hne [Hx ->]]]].
          right; right; exists ea, ex, m.
          split; [exact He | split; [exact Hqn | split; [exact Hne |]]].
          split; [| reflexivity].
          intros ->; exact Hx.
      - intros [[A [HA Hcase]] |
                [[A [HA ->]] |
                 [a0 [x0 [m [Ha0 [Hqn [Hne [Hx ->]]]]]]]]].
        + left; exists ((n, v), A); split; [exact HA |].
          cbn [fst snd]; rewrite dec_refl.
          destruct Hcase as [[Hcard [a0 [Hmin ->]]] | [Hcard ->]];
            rewrite Hcard; [rewrite Hmin |]; reflexivity.
        + right; left; exists ((n, v), A); split; [exact HA |].
          cbn [fst snd]; rewrite dec_refl; reflexivity.
        + right; right; exists ((n, v), (a0, x0)); split; [exact Ha0 |].
          cbn [fst snd]; rewrite dec_refl.
          apply mem_confEdges; exists m.
          split; [exact Hqn | split; [exact Hne | split; [| reflexivity]]].
          unfold exemptb; destruct x0; [exact (Hx eq_refl) | reflexivity].
    Qed.

    Lemma dependees_disjunct_spec : forall I A a y,
        T.DependeesSet.In y
          (dependees I (Name.Disjunct A, Version.Atom a)) <->
        y = dependee (inst_repo I) (inst_prov I) a.
    Proof. intros; apply SOde.singleton_in. Qed.

    Lemma dependees_soft_spec : forall I A a y,
        T.DependeesSet.In y
          (dependees I (Name.Soft A, Version.Atom a)) <->
        y = dependee (inst_repo I) (inst_prov I) a.
    Proof. intros; apply SOde.singleton_in. Qed.

    Lemma dependees_soft_escape : forall I A,
        dependees I (Name.Soft A, Version.Zero) =
        T.DependeesSet.empty.
    Proof. reflexivity. Qed.

    Lemma dependees_selector_spec : forall I a (m : N.t) (w : V.t) y,
        T.DependeesSet.In y
          (dependees I (Name.Selector a, Version.Ref m w)) <->
        y = (Name.Orig m, T.VSet.singleton (Version.Orig w)).
    Proof. intros; apply SOde.singleton_in. Qed.

    Lemma dependees_selector_real_spec :
      forall I (n : N.t) (phi : Ver.Formula) (u : V.t) y,
        T.DependeesSet.In y
          (dependees I (Name.Selector (n, phi), Version.RefReal u)) <->
        y = (Name.Orig n, T.VSet.singleton (Version.Orig u)).
    Proof. intros; apply SOde.singleton_in. Qed.

    Lemma cardinal_in : forall A (a : Atom.t),
        AtomSet.In a (clauseAtoms A) -> 1 <= AtomSet.cardinal (clauseAtoms A).
    Proof.
      intros A a Ha.
      rewrite AtomSet.cardinal_spec.
      apply SOap.elements_in in Ha.
      destruct (AtomSet.elements (clauseAtoms A)); [destruct Ha | cbn; lia].
    Qed.

    Theorem debian_soundness :
      forall I (S : T.PkgSet.t),
        T.IsResolution (reduceReal I) (reduceDeps I)
          (embedPkg (inst_root I)) S ->
        IsResolution I (debianResolution S).
    Proof.
      intros I S [Hsub Hroot Hdep Huniq].
      assert (Hdependee : forall (p : T.Pkg.t) (a : Atom.t),
          T.PkgSet.In p S ->
          T.DependeesSet.In (dependee (inst_repo I) (inst_prov I) a)
            (dependees I p) ->
          exists q, PkgSet.In q (debianResolution S) /\
            Match (inst_prov I) q a).
      { intros p [an af] HsS Hedge.
        assert (HsReal := Hsub _ HsS).
        unfold dependee in Hedge.
        destruct (provb (inst_prov I) (an, af)) eqn:Hpb; rewrite ?Hpb in Hedge.
        - assert (Hd : T.DepRel.In
              (p, (Name.Selector (an, af),
                   us (inst_repo I) (inst_prov I) (an, af)))
              (reduceDeps I))
            by (apply mem_reduceDeps; split; [exact HsReal | exact Hedge]).
          destruct (Hdep _ HsS _ _ Hd) as [dv [Hdv HdvS]].
          apply mem_us in Hdv.
          destruct Hdv as [[u [Hu ->]] | [m0 [u0 [vt [Hin [Hvt ->]]]]]].
          + assert (Hedge2 : T.DependeesSet.In
                (Name.Orig an, T.VSet.singleton (Version.Orig u))
                (dependees I
                   (Name.Selector (an, af), Version.RefReal u)))
              by (apply dependees_selector_real_spec; reflexivity).
            assert (Hd2 : T.DepRel.In
                ((Name.Selector (an, af), Version.RefReal u),
                 (Name.Orig an, T.VSet.singleton (Version.Orig u)))
                (reduceDeps I))
              by (apply mem_reduceDeps; split;
                  [apply Hsub; exact HdvS | exact Hedge2]).
            destruct (Hdep _ HdvS _ _ Hd2) as [dv2 [Hdv2 Hdv2S]].
            apply T.VSet.singleton_spec in Hdv2; rewrite Hdv2 in Hdv2S.
            exists (an, u); split.
            { apply mem_debianResolution; exact Hdv2S. }
            { left; cbn [aname aform fst snd]; split; [reflexivity |].
              unfold evalAt, Ver.eval in Hu; apply VSet.filter_spec' in Hu.
              destruct Hu as [_ Hh]; exact Hh. }
          + assert (Hedge2 : T.DependeesSet.In
                (Name.Orig m0, T.VSet.singleton (Version.Orig u0))
                (dependees I
                   (Name.Selector (an, af), Version.Ref m0 u0)))
              by (apply dependees_selector_spec; reflexivity).
            assert (Hd2 : T.DepRel.In
                ((Name.Selector (an, af), Version.Ref m0 u0),
                 (Name.Orig m0, T.VSet.singleton (Version.Orig u0)))
                (reduceDeps I))
              by (apply mem_reduceDeps; split;
                  [apply Hsub; exact HdvS | exact Hedge2]).
            destruct (Hdep _ HdvS _ _ Hd2) as [dv2 [Hdv2 Hdv2S]].
            apply T.VSet.singleton_spec in Hdv2; rewrite Hdv2 in Hdv2S.
            exists (m0, u0); split.
            { apply mem_debianResolution; exact Hdv2S. }
            { right; exists vt; split; [exact Hin | exact Hvt]. }
        - assert (Hd : T.DepRel.In
              (p, (Name.Orig an, embedVS (evalAt (inst_repo I) (an, af))))
              (reduceDeps I))
            by (apply mem_reduceDeps; split; [exact HsReal | exact Hedge]).
          destruct (Hdep _ HsS _ _ Hd) as [dv [Hdv HdvS]].
          unfold embedVS in Hdv; apply SOvw.mem_map in Hdv;
            destruct Hdv as [u [Hu ->]].
          exists (an, u); split.
          { apply mem_debianResolution; exact HdvS. }
          { left; cbn [aname aform fst snd]; split; [reflexivity |].
            unfold evalAt, Ver.eval in Hu; apply VSet.filter_spec' in Hu.
            destruct Hu as [_ Hh]; exact Hh. } }
      constructor.
      - intros p Hp.
        apply mem_debianResolution in Hp.
        apply Hsub in Hp.
        rewrite (surjective_pairing p).
        assert (Hv := mem_reduceReal I
                        (Name.Orig (fst p)) (Version.Orig (snd p)) Hp).
        apply versions_orig_spec in Hv.
        destruct Hv as [[v [HvR Hv]] | [_ Hv]]; [| discriminate Hv].
        injection Hv as Hv; subst v.
        exact HvR.
      - apply mem_debianResolution; exact Hroot.
      - intros p Hp A HA.
        apply mem_debianResolution in Hp.
        destruct (AtomSet.cardinal (clauseAtoms A) =? 1) eqn:Hcard.
        + destruct (AtomSet.min_elt (clauseAtoms A)) as [a |] eqn:Hmin.
          * assert (HaA : AtomSet.In a (clauseAtoms A))
              by (apply AtomSet.min_elt_spec1; exact Hmin).
            assert (Hedge : T.DependeesSet.In
                              (dependee (inst_repo I) (inst_prov I) a)
                              (dependees I (embedPkg p))).
            { apply (dependees_orig_spec I (fst p) (snd p)).
              left; exists A; split.
              - rewrite <- (surjective_pairing p); exact HA.
              - left; split; [exact Hcard |].
                exists a; split; [exact Hmin | reflexivity]. }
            destruct (Hdependee (embedPkg p) a Hp Hedge) as [q [HqS HqM]].
            exists a; split; [apply mem_clauseAtoms; exact HaA |].
            exists q; split; assumption.
          * exfalso.
            apply AtomSet.min_elt_spec3 in Hmin.
            apply Nat.eqb_eq in Hcard.
            rewrite AtomSet.cardinal_spec in Hcard.
            destruct (AtomSet.elements (clauseAtoms A)) as [| z l] eqn:He;
              [discriminate |].
            apply (Hmin z).
            apply SOap.elements_in.
            rewrite He; left; reflexivity.
        + assert (Hedge : T.DependeesSet.In (Name.Disjunct A, versionsDisj A)
                            (dependees I (embedPkg p))).
          { apply (dependees_orig_spec I (fst p) (snd p)).
            left; exists A; split.
            - rewrite <- (surjective_pairing p); exact HA.
            - right; split; [exact Hcard | reflexivity]. }
          assert (Hd : T.DepRel.In
                         (embedPkg p, (Name.Disjunct A, versionsDisj A))
                         (reduceDeps I))
            by (apply mem_reduceDeps; split;
                [apply Hsub; exact Hp | exact Hedge]).
          destruct (Hdep _ Hp _ _ Hd) as [dv [Hdv HdvS]].
          unfold versionsDisj in Hdv; apply SOaw.mem_map in Hdv;
            destruct Hdv as [a [HaA ->]].
          assert (Hedge2 : T.DependeesSet.In
                             (dependee (inst_repo I) (inst_prov I) a)
                             (dependees I
                                (Name.Disjunct A, Version.Atom a)))
            by (apply dependees_disjunct_spec; reflexivity).
          destruct
            (Hdependee (Name.Disjunct A, Version.Atom a) a HdvS Hedge2)
            as [q [HqS HqM]].
          exists a; split; [apply mem_clauseAtoms; exact HaA |].
          exists q; split; assumption.
      - intros pn pv Hp a e HaG [m [qv [HqS [Hqp [Hxq HqM]]]]].
        apply mem_debianResolution in Hp.
        apply mem_debianResolution in HqS.
        destruct (N.eq_dec m pn) as [-> | Hne].
        { assert (E := Huniq (Name.Orig pn) (Version.Orig qv) (Version.Orig pv)
                         HqS Hp).
          injection E as E; apply Hqp; rewrite E; reflexivity. }
        assert (Hmb : matchb (inst_prov I) (m, qv) a = true)
          by (apply matchb_iff; exact HqM).
        assert (HqR : PkgSet.In (m, qv) (inst_repo I)).
        { assert (H := Hsub _ HqS).
          apply mem_reduceReal, versions_orig_spec in H.
          destruct H as [[v [HvR Hv]] | [_ Hv]]; [| discriminate Hv].
          injection Hv as ->; exact HvR. }
        assert (Hqn : NSet.In m (confNames (inst_repo I) (inst_prov I) a))
          by (apply mem_confNames; exists qv; auto).
        assert (Hedge : T.DependeesSet.In
                          (Name.Orig m,
                           complementVS (inst_repo I) (inst_prov I) a m)
                          (dependees I (embedPkg (pn, pv)))).
        { apply (dependees_orig_spec I pn pv).
          right; right; exists a, e, m; auto 6. }
        assert (Hd : T.DepRel.In
                       (embedPkg (pn, pv),
                        (Name.Orig m,
                         complementVS (inst_repo I) (inst_prov I) a m))
                       (reduceDeps I))
          by (apply mem_reduceDeps; split;
              [apply Hsub; exact Hp | exact Hedge]).
        destruct (Hdep _ Hp _ _ Hd) as [dv [Hdv HdvS]].
        assert (E := Huniq (Name.Orig m) dv (Version.Orig qv) HdvS HqS);
          subst dv.
        apply mem_complementVS in Hdv.
        destruct Hdv as [Hdv | [u [_ [Hmu E]]]]; [discriminate Hdv |].
        injection E as <-; congruence.
      - intros n v v' Hv Hv'.
        apply mem_debianResolution in Hv; apply mem_debianResolution in Hv'.
        assert (H := Huniq (Name.Orig n)
                       (Version.Orig v) (Version.Orig v') Hv Hv').
        injection H as H; exact H.
    Qed.

    Definition sat (Pi : Prov.t) (S : PkgSet.t) (a : Atom.t) : option Pkg.t :=
      PkgSet.min_elt (PkgSet.filter (fun q => matchb Pi q a) S).

    Definition satAtoms (Pi : Prov.t) (S : PkgSet.t) (A : Clause.t) :
        AtomSet.t :=
      AtomSet.filter (fun a =>
          PkgSet.exists_ (fun q => matchb Pi q a) S)
        (clauseAtoms A).

    Definition satClause (Pi : Prov.t) (S : PkgSet.t) (A : Clause.t) :
        option Atom.t :=
      AtomSet.min_elt (satAtoms Pi S A).

    Definition rmatchb (q : Pkg.t) (a : Atom.t) : bool :=
      andb (NEqb.eqb (fst q) (aname a)) (Ver.satisfiesb (snd q) (aform a)).

    Definition chosenVersion '((m, w) : Pkg.t) (a : Atom.t) : Version.t :=
      if rmatchb (m, w) a then Version.RefReal w else Version.Ref m w.

    Definition chooseSatisfier (Pi : Prov.t) (S : PkgSet.t) (a : Atom.t) :
        option Version.t :=
      match sat Pi S a with
      | Some q => Some (chosenVersion q a)
      | None => None
      end.

    Definition cwSelector (Pi : Prov.t) (S : PkgSet.t) (A : Clause.t) :
        T.PkgSet.t :=
      SOap.filterMap (fun a =>
          if provb Pi a
          then match chooseSatisfier Pi S a with
               | Some v => Some (Name.Selector a, v)
               | None => None
               end
          else None)
        (clauseAtoms A).

    Definition cwSoft (Pi : Prov.t) (S : PkgSet.t) (A : Clause.t) : Version.t :=
      match satClause Pi S A with
      | Some a => Version.Atom a
      | None => Version.Zero
      end.

    Definition coreResolution (I : Inst) (S : PkgSet.t) : T.PkgSet.t :=
      T.PkgSet.union (SOrp.map embedPkg S)
        (T.PkgSet.union
           (SOcp.filterMap (fun c =>
                if andb (PkgSet.mem (fst c) S)
                     (2 <=? AtomSet.cardinal (clauseAtoms (snd c)))
                then match satClause (inst_prov I) S (snd c) with
                     | Some a => Some (Name.Disjunct (snd c), Version.Atom a)
                     | None => None
                     end
                else None)
              (inst_deps I))
           (T.PkgSet.union
              (SOcp.filterMap (fun c =>
                   if PkgSet.mem (fst c) S
                   then Some (Name.Soft (snd c), cwSoft (inst_prov I) S (snd c))
                   else None)
                 (inst_rec I))
              (T.PkgSet.union
                 (SOcp.unionMap (fun '(p, A) =>
                      if PkgSet.mem p S
                      then cwSelector (inst_prov I) S A
                      else T.PkgSet.empty)
                    (allClauses (inst_deps I) (inst_rec I)))
                 (absentPkgs (C.absentIn S (repoNames (inst_repo I))))))).

    Lemma cardinal1_eq : forall A (a b : Atom.t),
        AtomSet.cardinal (clauseAtoms A) = 1 ->
        AtomSet.In a (clauseAtoms A) -> AtomSet.In b (clauseAtoms A) -> a = b.
    Proof.
      intros A a b Hcard Ha Hb.
      rewrite AtomSet.cardinal_spec in Hcard.
      apply SOap.elements_in in Ha; apply SOap.elements_in in Hb.
      destruct (AtomSet.elements (clauseAtoms A)) as [| c l]; [discriminate |].
      destruct l; [| discriminate].
      destruct Ha as [Ha | []]; destruct Hb as [Hb | []]; subst; reflexivity.
    Qed.

    Lemma mem_satAtoms : forall Pi S A a,
        AtomSet.In a (satAtoms Pi S A) <->
        AtomSet.In a (clauseAtoms A) /\
        exists q, PkgSet.In q S /\ matchb Pi q a = true.
    Proof.
      intros Pi S A a; unfold satAtoms.
      rewrite AtomSet.filter_spec'.
      rewrite PkgSet.exists_spec'.
      unfold PkgSet.Exists; reflexivity.
    Qed.

    Lemma chooseSatisfier_spec : forall Pi S a v,
        chooseSatisfier Pi S a = Some v ->
        exists m w, PkgSet.In (m, w) S /\ matchb Pi (m, w) a = true /\
          v = chosenVersion (m, w) a.
    Proof.
      intros Pi S a u H; unfold chooseSatisfier, sat in H.
      destruct (PkgSet.min_elt (PkgSet.filter (fun q => matchb Pi q a) S))
        as [q |] eqn:Hmin; [| discriminate].
      injection H as <-.
      apply PkgSet.min_elt_spec1 in Hmin.
      rewrite PkgSet.filter_spec' in Hmin.
      destruct Hmin as [HqS Hm].
      destruct q as [n v].
      exists n, v; split; [exact HqS | split; [exact Hm | reflexivity]].
    Qed.

    Lemma chooseSatisfier_some : forall Pi S a (q : Pkg.t),
        PkgSet.In q S -> matchb Pi q a = true ->
        exists v, chooseSatisfier Pi S a = Some v.
    Proof.
      intros Pi S a q HqS Hm; unfold chooseSatisfier, sat.
      destruct (PkgSet.min_elt (PkgSet.filter (fun q0 => matchb Pi q0 a) S))
        as [q1 |] eqn:Hmin.
      - exists (chosenVersion q1 a); reflexivity.
      - exfalso.
        apply PkgSet.min_elt_spec3 in Hmin.
        apply (Hmin q).
        rewrite PkgSet.filter_spec'.
        split; assumption.
    Qed.

    Lemma mem_cwSelector : forall Pi S A p,
        T.PkgSet.In p (cwSelector Pi S A) <->
        exists a, AtomSet.In a (clauseAtoms A) /\ provb Pi a = true /\
          exists v, chooseSatisfier Pi S a = Some v /\ p = (Name.Selector a, v).
    Proof.
      intros Pi S A p; unfold cwSelector.
      rewrite SOap.mem_filterMap.
      split.
      - intros [a [Ha Hy]]; cbn beta iota in Hy.
        destruct (provb Pi a) eqn:Hp; [| discriminate].
        destruct (chooseSatisfier Pi S a) as [w0 |] eqn:Hcs; [| discriminate].
        injection Hy as <-; eauto 6.
      - intros [a [Ha [Hp [w0 [Hcs ->]]]]].
        exists a; split; [exact Ha | cbn beta iota].
        rewrite Hp, Hcs; reflexivity.
    Qed.

    Lemma cwSoft_versionsSoft : forall Pi S A,
        T.VSet.In (cwSoft Pi S A) (versionsSoft A).
    Proof.
      intros Pi S A; unfold cwSoft, satClause.
      destruct (AtomSet.min_elt (satAtoms Pi S A)) as [a |] eqn:Hmin;
        apply mem_versionsSoft; [right | left; reflexivity].
      apply AtomSet.min_elt_spec1, mem_satAtoms in Hmin.
      exists a; split; [exact (proj1 Hmin) | reflexivity].
    Qed.

    Inductive CoreMem (I : Inst) (S : PkgSet.t) : T.Pkg.t -> Prop :=
    | CoreReal : forall n v, PkgSet.In (n, v) S ->
        CoreMem I S (Name.Orig n, Version.Orig v)
    | CoreDisjunct : forall p Al a, Deps.In (p, Al) (inst_deps I) ->
        PkgSet.mem p S = true ->
        (2 <=? AtomSet.cardinal (clauseAtoms Al)) = true ->
        AtomSet.min_elt (satAtoms (inst_prov I) S Al) = Some a ->
        CoreMem I S (Name.Disjunct Al, Version.Atom a)
    | CoreSoft : forall p Al, Deps.In (p, Al) (inst_rec I) ->
        PkgSet.mem p S = true ->
        CoreMem I S (Name.Soft Al, cwSoft (inst_prov I) S Al)
    | CoreSelector : forall p Al a v,
        Deps.In (p, Al) (allClauses (inst_deps I) (inst_rec I)) ->
        PkgSet.mem p S = true -> AtomSet.In a (clauseAtoms Al) ->
        provb (inst_prov I) a = true ->
        chooseSatisfier (inst_prov I) S a = Some v ->
        CoreMem I S (Name.Selector a, v)
    | CoreAbsent : forall n v, PkgSet.In (n, v) (inst_repo I) ->
        (forall v, ~ PkgSet.In (n, v) S) ->
        CoreMem I S (Name.Orig n, Version.Bot).

    Lemma mem_coreResolution : forall I S q,
        T.PkgSet.In q (coreResolution I S) <->
        CoreMem I S q.
    Proof.
      intros I S q; unfold coreResolution, satClause.
      rewrite !T.PkgSet.union_spec, SOrp.mem_map, SOcp.mem_filterMap_if,
        SOcp.mem_filterMap, SOcp.mem_unionMap, mem_absentPkgs.
      split.
      - intros [[[n v] [Hp ->]] | [[[p Al] [Hc Hy]] | [[[p Al] [Hc [Hm ->]]]
               | [[[p Al] [Hc Hy]] | [n [Hn ->]]]]]].
        + apply CoreReal; exact Hp.
        + cbn [fst snd] in Hy.
          destruct (andb (PkgSet.mem p S)
                      (2 <=? AtomSet.cardinal (clauseAtoms Al)))
            eqn:Hg; [| discriminate].
          destruct (AtomSet.min_elt (satAtoms (inst_prov I) S Al))
            as [a |] eqn:Hmin;
            [| discriminate].
          injection Hy as <-; apply andb_prop in Hg as [Hm Hcard].
          eapply CoreDisjunct; eassumption.
        + eapply CoreSoft; eassumption.
        + cbn beta iota in Hy; apply SOcp.in_if_empty in Hy as [Hm Hy].
          apply mem_cwSelector in Hy; mem_destruct.
          eapply CoreSelector; eassumption.
        + apply C.mem_absentIn in Hn as [Hn Hnone].
          apply mem_repoNames in Hn as [v Hv]; eapply CoreAbsent; eassumption.
      - destruct 1 as [n v Hp | p Al a Hc Hm Hcard Hmin | p Al Hc Hm
                      | p Al a w Hc Hm Ha Hpv Hcs | n v Hn Hnone].
        + left; exists (n, v); auto.
        + right; left; exists (p, Al); split; [exact Hc | cbn [fst snd]].
          rewrite Hm, Hcard, Hmin; reflexivity.
        + right; right; left; exists (p, Al); auto.
        + right; right; right; left; exists (p, Al); split; [exact Hc |].
          cbn beta iota; rewrite Hm; apply mem_cwSelector; eauto 7.
        + right; right; right; right; exists n; split; [| reflexivity].
          apply C.mem_absentIn; split; [apply mem_repoNames; eauto | exact Hnone].
    Qed.

    Theorem debian_completeness :
      forall I (S : PkgSet.t),
        IsResolution I S ->
        T.IsResolution (reduceReal I) (reduceDeps I)
          (embedPkg (inst_root I)) (coreResolution I S).
    Proof.
      intros I S [Hsub Hroot Hclo Hconf Huniq].
      assert (Hus : forall (q : Pkg.t) (a : Atom.t),
          PkgSet.In q S -> Match (inst_prov I) q a ->
          T.VSet.In (chosenVersion q a) (us (inst_repo I) (inst_prov I) a)).
      { intros [m qv] [an af] HqS HM.
        unfold chosenVersion, rmatchb; cbn [aname aform fst snd].
        destruct (andb (NEqb.eqb m an) (Ver.satisfiesb qv af)) eqn:Hr;
          apply mem_us.
        - apply andb_prop in Hr; destruct Hr as [Hn Hh].
          apply NEqb.eqb_true_iff in Hn as ->.
          left; exists qv; split; [| reflexivity].
          unfold evalAt, Ver.eval; cbn [aname aform fst snd].
          apply VSet.filter_spec'.
          split; [| exact Hh].
          apply C.mem_versions.
          apply Hsub; exact HqS.
        - destruct HM as [[Hfq Hh] | [vt [Hin Hvt]]].
          + exfalso; cbn [aname aform fst snd] in Hfq, Hh.
            subst m; rewrite NEqb.eqb_refl, Hh in Hr; discriminate Hr.
          + right; exists m, qv, vt.
            split; [exact Hin | split; [exact Hvt | reflexivity]]. }
      assert (Hfwd : forall (a : Atom.t) (q : Pkg.t) n vs,
          PkgSet.In q S -> Match (inst_prov I) q a ->
          (exists p A, Deps.In (p, A) (allClauses (inst_deps I) (inst_rec I)) /\
             PkgSet.In p S /\
             AtomSet.In a (clauseAtoms A)) ->
          (n, vs) = dependee (inst_repo I) (inst_prov I) a ->
          exists dv, T.VSet.In dv vs /\
            T.PkgSet.In (n, dv) (coreResolution I S)).
      { intros a q n vs HqS HM Hcl Heq.
        unfold dependee in Heq.
        destruct (provb (inst_prov I) a) eqn:Hpb; cbn [andb] in Heq;
          injection Heq as -> ->.
        - assert (Hmb : matchb (inst_prov I) q a = true)
            by (apply matchb_iff; exact HM).
          destruct (chooseSatisfier_some (inst_prov I) S a q HqS Hmb) as
            [w0 Hcs].
          pose proof (chooseSatisfier_spec (inst_prov I) S a w0 Hcs)
            as [qn0 [qv0 [Hq0S [Hq0m ->]]]].
          exists (chosenVersion (qn0, qv0) a); split.
          + apply (Hus (qn0, qv0)); [exact Hq0S | apply matchb_iff; exact Hq0m].
          + destruct Hcl as [cp [cA [Hc [HcpS HaA]]]].
            apply mem_coreResolution; eapply CoreSelector; try eassumption.
            apply PkgSet.mem_spec; exact HcpS.
        - destruct q as [m qv], a as [an af].
          destruct HM as [[Hfq Hh] | [vt [Hin Hvt]]].
          2:{ exfalso.
              assert (Hpb2 : provb (inst_prov I) (an, af) = true)
                by (apply provb_iff; exists (m, qv), vt; split; assumption).
              congruence. }
          exists (Version.Orig qv); split.
          + unfold embedVS; apply SOvw.mem_map;
              exists qv; split; [| reflexivity].
            unfold evalAt, Ver.eval; apply VSet.filter_spec'.
            split; [| exact Hh].
            apply C.mem_versions.
            rewrite <- Hfq.
            apply Hsub; exact HqS.
          + rewrite <- Hfq; apply mem_coreResolution, CoreReal; exact HqS. }
      constructor.
      - intros p' Hp'.
        apply mem_coreResolution in Hp'; unfold reduceReal.
        rewrite !T.PkgSet.union_spec, mem_realOrig, mem_realDisjunct,
          mem_realSoft, mem_realSelector, mem_absentPkgs.
        destruct Hp' as [n v Hp | cp cA a0 Hc Hm Hcard Hmin | cp cA Hc Hm
                       | cp cA a0 w0 Hc Hm Ha0 Hp0 Hcs | n0 v0 Hn0 _].
        + left; exists n, v; split; [apply Hsub; exact Hp | reflexivity].
        + right; left; exists cp, cA; split; [exact Hc |].
          split; [exact Hcard |].
          apply AtomSet.min_elt_spec1, mem_satAtoms in Hmin.
          exists a0; split; [exact (proj1 Hmin) | reflexivity].
        + right; right; left; exists cp, cA; split; [exact Hc |].
          pose proof (cwSoft_versionsSoft (inst_prov I) S cA) as Hw.
          apply mem_versionsSoft in Hw.
          destruct Hw as [-> | [a [Ha ->]]]; [left; reflexivity |].
          right; exists a; split; [exact Ha | reflexivity].
        + right; right; right; left; exists cp, cA; split; [exact Hc |].
          exists a0; split; [exact Ha0 |]; split; [exact Hp0 |].
          exists w0; split; [| reflexivity].
          apply chooseSatisfier_spec in Hcs.
          destruct Hcs as [m [qv [HqS [Hqm ->]]]].
          apply (Hus (m, qv)); [exact HqS | apply matchb_iff; exact Hqm].
        + right; right; right; right; exists n0; split; [| reflexivity].
          apply mem_repoNames; exists v0; exact Hn0.
      - revert Hroot; destruct (inst_root I) as [rn rv]; intro Hroot.
        apply mem_coreResolution, CoreReal; exact Hroot.
      - intros p' Hp' n vs Hd.
        apply mem_coreResolution in Hp'.
        apply mem_reduceDeps in Hd; destruct Hd as [_ Hout].
        destruct Hp' as [pn pv HpS | cp cA a0 Hc Hmem Hcard Hmin | cp cA Hc Hmem
                       | cp cA a0 w0 Hc Hmem Ha0 Hpv Hcs | n0 _ _ _].
        + apply (dependees_orig_spec I pn pv) in Hout.
          destruct Hout as [[A [HA Hcase]] |
                            [[A [HA Heq]] |
                             [a0 [x0 [m [Ha0 [Hqn [Hne [Hx Heq]]]]]]]]].
          * assert (HpA : Deps.In ((pn, pv), A) (inst_deps I)) by exact HA.
            destruct (Hclo (pn, pv) HpS A HpA) as [aw [HawA [q [HqS HqM]]]].
            apply mem_clauseAtoms in HawA.
            destruct Hcase as [[Hcard [am [Hmin Heq]]] | [Hcard Heq]].
            { assert (HamA : AtomSet.In am (clauseAtoms A))
                by (apply AtomSet.min_elt_spec1; exact Hmin).
              assert (Haw : aw = am)
                by (apply Nat.eqb_eq in Hcard;
                    exact (cardinal1_eq A aw am Hcard HawA HamA)).
              subst aw.
              apply (Hfwd am q n vs HqS HqM); [| exact Heq].
              exists (pn, pv), A.
              split; [apply allClauses_inL; exact HpA |].
              split; [exact HpS | exact HamA]. }
            { injection Heq as -> ->.
              assert (Hsat : AtomSet.In aw (satAtoms (inst_prov I) S A)).
              { apply mem_satAtoms; split; [exact HawA |].
                exists q; split; [exact HqS | apply matchb_iff; exact HqM]. }
              destruct (AtomSet.min_elt (satAtoms (inst_prov I) S A)) as [am |]
                eqn:Hmin.
              2:{ exfalso; apply AtomSet.min_elt_spec3 in Hmin.
                  exact (Hmin aw Hsat). }
              assert (Hmin1 := AtomSet.min_elt_spec1 Hmin).
              apply mem_satAtoms in Hmin1; destruct Hmin1 as [HamA _].
              exists (Version.Atom am); split.
              - unfold versionsDisj; apply SOaw.mem_map; exists am; split;
                  [exact HamA | reflexivity].
              - apply mem_coreResolution; eapply CoreDisjunct;
                  [exact HpA | apply PkgSet.mem_spec; exact HpS | | exact Hmin].
                apply Nat.leb_le; apply Nat.eqb_neq in Hcard.
                assert (Hle := cardinal_in A aw HawA); lia. }
          * injection Heq as -> ->.
            exists (cwSoft (inst_prov I) S A);
              split; [apply cwSoft_versionsSoft |].
            apply mem_coreResolution; eapply CoreSoft;
              [exact HA | apply PkgSet.mem_spec; exact HpS].
          * injection Heq as -> ->.
            destruct (C.hasNameb S m) eqn:Hh.
            { apply C.hasNameb_true in Hh; destruct Hh as [u Hu].
              exists (Version.Orig u); split.
              - apply mem_complementVS; right; exists u.
                split; [apply Hsub; exact Hu |]; split; [| reflexivity].
                destruct (matchb (inst_prov I) (m, u) a0) eqn:Hm; [| exact Hm].
                exfalso; apply (Hconf pn pv HpS a0 x0 Ha0).
                exists m, u; split; [exact Hu |].
                split; [intro E; injection E as E _; exact (Hne E) |].
                split; [exact Hx | apply matchb_iff; exact Hm].
              - apply mem_coreResolution, CoreReal; exact Hu. }
            { assert (Hnone := proj1 (C.hasNameb_false S m) Hh).
              exists Version.Bot; split; [apply mem_complementVS; left; reflexivity |].
              apply mem_confNames in Hqn; destruct Hqn as [u [HuR _]].
              apply mem_coreResolution; exact (CoreAbsent I S m u HuR Hnone). }
        + apply dependees_disjunct_spec in Hout; rename Hout into Heq.
          assert (Hmin1 := AtomSet.min_elt_spec1 Hmin).
          apply mem_satAtoms in Hmin1; destruct Hmin1 as [Ha0A [q [HqS Hqm]]].
          apply (Hfwd a0 q n vs HqS);
            [apply matchb_iff; exact Hqm | | exact Heq].
          exists cp, cA; split; [apply allClauses_inL; exact Hc |].
          split; [apply PkgSet.mem_spec; exact Hmem | exact Ha0A].
        + unfold cwSoft, satClause in Hout.
          destruct (AtomSet.min_elt (satAtoms (inst_prov I) S cA))
            as [a0 |] eqn:Hmin.
          * apply dependees_soft_spec in Hout; rename Hout into Heq.
            assert (Hmin1 := AtomSet.min_elt_spec1 Hmin).
            apply mem_satAtoms in Hmin1; destruct Hmin1 as [Ha0A [q [HqS Hqm]]].
            apply (Hfwd a0 q n vs HqS);
              [apply matchb_iff; exact Hqm | | exact Heq].
            exists cp, cA; split; [apply allClauses_inR; exact Hc |].
            split; [apply PkgSet.mem_spec; exact Hmem | exact Ha0A].
          * rewrite dependees_soft_escape in Hout.
            exfalso; exact (SOde.empty_in _ Hout).
        + pose proof (chooseSatisfier_spec (inst_prov I) S a0 w0 Hcs)
            as [qn0 [qv0 [Hq0S [Hq0m Ew]]]].
          subst w0.
          unfold chosenVersion, rmatchb in Hout; cbn [fst snd] in Hout.
          destruct (andb (NEqb.eqb qn0 (aname a0))
                      (Ver.satisfiesb qv0 (aform a0)))
            eqn:Hr.
          * destruct a0 as [an0 af0].
            apply dependees_selector_real_spec in Hout.
            injection Hout as -> ->.
            apply andb_prop in Hr; destruct Hr as [Hn _].
            apply NEqb.eqb_true_iff in Hn; cbn [aname fst] in Hn.
            exists (Version.Orig qv0); split.
            { apply T.VSet.singleton_spec; reflexivity. }
            { rewrite <- Hn; apply mem_coreResolution, CoreReal.
              exact Hq0S. }
          * apply dependees_selector_spec in Hout.
            injection Hout as -> ->.
            exists (Version.Orig qv0); split.
            { apply T.VSet.singleton_spec; reflexivity. }
            { apply mem_coreResolution, CoreReal; exact Hq0S. }
        + cbn [dependees] in Hout; exfalso; exact (SOde.empty_in _ Hout).
      - intros n cv1 cv2 H1 H2.
        apply mem_coreResolution in H1, H2.
        inversion H1 as [n1 v1 Hp1 | | | | n1]; subst;
          inversion H2 as [n2 v2 Hp2 | | | | n2]; subst;
          try congruence;
          try (exfalso; match goal with
                        | Hnone : forall v, ~ PkgSet.In _ S |- _ => eapply Hnone
                        end; eassumption).
        rewrite (Huniq n1 v1 v2 Hp1 Hp2); reflexivity.
    Qed.

    Module Lookup.

      Module SOcn := SetOps ClauseElt N Deps NSet.
      Definition atomNames (D : Deps.t) (p : Pkg.t) : NSet.t :=
        SOcn.unionMap (fun '(q, A) =>
            if Pkg.eq_dec q p then clauseNames A else NSet.empty)
          D.

      Module PkgFibred := FibredRel N V Pkg PkgSet.
      Lemma versions_tailFibre : forall R n,
          C.versions (PkgFibred.tailFibre R n) n = C.versions R n.
      Proof.
        intros R n; apply VSet.ext; intro v.
        rewrite !C.mem_versions.
        split; [exact (PkgFibred.tailFibre_subset R n (n, v)) |].
        intro H; apply PkgFibred.mem_tailFibre; split; [exact H | reflexivity].
      Qed.

      Lemma evalAt_tailFibre : forall R (n : N.t) (phi : Ver.Formula),
          evalAt (PkgFibred.tailFibre R n) (n, phi) = evalAt R (n, phi).
      Proof.
        intros R n phi; unfold evalAt.
        rewrite versions_tailFibre; reflexivity.
      Qed.

      Lemma provb_nodeFibre : forall Pi (n : N.t) (phi : Ver.Formula),
          provb (ProvFibred.nodeFibre Pi n) (n, phi) = provb Pi (n, phi).
      Proof.
        intros Pi n phi; unfold provb.
        apply Prov.exists_restrict; [apply ProvFibred.nodeFibre_subset |].
        intros [q [m v]] Hin Hb; cbn [aname aform fst snd] in Hb.
        apply andb_prop in Hb; destruct Hb as [Hn _].
        apply ProvFibred.mem_nodeFibre; split;
          [exact Hin | apply NEqb.eqb_true_iff; exact Hn].
      Qed.

      Lemma us_filter : forall R Pi (n : N.t) (phi : Ver.Formula),
          us (PkgFibred.tailFibre R n) (ProvFibred.nodeFibre Pi n) (n, phi) =
          us R Pi (n, phi).
      Proof.
        intros R Pi n phi; apply T.VSet.ext; intro u'; unfold us.
        rewrite !T.VSet.union_spec, evalAt_tailFibre.
        apply or_iff_compat_l.
        apply SOew.filterMap_restrict; [apply ProvFibred.nodeFibre_subset |].
        intros [q [m v]] Hin Hf; cbn [fst snd aname aform] in Hf.
        destruct (NEqb.eqb m n) eqn:Hn; [| discriminate Hf].
        apply ProvFibred.mem_nodeFibre; split;
          [exact Hin | apply NEqb.eqb_true_iff; exact Hn].
      Qed.

      Lemma dependee_filter : forall R Pi (n : N.t) (phi : Ver.Formula),
          dependee (PkgFibred.tailFibre R n) (ProvFibred.nodeFibre Pi n)
            (n, phi) =
          dependee R Pi (n, phi).
      Proof.
        intros R Pi n phi; unfold dependee.
        rewrite provb_nodeFibre, us_filter, evalAt_tailFibre; reflexivity.
      Qed.

      Lemma mem_atomNames : forall D (p : Pkg.t) (n : N.t),
          NSet.In n (atomNames D p) <->
          exists A, Deps.In (p, A) D /\
            exists phi, AtomSet.In (n, phi) (clauseAtoms A).
      Proof.
        intros D p n; unfold atomNames; rewrite SOcn.mem_unionMap.
        split.
        - intros [[q A] [Hc Hn]]; cbn beta iota in Hn.
          destruct (Pkg.eq_dec q p) as [-> | NE];
            [| exfalso; exact (SOcn.empty_in _ Hn)].
          apply mem_clauseNames in Hn.
          exists A; split; assumption.
        - intros [A [Hc Hf]].
          exists (p, A); split; [exact Hc | cbn beta iota; rewrite dec_refl].
          apply mem_clauseNames; exact Hf.
      Qed.

      Module ProvPreimage := PreimageOfKeys N ProvElt NSet Prov.
      Definition provPreimage (Pi : Prov.t) (ns : NSet.t) : Prov.t :=
        ProvPreimage.ofKeys ProvFibred.node ns Pi.

      Lemma evalAt_namePreimage : forall R ns (n : N.t) (phi : Ver.Formula),
          NSet.In n ns ->
          evalAt (C.namePreimage R ns) (n, phi) = evalAt R (n, phi).
      Proof.
        intros R ns n phi Hm; unfold evalAt.
        rewrite C.versions_namePreimage by exact Hm; reflexivity.
      Qed.

      Lemma provRestrict_sub : forall Pi ns (p : Pkg.t),
          Prov.Subset
            (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p)) Pi.
      Proof.
        intros Pi ns p e He; apply Prov.union_spec in He.
        destruct He as [He | He];
          [exact (ProvPreimage.ofKeys_subset _ _ _ _ He)
          | exact (ProvFibred.tailFibre_subset _ _ _ He)].
      Qed.

      Lemma provb_union_restrict :
        forall Pi ns (p : Pkg.t) (n : N.t) (phi : Ver.Formula),
          NSet.In n ns ->
          provb (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p))
            (n, phi)
          = provb Pi (n, phi).
      Proof.
        intros Pi ns p n phi Hm; unfold provb.
        apply Prov.exists_restrict; [apply provRestrict_sub |].
        intros [q [m v]] Hin Hb; cbn [aname aform fst snd] in Hb.
        apply andb_prop in Hb; destruct Hb as [Hn _].
        apply NEqb.eqb_true_iff in Hn as ->.
        apply Prov.union_spec; left; unfold provPreimage.
        apply ProvPreimage.mem_ofKeys; split; [exact Hin | exact Hm].
      Qed.

      Lemma us_union_restrict :
        forall R Pi ns (p : Pkg.t) (n : N.t) (phi : Ver.Formula),
          NSet.In n ns ->
          us (C.namePreimage R ns)
            (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p))
            (n, phi)
          = us R Pi (n, phi).
      Proof.
        intros R Pi ns p n phi Hm; apply T.VSet.ext; intro y; unfold us.
        rewrite !T.VSet.union_spec, evalAt_namePreimage by exact Hm.
        apply or_iff_compat_l.
        apply SOew.filterMap_restrict; [apply provRestrict_sub |].
        intros [q [m v]] Hin Hf; cbn [fst snd aname aform] in Hf.
        destruct (NEqb.eqb m n) eqn:Hn; [| discriminate Hf].
        apply NEqb.eqb_true_iff in Hn as ->.
        apply Prov.union_spec; left; unfold provPreimage.
        apply ProvPreimage.mem_ofKeys; split; [exact Hin | exact Hm].
      Qed.

      Lemma dependee_union_restrict :
        forall R Pi ns (p : Pkg.t) (n : N.t) (phi : Ver.Formula),
          NSet.In n ns ->
          dependee (C.namePreimage R ns)
            (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p))
            (n, phi)
          = dependee R Pi (n, phi).
      Proof.
        intros R Pi ns p n phi Hm; unfold dependee.
        rewrite provb_union_restrict, us_union_restrict, evalAt_namePreimage
          by exact Hm.
        reflexivity.
      Qed.

      Module DepsFibred := FibredRel Pkg Clause ClauseElt Deps.
      Module ConfFibred := FibredRel Pkg Conflictees ConfElt Conf.
      Theorem versions_lookupOrig : forall I (n : N.t),
          versions I (Name.Orig n) =
          versions
            (MkInst (PkgFibred.tailFibre (inst_repo I) n) Deps.empty Deps.empty
               Prov.empty Conf.empty (inst_root I))
            (Name.Orig n).
      Proof.
        intros I n; cbn [versions inst_repo]; rewrite versions_tailFibre.
        reflexivity.
      Qed.

      Theorem dependees_lookupAbsent : forall I (n : N.t),
          dependees I (Name.Orig n, Version.Bot) = T.DependeesSet.empty.
      Proof. intros; reflexivity. Qed.

      Definition providerNames (Pi : Prov.t) (n : N.t) : NSet.t :=
        SOpin.filterMap
          (fun e => if N.eq_dec (fst (snd e)) n then Some (fst (fst e)) else
             None)
          Pi.

      Lemma mem_providerNames : forall Pi (n m : N.t),
          NSet.In m (providerNames Pi n) <->
          exists q v, Prov.In (q, (n, v)) Pi /\ fst q = m.
      Proof.
        intros Pi n m; unfold providerNames; rewrite SOpin.mem_filterMap_dec.
        split; [intros [[q [m0 v]] [He [Hm ->]]]; cbn in Hm; subst m0; eauto |].
        intros [q [v [He <-]]]; exists (q, (n, v)); auto.
      Qed.

      Definition confRead (Pi : Prov.t) (G : Conf.t) (p : Pkg.t) : NSet.t :=
        SOgn.unionMap
          (fun e =>
             if Pkg.eq_dec (fst e) p
             then NSet.add (aname (fst (snd e)))
                    (providerNames Pi (aname (fst (snd e))))
             else NSet.empty)
          G.

      Lemma mem_confRead : forall Pi G (p : Pkg.t) (m : N.t),
          NSet.In m (confRead Pi G p) <->
          exists a e, Conf.In (p, (a, e)) G /\
                      (m = aname a \/ NSet.In m (providerNames Pi (aname a))).
      Proof.
        intros Pi G p m; unfold confRead; rewrite SOgn.mem_unionMap_dec.
        split.
        - intros [[q [a e]] [Hg [Hq Hx]]]; cbn [fst snd] in Hq, Hx; subst q.
          apply NSet.add_spec in Hx; eauto.
        - intros [a [e [Hg Hx]]]; exists (p, (a, e)); cbn [fst snd].
          rewrite NSet.add_spec; auto.
      Qed.

      Definition readNames (Pi : Prov.t) (D : Deps.t) (G : Conf.t) (p : Pkg.t)
        : NSet.t :=
        NSet.union (atomNames D p) (confRead Pi G p).

      Lemma matchb_provPreimage : forall Pi ns (p q : Pkg.t) a,
          NSet.In (aname a) ns ->
          matchb (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p))
            q a
          = matchb Pi q a.
      Proof.
        intros Pi ns p q a Hm; unfold matchb; f_equal.
        apply Prov.exists_restrict; [apply provRestrict_sub |].
        intros [q' [m v]] Hin Hb; cbn [fst snd aname aform] in Hb.
        apply andb_prop in Hb; destruct Hb as [_ Hb].
        apply andb_prop in Hb; destruct Hb as [Hn _].
        apply NEqb.eqb_true_iff in Hn as ->.
        apply Prov.union_spec; left; unfold provPreimage.
        apply ProvPreimage.mem_ofKeys; split; [exact Hin | exact Hm].
      Qed.

      Theorem dependees_lookupOrig : forall I (n : N.t) (v : V.t),
          dependees I (Name.Orig n, Version.Orig v) =
          let ms :=
            readNames (inst_prov I) (inst_deps I) (inst_conf I) (n, v) in
          dependees
            (MkInst (C.namePreimage (inst_repo I) ms)
               (DepsFibred.tailFibre (inst_deps I) (n, v))
               (DepsFibred.tailFibre (inst_rec I) (n, v))
               (Prov.union (provPreimage (inst_prov I) ms)
                  (ProvFibred.tailFibre (inst_prov I) (n, v)))
               (ConfFibred.tailFibre (inst_conf I) (n, v))
               (inst_root I))
            (Name.Orig n, Version.Orig v).
      Proof.
        intros I n v; cbv zeta; apply T.DependeesSet.ext; intro y.
        set (ms := readNames (inst_prov I) (inst_deps I) (inst_conf I) (n, v)).
        rewrite !dependees_orig_spec.
        cbn [inst_repo inst_deps inst_rec inst_prov inst_conf].
        assert (Hfib : forall (E : Deps.t) A,
                   Deps.In ((n, v), A) (DepsFibred.tailFibre E (n, v)) <->
                   Deps.In ((n, v), A) E).
        { intros E A; unfold DepsFibred.tailFibre.
          rewrite Deps.filter_spec'; cbn [DepsFibred.tail fst].
          split.
          - intros [HA _]; exact HA.
          - intro HA; split; [exact HA |].
            apply dec_refl. }
        assert (Hcfib : forall a e,
                   Conf.In ((n, v), (a, e))
                     (ConfFibred.tailFibre (inst_conf I) (n, v)) <->
                   Conf.In ((n, v), (a, e)) (inst_conf I)).
        { intros a e; unfold ConfFibred.tailFibre.
          rewrite Conf.filter_spec'; cbn [ConfFibred.tail fst].
          split.
          - intros [H _]; exact H.
          - intro H; split; [exact H |].
            apply dec_refl. }
        assert (Hatom : forall an,
                   NSet.In an (atomNames (inst_deps I) (n, v)) -> NSet.In an ms)
          by (intros an H; apply NSet.union_spec; left; exact H).
        assert (Hcn : forall a e, Conf.In ((n, v), (a, e)) (inst_conf I) ->
                                NSet.In (aname a) ms).
        { intros a e Hg; apply NSet.union_spec; right; apply mem_confRead.
          exists a, e; split; [exact Hg | left; reflexivity]. }
        assert (Hcp : forall a e (m : N.t) u vt,
                   Conf.In ((n, v), (a, e)) (inst_conf I) ->
                   Prov.In ((m, u), (aname a, vt)) (inst_prov I) ->
                   NSet.In m ms).
        { intros a e m u vt Hg Hin; apply NSet.union_spec; right.
          apply mem_confRead; exists a, e; split; [exact Hg | right].
          apply mem_providerNames; exists (m, u), vt; auto. }
        assert (Hmatch : forall a e (m : N.t) u,
                   Conf.In ((n, v), (a, e)) (inst_conf I) ->
                   matchb (inst_prov I) (m, u) a = true -> NSet.In m ms).
        { intros [an af] e m u Hg Hm; apply matchb_iff in Hm.
          destruct Hm as [[Hn _] | [vt [Hin _]]].
          - rewrite Hn; exact (Hcn (an, af) e Hg).
          - exact (Hcp (an, af) e m u vt Hg Hin). }
        assert (HconfN : forall a e, Conf.In ((n, v), (a, e)) (inst_conf I) ->
                   confNames (C.namePreimage (inst_repo I) ms)
                     (Prov.union (provPreimage (inst_prov I) ms)
                        (ProvFibred.tailFibre (inst_prov I) (n, v))) a
                   = confNames (inst_repo I) (inst_prov I) a).
        { intros a e Hg; apply NSet.ext; intro m; rewrite !mem_confNames.
          split; intros [u [HR Hm]]; exists u.
          - apply C.mem_namePreimage in HR.
            destruct HR as [HR _].
            rewrite matchb_provPreimage in Hm by exact (Hcn a e Hg).
            auto.
          - split;
              [| rewrite matchb_provPreimage by exact (Hcn a e Hg); exact Hm].
            apply C.mem_namePreimage; split;
              [exact HR | cbn [fst]; exact (Hmatch a e m u Hg Hm)]. }
        assert (Hadm : forall a e (m : N.t),
                   Conf.In ((n, v), (a, e)) (inst_conf I) ->
                   NSet.In m (confNames (inst_repo I) (inst_prov I) a) ->
                   complementVS (C.namePreimage (inst_repo I) ms)
                     (Prov.union (provPreimage (inst_prov I) ms)
                        (ProvFibred.tailFibre (inst_prov I) (n, v))) a m
                   = complementVS (inst_repo I) (inst_prov I) a m).
        { intros a e m Hg Hqn.
          assert (Hqn' : NSet.In m ms).
          { apply mem_confNames in Hqn; destruct Hqn as [u [_ Hm]].
            exact (Hmatch a e m u Hg Hm). }
          apply T.VSet.ext; intro w; rewrite !mem_complementVS.
          apply or_iff_compat_l.
          split; intros [u [HR [Hm Hw]]]; exists u.
          - apply C.mem_namePreimage in HR.
            destruct HR as [HR _].
            rewrite matchb_provPreimage in Hm by exact (Hcn a e Hg).
            auto.
          - split; [| split; [| exact Hw]].
            + apply C.mem_namePreimage; split;
                [exact HR | exact Hqn'].
            + rewrite matchb_provPreimage by exact (Hcn a e Hg); exact Hm. }
        split.
        - intros [[A [HA Hcase]] |
                  [[A [HA Hy]] |
                   [a [e [m [Hg [Hqn [Hne [Hx Hy]]]]]]]]].
          + left; exists A; split;
              [apply (proj2 (Hfib (inst_deps I) A)); exact HA |].
            destruct Hcase as [[Hcard [a0 [Hmin Hy]]] | [Hcard Hy]].
            * destruct a0 as [an af].
              assert (Hin : NSet.In an ms).
              { apply Hatom, mem_atomNames; exists A; split; [exact HA |].
                exists af; exact (AtomSet.min_elt_spec1 Hmin). }
              left; split; [exact Hcard |].
              exists (an, af); split; [exact Hmin |].
              rewrite dependee_union_restrict by exact Hin.
              exact Hy.
            * right; split; [exact Hcard | exact Hy].
          + right; left; exists A; split;
              [apply (proj2 (Hfib (inst_rec I) A)); exact HA | exact Hy].
          + right; right; exists a, e, m.
            split; [apply Hcfib; exact Hg |].
            split; [rewrite (HconfN a e Hg); exact Hqn |].
            split; [exact Hne |].
            split; [exact Hx |].
            rewrite (Hadm a e m Hg Hqn); exact Hy.
        - intros [[A [HA Hcase]] |
                  [[A [HA Hy]] |
                   [a [e [m [Hg [Hqn [Hne [Hx Hy]]]]]]]]].
          + apply (proj1 (Hfib (inst_deps I) A)) in HA.
            left; exists A; split; [exact HA |].
            destruct Hcase as [[Hcard [a0 [Hmin Hy]]] | [Hcard Hy]].
            * destruct a0 as [an af].
              assert (Hin : NSet.In an ms).
              { apply Hatom, mem_atomNames; exists A; split; [exact HA |].
                exists af; exact (AtomSet.min_elt_spec1 Hmin). }
              left; split; [exact Hcard |].
              exists (an, af); split; [exact Hmin |].
              rewrite dependee_union_restrict in Hy by exact Hin.
              exact Hy.
            * right; split; [exact Hcard | exact Hy].
          + right; left; exists A; split;
              [apply (proj1 (Hfib (inst_rec I) A)); exact HA | exact Hy].
          + apply Hcfib in Hg.
            rewrite (HconfN a e Hg) in Hqn.
            right; right; exists a, e, m.
            split; [exact Hg |].
            split; [exact Hqn |].
            split; [exact Hne |].
            split; [exact Hx |].
            rewrite (Hadm a e m Hg Hqn) in Hy; exact Hy.
      Qed.

      Theorem versions_lookupDisjunct : forall I (A : Clause.t),
          versions I (Name.Disjunct A) = versionsDisj A.
      Proof. intros; reflexivity. Qed.

      Theorem dependees_lookupDisjunct :
        forall I (A : Clause.t) (n : N.t) (phi : Ver.Formula),
          dependees I (Name.Disjunct A, Version.Atom (n, phi)) =
          dependees
            (MkInst (PkgFibred.tailFibre (inst_repo I) n) Deps.empty Deps.empty
               (ProvFibred.nodeFibre (inst_prov I) n) Conf.empty (inst_root I))
            (Name.Disjunct A, Version.Atom (n, phi)).
      Proof.
        intros I A n phi; cbn [dependees inst_repo inst_prov].
        rewrite dependee_filter; reflexivity.
      Qed.

      Theorem versions_lookupSoft : forall I (A : Clause.t),
          versions I (Name.Soft A) = versionsSoft A.
      Proof. intros; reflexivity. Qed.

      Theorem dependees_lookupSoft :
        forall I (A : Clause.t) (n : N.t) (phi : Ver.Formula),
          dependees I (Name.Soft A, Version.Atom (n, phi)) =
          dependees
            (MkInst (PkgFibred.tailFibre (inst_repo I) n) Deps.empty Deps.empty
               (ProvFibred.nodeFibre (inst_prov I) n) Conf.empty (inst_root I))
            (Name.Soft A, Version.Atom (n, phi)).
      Proof.
        intros I A n phi; cbn [dependees inst_repo inst_prov].
        rewrite dependee_filter; reflexivity.
      Qed.

      Theorem versions_lookupSelector :
        forall I (n : N.t) (phi : Ver.Formula),
          versions I (Name.Selector (n, phi)) =
          versions
            (MkInst (PkgFibred.tailFibre (inst_repo I) n) Deps.empty Deps.empty
               (ProvFibred.nodeFibre (inst_prov I) n) Conf.empty (inst_root I))
            (Name.Selector (n, phi)).
      Proof.
        intros I n phi; cbn [versions inst_repo inst_prov].
        symmetry; apply us_filter.
      Qed.

      Theorem dependees_lookupSelector :
        forall I (n : N.t) (phi : Ver.Formula) (v : Version.t),
          dependees I (Name.Selector (n, phi), v) =
          match v with
          | Version.Ref m w =>
              T.DependeesSet.singleton
                (Name.Orig m, T.VSet.singleton (Version.Orig w))
          | Version.RefReal u =>
              T.DependeesSet.singleton
                (Name.Orig n, T.VSet.singleton (Version.Orig u))
          | _ => T.DependeesSet.empty
          end.
      Proof. intros I n phi v; destruct v; reflexivity. Qed.

    End Lookup.

    Theorem debian_retraction : forall I S,
        debianResolution (coreResolution I S) = S.
    Proof.
      intros I S; apply PkgSet.ext; intros [n v].
      rewrite mem_debianResolution, mem_coreResolution.
      unfold embedPkg; cbn [fst snd].
      split; [intro H; inversion H; assumption | apply CoreReal].
    Qed.
  End Reduction.
End Debian.
