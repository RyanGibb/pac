From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Core Versions Debian.

Create HintDb cmp_debma.
Create Rewrite HintDb cmp_debma.

Module Type ArchParam.
  Declare Module A : FiniteUsualOrderedType.
  Parameter native : A.t.
End ArchParam.

Module DebianMA (N V : UsualOrderedType) (AP : ArchParam).
  Module A := AP.A.

  Inductive NameArch : Type :=
  | QAArch (alpha : A.t)
  | QAExact (alpha : A.t)
  | QAAny
  | QAGroup.

  Module AF := UOTCompareFacts A.
  #[local] Hint Rewrite AF.compare_eq_iff : cmp_debma.
  #[local] Hint Extern 1 => cmp_by AF.compare_antisym : cmp_debma.
  #[local] Hint Extern 1 => cmp_by AF.compare_lt_trans : cmp_debma.

  Module NameArchComp <: ComparableType.
    Definition t := NameArch.
    Definition compare (x y : t) : comparison :=
      match x, y with
      | QAArch a1, QAArch a2 => A.compare a1 a2
      | QAArch _, _ => Lt
      | _, QAArch _ => Gt
      | QAExact a1, QAExact a2 => A.compare a1 a2
      | QAExact _, _ => Lt
      | _, QAExact _ => Gt
      | QAAny, QAAny => Eq
      | QAAny, QAGroup => Lt
      | QAGroup, QAAny => Gt
      | QAGroup, QAGroup => Eq
      end.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_debma. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_debma. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_debma. Qed.
  End NameArchComp.
  Module NameArchOT := UOTFromCompare NameArchComp.

  Module QN := PairUOT N NameArchOT.
  Module NF := UOTCompareFacts N.
  Module MG <: NameGroup QN.
    Definition groupEq (m n : QN.t) : bool :=
      match N.compare (fst m) (fst n) with Eq => true | _ => false end.
    Lemma groupEq_refl : forall n, groupEq n n = true.
    Proof.
      intro n; unfold groupEq.
      assert (H : N.compare (fst n) (fst n) = Eq)
        by (apply NF.compare_eq_iff; reflexivity).
      rewrite H; reflexivity.
    Qed.
    Lemma groupEq_sym : forall m n, groupEq m n = groupEq n m.
    Proof.
      intros m n; unfold groupEq.
      rewrite (NF.compare_antisym (fst n) (fst m)).
      destruct (N.compare (fst n) (fst m)); reflexivity.
    Qed.
    Lemma groupEq_trans : forall m n o,
        groupEq m n = true -> groupEq n o = true -> groupEq m o = true.
    Proof.
      intros m n o H1 H2; unfold groupEq in *.
      destruct (N.compare (fst m) (fst n)) eqn:E1; try discriminate.
      destruct (N.compare (fst n) (fst o)) eqn:E2; try discriminate.
      apply NF.compare_eq_iff in E1; apply NF.compare_eq_iff in E2.
      rewrite E1, E2.
      assert (H : N.compare (fst o) (fst o) = Eq)
        by (apply NF.compare_eq_iff; reflexivity).
      rewrite H; reflexivity.
    Qed.
  End MG.

  Lemma groupEq_iff : forall (m n : N.t) (a a' : NameArch),
      MG.groupEq (m, a) (n, a') = true <-> m = n.
  Proof.
    intros m n a a'; unfold MG.groupEq; cbn [fst].
    destruct (N.compare m n) eqn:E.
    - apply NF.compare_eq_iff in E; split; intro; congruence.
    - split; intro H; [discriminate |].
      apply NF.compare_eq_iff in H; congruence.
    - split; intro H; [discriminate |].
      apply NF.compare_eq_iff in H; congruence.
  Qed.

  Module Deb := Debian QN V MG.

  Module NA := PairUOT N A.
  Module C := Core NA V.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.

  Definition pname (p : Pkg.t) : N.t := fst (fst p).
  Definition parch (p : Pkg.t) : A.t := snd (fst p).
  Definition pver (p : Pkg.t) : V.t := snd p.

  Inductive MAClass : Type :=
  | MANo
  | MASame
  | MAForeign
  | MAAllowed.

  Module MCComp <: ComparableType.
    Definition t := MAClass.
    Definition compare (x y : t) : comparison :=
      match x, y with
      | MANo, MANo => Eq | MANo, _ => Lt | _, MANo => Gt
      | MASame, MASame => Eq | MASame, _ => Lt | _, MASame => Gt
      | MAForeign, MAForeign => Eq | MAForeign, _ => Lt | _, MAForeign => Gt
      | MAAllowed, MAAllowed => Eq
      end.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_debma. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_debma. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_debma. Qed.
  End MCComp.
  Module MCOT := UOTFromCompare MCComp.

  Module ClsElt := PairUOT Pkg MCOT.
  Module Cls := FSetUOT ClsElt.

  Module ClsFibred := FibredRel Pkg MCOT ClsElt Cls.
  Definition classOf (M : Cls.t) (p : Pkg.t) : MAClass :=
    match Cls.min_elt (ClsFibred.tailFibre M p) with
    | Some e => snd e
    | None => MANo
    end.

  Inductive Qual : Type :=
  | QUnq
  | QAny
  | QNative
  | QArch (alpha : A.t).

  Module QualComp <: ComparableType.
    Definition t := Qual.
    Definition compare (x y : t) : comparison :=
      match x, y with
      | QUnq, QUnq => Eq
      | QUnq, _ => Lt
      | _, QUnq => Gt
      | QAny, QAny => Eq
      | QAny, _ => Lt
      | _, QAny => Gt
      | QNative, QNative => Eq
      | QNative, _ => Lt
      | _, QNative => Gt
      | QArch a1, QArch a2 => A.compare a1 a2
      end.
    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_debma. Qed.
    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_debma. Qed.
    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_debma. Qed.
  End QualComp.
  Module QualOT := UOTFromCompare QualComp.

  Module Atom := TripleUOT N QualOT Deb.Ver.FOT.

  Definition aname (a : Atom.t) : N.t := fst a.
  Definition aqual (a : Atom.t) : Qual := fst (snd a).
  Definition aform (a : Atom.t) : Deb.Ver.Formula := snd (snd a).

  Module AtomSet := FSetUOT Atom.
  Module Clause := ListUOT Atom.
  Definition clauseAtoms (Al : Clause.t) : AtomSet.t := AtomSet.ofList Al.

  Lemma mem_clauseAtoms : forall Al a,
      AtomSet.In a (clauseAtoms Al) <-> List.In a Al.
  Proof. intros Al a; apply AtomSet.mem_ofList. Qed.

  Module ClauseElt := PairUOT Pkg Clause.
  Module Deps := FSetUOT ClauseElt.

  Module Provided := PairUOT N Deb.DTOT.
  Module ProvElt := PairUOT Pkg Provided.
  Module Prov := FSetUOT ProvElt.

  Module ConfElt := PairUOT Pkg Atom.
  Module Conf := FSetUOT ConfElt.

  Definition BaseMatch (Pi : Prov.t) (n : N.t) (phi : Deb.Ver.Formula)
      (q : Pkg.t) : Prop :=
    (pname q = n /\ Deb.Ver.satisfiesb (pver q) phi = true) \/
    (exists v, Prov.In (q, (n, v)) Pi /\ Deb.vtMatchb v phi = true).

  Definition MAMatch (Pi : Prov.t) (M : Cls.t) (alpha : A.t)
      (a : Atom.t) (q : Pkg.t) : Prop :=
    BaseMatch Pi (aname a) (aform a) q /\
    match aqual a with
    | QUnq => parch q = alpha \/ classOf M q = MAForeign
    | QNative => parch q = AP.native
    | QArch alpha' => parch q = alpha'
    | QAny => classOf M q = MAAllowed
    end.

  Definition MAConfMatch (Pi : Prov.t) (M : Cls.t)
      (a : Atom.t) (q : Pkg.t) : Prop :=
    BaseMatch Pi (aname a) (aform a) q /\
    match aqual a with
    | QUnq => True
    | QNative => parch q = AP.native
    | QArch alpha' => parch q = alpha'
    | QAny => classOf M q = MAAllowed
    end.

  Record Inst : Type := MkInst
    { inst_repo : PkgSet.t
    ; inst_deps : Deps.t
    ; inst_rec : Deps.t
    ; inst_prov : Prov.t
    ; inst_conf : Conf.t
    ; inst_cls : Cls.t
    ; inst_root : Pkg.t }.

  Record IsResolution (I : Inst) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S (inst_repo I)
    ; res_root_mem : PkgSet.In (inst_root I) S
    ; res_dep_closure :
        forall n alpha v, PkgSet.In ((n, alpha), v) S ->
        forall Al, Deps.In (((n, alpha), v), Al) (inst_deps I) ->
        exists a, List.In a Al /\
          exists q, PkgSet.In q S /\
            MAMatch (inst_prov I) (inst_cls I) alpha a q
    ; res_conflict_avoidance :
        forall n alpha v, PkgSet.In ((n, alpha), v) S ->
        forall a, Conf.In (((n, alpha), v), a) (inst_conf I) ->
        ~ exists m alpha' u, PkgSet.In ((m, alpha'), u) S /\ m <> n /\
            MAConfMatch (inst_prov I) (inst_cls I) a ((m, alpha'), u)
    ; res_lockstep :
        forall n alpha v alpha' u,
        PkgSet.In ((n, alpha), v) S -> PkgSet.In ((n, alpha'), u) S ->
        alpha <> alpha' ->
        classOf (inst_cls I) ((n, alpha), v) = MASame /\
        classOf (inst_cls I) ((n, alpha'), u) = MASame /\ v = u
    ; res_version_unique : C.VersionUnique S }.

  Module Reduction.
    Definition embedPkg (p : Pkg.t) : Deb.Ver.C.Pkg.t :=
      ((pname p, QAArch (parch p)), pver p).

    Module SOmr := SetOps Pkg Deb.Ver.C.Pkg PkgSet Deb.Ver.C.PkgSet.
    Definition reduceReal (R : PkgSet.t) : Deb.Ver.C.PkgSet.t :=
      SOmr.map embedPkg R.

    Definition reduceAtom (alpha : A.t) (a : Atom.t) : Deb.Atom.t :=
      ((aname a,
        match aqual a with
        | QUnq => QAArch alpha
        | QNative => QAExact AP.native
        | QArch alpha' => QAExact alpha'
        | QAny => QAAny
        end), aform a).

    Definition reduceClause (alpha : A.t) (Al : Clause.t) : Deb.Clause.t :=
      List.map (reduceAtom alpha) Al.

    Lemma mem_reduceClause : forall alpha Al a',
        Deb.AtomSet.In a' (Deb.clauseAtoms (reduceClause alpha Al)) <->
        exists a, List.In a Al /\ a' = reduceAtom alpha a.
    Proof.
      intros alpha Al a'; rewrite Deb.mem_clauseAtoms; unfold reduceClause.
      rewrite List.in_map_iff; split; intros [a [Ha He]]; exists a; auto.
    Qed.

    Module SOdp := SetOps ClauseElt Deb.ClauseElt Deps Deb.Deps.
    Definition reduceDeps (D : Deps.t) : Deb.Deps.t :=
      SOdp.map (fun c =>
          (embedPkg (fst c), reduceClause (parch (fst c)) (snd c)))
        D.

    Definition reduceRec (Dopt : Deps.t) : Deb.Deps.t := reduceDeps Dopt.

    Definition reduceProvEntry (M : Cls.t) (e : ProvElt.t) :
        list Deb.ProvElt.t :=
      let p := fst e in
      let m := fst (snd e) in
      let v := snd (snd e) in
      (embedPkg p, ((m, QAExact (parch p)), v))
        :: match classOf M p with
           | MAForeign =>
               List.map (fun b => (embedPkg p, ((m, QAArch b), v))) A.enum
           | MAAllowed =>
               (embedPkg p, ((m, QAAny), v))
                 :: (embedPkg p, ((m, QAArch (parch p)), v)) :: nil
           | _ => (embedPkg p, ((m, QAArch (parch p)), v)) :: nil
           end.

    Definition implProvOf (M : Cls.t) (p : Pkg.t) : list Deb.ProvElt.t :=
      (embedPkg p, ((pname p, QAGroup), Deb.DTVal (pver p)))
        :: (embedPkg p, ((pname p, QAExact (parch p)), Deb.DTVal (pver p)))
        :: match classOf M p with
           | MAForeign =>
               List.map
                 (fun b =>
                    (embedPkg p, ((pname p, QAArch b), Deb.DTVal (pver p))))
                 A.enum
           | MAAllowed =>
               (embedPkg p, ((pname p, QAAny), Deb.DTVal (pver p))) :: nil
           | _ => nil
           end.

    Module SOpv2 := SetOps ProvElt Deb.ProvElt Prov Deb.Prov.
    Module SOppv := SetOps Deb.ProvElt Deb.ProvElt Deb.Prov Deb.Prov.
    Module SOrpv := SetOps Pkg Deb.ProvElt PkgSet Deb.Prov.
    Definition reduceProv (R : PkgSet.t) (Pi : Prov.t) (M : Cls.t) :
        Deb.Prov.t :=
      Deb.Prov.union
        (SOpv2.unionMap (fun e => SOppv.ofList (reduceProvEntry M e)) Pi)
        (SOrpv.unionMap (fun p => SOppv.ofList (implProvOf M p)) R).

    Definition reduceConfEntry (e : ConfElt.t) : list Deb.ConfElt.t :=
      let p := fst e in
      let a := snd e in
      let n := aname a in
      let phi := aform a in
      match aqual a with
      | QUnq =>
          (embedPkg p, (((n, QAGroup), phi), true))
            :: (embedPkg p, (((n, QAAny), phi), true))
            :: List.map
              (fun b => (embedPkg p, (((n, QAArch b), phi), true))) A.enum
      | QNative => (embedPkg p, (((n, QAExact AP.native), phi), true)) :: nil
      | QArch b => (embedPkg p, (((n, QAExact b), phi), true)) :: nil
      | QAny => (embedPkg p, (((n, QAAny), phi), true)) :: nil
      end.

    Definition implConfOf (M : Cls.t) (p : Pkg.t) : Deb.ConfElt.t :=
      match classOf M p with
      | MASame =>
          (embedPkg p,
             (((pname p, QAGroup), Deb.Ver.FCmp OpNe (pver p)), false))
      | _ =>
          (embedPkg p, (((pname p, QAGroup), Deb.Ver.FTop), false))
      end.

    Module SOcf := SetOps ConfElt Deb.ConfElt Conf Deb.Conf.
    Module SOccf := SetOps Deb.ConfElt Deb.ConfElt Deb.Conf Deb.Conf.
    Module SOrcf := SetOps Pkg Deb.ConfElt PkgSet Deb.Conf.
    Definition reduceConf (R : PkgSet.t) (G : Conf.t) (M : Cls.t) :
        Deb.Conf.t :=
      Deb.Conf.union
        (SOcf.unionMap (fun e => SOccf.ofList (reduceConfEntry e)) G)
        (SOrcf.map (implConfOf M) R).

    Definition reduceInst (I : Inst) : Deb.Inst :=
      Deb.MkInst (reduceReal (inst_repo I)) (reduceDeps (inst_deps I))
        (reduceRec (inst_rec I))
        (reduceProv (inst_repo I) (inst_prov I) (inst_cls I))
        (reduceConf (inst_repo I) (inst_conf I) (inst_cls I))
        (embedPkg (inst_root I)).

    Definition tryInvPkg (p : Deb.Ver.C.Pkg.t) : option Pkg.t :=
      match p with
      | ((n, QAArch b), v) => Some ((n, b), v)
      | _ => None
      end.

    Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
    Proof.
      intros [[n b] v]; unfold tryInvPkg, embedPkg, pname, parch, pver;
        cbn [fst snd]; reflexivity.
    Qed.

    Lemma tryInvPkg_some : forall (q : Deb.Ver.C.Pkg.t) (p : Pkg.t),
        tryInvPkg q = Some p -> embedPkg p = q.
    Proof.
      intros [[n [b | b | |]] v] p H; cbn [tryInvPkg] in H; try discriminate.
      injection H as <-; unfold embedPkg, pname, parch, pver;
        cbn [fst snd]; reflexivity.
    Qed.

    Module SOpre := SetOps Deb.Ver.C.Pkg Pkg Deb.Ver.C.PkgSet PkgSet.
    Definition debianMAResolution (S : Deb.Ver.C.PkgSet.t) : PkgSet.t :=
      SOpre.filterMap tryInvPkg S.

    Lemma embedPkg_injective : forall p q, embedPkg p = embedPkg q -> p = q.
    Proof. exact (SOpre.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

    Lemma mem_debianMAResolution : forall S q,
        PkgSet.In q (debianMAResolution S) <->
          Deb.Ver.C.PkgSet.In (embedPkg q) S.
    Proof.
      unfold debianMAResolution.
      exact (SOpre.mem_filterMap_inv tryInvPkg embedPkg tryInvPkg_embed
               tryInvPkg_some).
    Qed.

    Lemma mem_reduceDeps : forall D y,
        Deb.Deps.In y (reduceDeps D) <->
        exists p Al, Deps.In (p, Al) D /\
          y = (embedPkg p, reduceClause (parch p) Al).
    Proof.
      intros D y; unfold reduceDeps; rewrite SOdp.mem_map.
      split.
      - intros [[p Al] [Hc Hy]]; cbn [fst snd] in Hy.
        exists p, Al; split; assumption.
      - intros [p [Al [Hc ->]]]; exists (p, Al); split;
        [exact Hc | reflexivity].
    Qed.

    Lemma mem_reduceProv : forall R Pi M y,
        Deb.Prov.In y (reduceProv R Pi M) <->
        (exists e, Prov.In e Pi /\ List.In y (reduceProvEntry M e)) \/
        (exists p, PkgSet.In p R /\ List.In y (implProvOf M p)).
    Proof.
      intros R Pi M y; unfold reduceProv.
      rewrite Deb.Prov.union_spec, SOpv2.mem_unionMap, SOrpv.mem_unionMap.
      cbn beta; setoid_rewrite SOppv.mem_ofList; reflexivity.
    Qed.

    Lemma mem_reduceConf : forall R G M y,
        Deb.Conf.In y (reduceConf R G M) <->
        (exists e, Conf.In e G /\ List.In y (reduceConfEntry e)) \/
        (exists p, PkgSet.In p R /\ y = implConfOf M p).
    Proof.
      intros R G M y; unfold reduceConf.
      rewrite Deb.Conf.union_spec, SOcf.mem_unionMap, SOrcf.mem_map.
      cbn beta; setoid_rewrite SOccf.mem_ofList; reflexivity.
    Qed.

    Lemma provElt_eq : forall (p p' : Pkg.t) (m m' : N.t) (x x' : NameArch)
        (v v' : Deb.DTop),
        (embedPkg p, ((m, x), v)) = (embedPkg p', ((m', x'), v')) ->
        p = p' /\ m = m' /\ x = x' /\ v = v'.
    Proof.
      intros p p' m m' x x' v v' H.
      pose proof (f_equal fst H) as Hp; cbn [fst] in Hp.
      pose proof (f_equal (fun y => fst (fst (snd y))) H) as Hm.
      pose proof (f_equal (fun y => snd (fst (snd y))) H) as Hx.
      pose proof (f_equal (fun y => snd (snd y)) H) as Hv.
      cbn [fst snd] in Hm, Hx, Hv.
      exact (conj (embedPkg_injective _ _ Hp) (conj Hm (conj Hx Hv))).
    Qed.

    Lemma in_reduceProvEntry : forall M (p : Pkg.t) (m : N.t) v y,
        List.In y (reduceProvEntry M (p, (m, v))) <->
        exists x, y = (embedPkg p, ((m, x), v)) /\
          match x with
          | QAArch b => parch p = b \/ classOf M p = MAForeign
          | QAExact b => parch p = b
          | QAAny => classOf M p = MAAllowed
          | QAGroup => False
          end.
    Proof.
      intros M p m v y; unfold reduceProvEntry; cbn [fst snd].
      split.
      - intros [<- | H].
        + exists (QAExact (parch p)); split; reflexivity.
        + destruct (classOf M p) eqn:Hc.
          * destruct H as [<- | []].
            exists (QAArch (parch p)); split; [reflexivity | left; reflexivity].
          * destruct H as [<- | []].
            exists (QAArch (parch p)); split; [reflexivity | left; reflexivity].
          * apply in_map_iff in H; destruct H as [b [<- _]].
            exists (QAArch b); split; [reflexivity | right; reflexivity].
          * destruct H as [<- | [<- | []]].
            -- exists QAAny; split; [reflexivity | reflexivity].
            -- exists (QAArch (parch p)); split;
                 [reflexivity | left; reflexivity].
      - intros [x [-> Hx]].
        destruct x as [b | b | |].
        + right.
          destruct (classOf M p) eqn:Hc.
          * destruct Hx as [<- | Hf]; [left; reflexivity | congruence].
          * destruct Hx as [<- | Hf]; [left; reflexivity | congruence].
          * apply in_map_iff; exists b; split;
              [reflexivity | apply A.enum_complete].
          * destruct Hx as [<- | Hf]; [right; left; reflexivity | congruence].
        + left; rewrite Hx; reflexivity.
        + right; rewrite Hx; left; reflexivity.
        + contradiction.
    Qed.

    Lemma in_implProvOf : forall M (p : Pkg.t) y,
        List.In y (implProvOf M p) <->
        exists x, y = (embedPkg p, ((pname p, x), Deb.DTVal (pver p))) /\
          match x with
          | QAArch _ => classOf M p = MAForeign
          | QAExact b => parch p = b
          | QAAny => classOf M p = MAAllowed
          | QAGroup => True
          end.
    Proof.
      intros M p y; unfold implProvOf.
      split.
      - intros [<- | [<- | H]].
        + exists QAGroup; split; [reflexivity | exact I].
        + exists (QAExact (parch p)); split; reflexivity.
        + destruct (classOf M p) eqn:Hc; cbn [List.In] in H; try contradiction.
          * apply in_map_iff in H; destruct H as [b [<- _]].
            exists (QAArch b); split; [reflexivity | reflexivity].
          * destruct H as [<- | []].
            exists QAAny; split; [reflexivity | reflexivity].
      - intros [x [-> Hx]].
        destruct x as [b | b | |].
        + right; right; rewrite Hx.
          apply in_map_iff; exists b; split;
            [reflexivity | apply A.enum_complete].
        + right; left; rewrite Hx; reflexivity.
        + right; right; rewrite Hx; left; reflexivity.
        + left; reflexivity.
    Qed.

    Lemma debMatch_char : forall R Pi M q n x phi,
        PkgSet.In q R ->
        (Deb.Match (reduceProv R Pi M) (embedPkg q) ((n, x), phi) <->
         match x with
         | QAArch b =>
             BaseMatch Pi n phi q /\ (parch q = b \/ classOf M q = MAForeign)
         | QAExact b => BaseMatch Pi n phi q /\ parch q = b
         | QAAny => BaseMatch Pi n phi q /\ classOf M q = MAAllowed
         | QAGroup => pname q = n /\ Deb.Ver.satisfiesb (pver q) phi = true
         end).
    Proof.
      intros R Pi M q n x phi HqR.
      unfold Deb.Match; cbn [Deb.aname Deb.aform fst snd].
      split.
      - intros [[He Hv] | [v [Hin Hvt]]].
        + unfold embedPkg in He, Hv; cbn [fst snd] in He, Hv.
          injection He as <- <-.
          split; [left; split; [reflexivity | exact Hv] | left; reflexivity].
        + rewrite mem_reduceProv in Hin.
          destruct Hin as [[[p0 [m0 v0]] [HePi Hl]] | [p0 [Hp0 Hl]]].
          * apply in_reduceProvEntry in Hl; destruct Hl as [x' [Heq Hx']].
            destruct (provElt_eq _ _ _ _ _ _ _ _ Heq) as [<- [<- [<- <-]]].
            destruct x as [b | b | |];
              try (split; [right; exists v; split; assumption | exact Hx']);
              contradiction.
          * apply in_implProvOf in Hl; destruct Hl as [x' [Heq Hx']].
            destruct (provElt_eq _ _ _ _ _ _ _ _ Heq) as [<- [-> [<- ->]]].
            destruct x as [b | b | |];
              [ split;
                [left; split; [reflexivity | exact Hvt] | right; exact Hx']
              | split; [left; split; [reflexivity | exact Hvt] | exact Hx']
              | split; [left; split; [reflexivity | exact Hvt] | exact Hx']
              | split; [reflexivity | exact Hvt] ].
      - destruct x as [b | b | |].
        + intros [HB Harch].
          destruct HB as [[Hn Hv] | [v [HPi Hvt]]].
          * destruct Harch as [Hb | Hf].
            -- subst n b; left; split; [reflexivity | exact Hv].
            -- subst n; right; exists (Deb.DTVal (pver q)); split; [| exact Hv].
               rewrite mem_reduceProv; right; exists q; split; [exact HqR |].
               apply in_implProvOf; exists (QAArch b); split;
                 [reflexivity | exact Hf].
          * right; exists v; split; [| exact Hvt].
            rewrite mem_reduceProv; left; exists (q, (n, v)); split;
              [exact HPi |].
            apply in_reduceProvEntry; exists (QAArch b); split;
              [reflexivity | exact Harch].
        + intros [HB Hb]; subst b.
          destruct HB as [[Hn Hv] | [v [HPi Hvt]]].
          * subst n; right; exists (Deb.DTVal (pver q)); split; [| exact Hv].
            rewrite mem_reduceProv; right; exists q; split; [exact HqR |].
            apply in_implProvOf; exists (QAExact (parch q)); split; reflexivity.
          * right; exists v; split; [| exact Hvt].
            rewrite mem_reduceProv; left; exists (q, (n, v)); split;
              [exact HPi |].
            apply in_reduceProvEntry; exists (QAExact (parch q)); split;
              reflexivity.
        + intros [HB Hall].
          destruct HB as [[Hn Hv] | [v [HPi Hvt]]].
          * subst n; right; exists (Deb.DTVal (pver q)); split; [| exact Hv].
            rewrite mem_reduceProv; right; exists q; split; [exact HqR |].
            apply in_implProvOf; exists QAAny; split;
              [reflexivity | exact Hall].
          * right; exists v; split; [| exact Hvt].
            rewrite mem_reduceProv; left; exists (q, (n, v)); split;
              [exact HPi |].
            apply in_reduceProvEntry; exists QAAny; split;
              [reflexivity | exact Hall].
        + intros [Hn Hv]; subst n.
          right; exists (Deb.DTVal (pver q)); split; [| exact Hv].
          rewrite mem_reduceProv; right; exists q; split; [exact HqR |].
          apply in_implProvOf; exists QAGroup; split; [reflexivity | exact I].
    Qed.

    Lemma match_transfer : forall R Pi M alpha a q,
        PkgSet.In q R ->
        (MAMatch Pi M alpha a q <->
         Deb.Match (reduceProv R Pi M) (embedPkg q) (reduceAtom alpha a)).
    Proof.
      intros R Pi M alpha a q HqR.
      unfold MAMatch, reduceAtom.
      destruct (aqual a) as [ | | | b].
      - exact (iff_sym
          (debMatch_char R Pi M q (aname a) (QAArch alpha) (aform a) HqR)).
      - exact (iff_sym
          (debMatch_char R Pi M q (aname a) QAAny (aform a) HqR)).
      - exact (iff_sym
          (debMatch_char R Pi M q (aname a) (QAExact AP.native) (aform a)
             HqR)).
      - exact (iff_sym
          (debMatch_char R Pi M q (aname a) (QAExact b) (aform a) HqR)).
    Qed.

    Lemma conf_transfer : forall R Pi M (p : Pkg.t) a q,
        PkgSet.In q R ->
        ((exists q' ea e, List.In (q', (ea, e)) (reduceConfEntry (p, a)) /\
            Deb.Match (reduceProv R Pi M) (embedPkg q) ea) <->
         MAConfMatch Pi M a q).
    Proof.
      intros R Pi M p a q HqR.
      unfold MAConfMatch, reduceConfEntry; cbn [fst snd].
      destruct (aqual a) as [ | | | b].
      - split.
        + intros [q' [ea [e [Hce HM]]]].
          split; [| exact I].
          destruct Hce as [E | [E | Hce]].
          * injection E as _ <- _.
            destruct (proj1 (debMatch_char R Pi M q (aname a) QAGroup
                               (aform a) HqR) HM) as [Hn Hv].
            left; split; assumption.
          * injection E as _ <- _.
            exact (proj1 (proj1 (debMatch_char R Pi M q (aname a) QAAny
                                   (aform a) HqR) HM)).
          * apply in_map_iff in Hce; destruct Hce as [b [E Hb]].
            injection E as _ <- _.
            exact (proj1 (proj1 (debMatch_char R Pi M q (aname a) (QAArch b)
                                   (aform a) HqR) HM)).
        + intros [HB _].
          destruct HB as [[Hn Hv] | [v [HPi Hvt]]].
          * exists (embedPkg p), ((aname a, QAGroup), aform a), true.
            split; [left; reflexivity |].
            apply (proj2 (debMatch_char R Pi M q (aname a) QAGroup
                            (aform a) HqR)).
            split; assumption.
          * exists (embedPkg p), ((aname a, QAArch (parch q)), aform a), true.
            split.
            -- right; right; apply in_map_iff.
               exists (parch q); split; [reflexivity | apply A.enum_complete].
            -- apply (proj2 (debMatch_char R Pi M q (aname a)
                               (QAArch (parch q)) (aform a) HqR)).
               split; [right; exists v; split; assumption | left; reflexivity].
      - split.
        + intros [q' [ea [e [Hce HM]]]].
          destruct Hce as [E | []].
          injection E as _ <- _.
          exact (proj1 (debMatch_char R Pi M q (aname a) QAAny (aform a)
                          HqR) HM).
        + intros H.
          exists (embedPkg p), ((aname a, QAAny), aform a), true.
          split; [left; reflexivity |].
          exact (proj2 (debMatch_char R Pi M q (aname a) QAAny (aform a)
                          HqR) H).
      - split.
        + intros [q' [ea [e [Hce HM]]]].
          destruct Hce as [E | []].
          injection E as _ <- _.
          exact (proj1 (debMatch_char R Pi M q (aname a) (QAExact AP.native)
                          (aform a) HqR) HM).
        + intros H.
          exists (embedPkg p), ((aname a, QAExact AP.native), aform a), true.
          split; [left; reflexivity |].
          exact (proj2 (debMatch_char R Pi M q (aname a) (QAExact AP.native)
                          (aform a) HqR) H).
      - split.
        + intros [q' [ea [e [Hce HM]]]].
          destruct Hce as [E | []].
          injection E as _ <- _.
          exact (proj1 (debMatch_char R Pi M q (aname a) (QAExact b)
                          (aform a) HqR) HM).
        + intros H.
          exists (embedPkg p), ((aname a, QAExact b), aform a), true.
          split; [left; reflexivity |].
          exact (proj2 (debMatch_char R Pi M q (aname a) (QAExact b)
                          (aform a) HqR) H).
    Qed.

    Lemma impl_conf_transfer : forall R Pi M (p q : Pkg.t),
        PkgSet.In q R ->
        (Deb.Match (reduceProv R Pi M) (embedPkg q)
           (fst (snd (implConfOf M p))) <->
         (pname q = pname p /\
          match classOf M p with
          | MASame => pver q <> pver p
          | _ => True
          end)).
    Proof.
      pose proof Deb.Ver.cmpOpEval_ne_iff as Hne.
      intros R Pi M p q HqR.
      unfold implConfOf.
      destruct (classOf M p) eqn:Hcls; cbn [fst snd].
      - split.
        + intro HM.
          destruct (proj1 (debMatch_char R Pi M q (pname p) QAGroup
                             Deb.Ver.FTop HqR) HM) as [Hn _].
          split; [exact Hn | exact I].
        + intros [Hn _].
          apply (proj2 (debMatch_char R Pi M q (pname p) QAGroup
                          Deb.Ver.FTop HqR)).
          split; [exact Hn | reflexivity].
      - split.
        + intro HM.
          destruct (proj1 (debMatch_char R Pi M q (pname p) QAGroup
                             (Deb.Ver.FCmp OpNe (pver p)) HqR) HM) as [Hn Hv].
          split; [exact Hn | exact (proj1 (Hne _ _) Hv)].
        + intros [Hn Hv].
          apply (proj2 (debMatch_char R Pi M q (pname p) QAGroup
                          (Deb.Ver.FCmp OpNe (pver p)) HqR)).
          split; [exact Hn | exact (proj2 (Hne _ _) Hv)].
      - split.
        + intro HM.
          destruct (proj1 (debMatch_char R Pi M q (pname p) QAGroup
                             Deb.Ver.FTop HqR) HM) as [Hn _].
          split; [exact Hn | exact I].
        + intros [Hn _].
          apply (proj2 (debMatch_char R Pi M q (pname p) QAGroup
                          Deb.Ver.FTop HqR)).
          split; [exact Hn | reflexivity].
      - split.
        + intro HM.
          destruct (proj1 (debMatch_char R Pi M q (pname p) QAGroup
                             Deb.Ver.FTop HqR) HM) as [Hn _].
          split; [exact Hn | exact I].
        + intros [Hn _].
          apply (proj2 (debMatch_char R Pi M q (pname p) QAGroup
                          Deb.Ver.FTop HqR)).
          split; [exact Hn | reflexivity].
    Qed.

    Lemma reduceConfEntry_pkg : forall p a q ea e,
        List.In (q, (ea, e)) (reduceConfEntry (p, a)) -> q = embedPkg p.
    Proof.
      intros p a q ea e H; unfold reduceConfEntry in H; cbn [fst snd] in H.
      destruct (aqual a) as [ | | | b]; simpl in H;
        repeat (destruct H as [E | H]; [congruence |]);
        try contradiction.
      apply in_map_iff in H; destruct H as [b' [E _]]; congruence.
    Qed.

    Lemma reduceConfEntry_flag : forall p a q ea e,
        List.In (q, (ea, e)) (reduceConfEntry (p, a)) -> e = true.
    Proof.
      intros p a q ea e H; unfold reduceConfEntry in H; cbn [fst snd] in H.
      destruct (aqual a) as [ | | | b]; simpl in H;
        repeat (destruct H as [E | H]; [congruence |]);
        try contradiction.
      apply in_map_iff in H; destruct H as [b' [E _]]; congruence.
    Qed.

    Lemma reduceConfEntry_name : forall (p : Pkg.t) (a : Atom.t)
        (q : Deb.Ver.C.Pkg.t) (ea : Deb.Atom.t) (e : bool),
        List.In (q, (ea, e)) (reduceConfEntry (p, a)) ->
        fst (fst ea) = aname a.
    Proof.
      intros p a q ea e H; unfold reduceConfEntry in H; cbn [fst snd] in H.
      destruct (aqual a) as [ | | | b]; simpl in H;
        repeat (destruct H as [E | H];
                [injection E as _ E2 _; rewrite <- E2; reflexivity |]);
        try contradiction.
      apply in_map_iff in H; destruct H as [b' [E _]].
      injection E as _ E2 _; rewrite <- E2; reflexivity.
    Qed.

    Lemma implConfOf_atomName : forall M (p : Pkg.t),
        fst (fst (snd (implConfOf M p))) = (pname p, QAGroup).
    Proof.
      intros M p; unfold implConfOf; destruct (classOf M p); reflexivity.
    Qed.

    Lemma implConfOf_pkg : forall M p,
        implConfOf M p = (embedPkg p, snd (implConfOf M p)).
    Proof.
      intros M p; unfold implConfOf; destruct (classOf M p); reflexivity.
    Qed.

    Lemma implConfOf_flag : forall M p,
        implConfOf M p = (embedPkg p, (fst (snd (implConfOf M p)), false)).
    Proof.
      intros M p; unfold implConfOf; destruct (classOf M p); reflexivity.
    Qed.

    Theorem debian_ma_soundness : forall I S,
        Deb.IsResolution (reduceInst I) S ->
        IsResolution I (debianMAResolution S).
    Proof.
      intros [R D Dopt Pi G M r] S HT.
      destruct HT as [Hsub Hroot Hcc Hca Hvu].
      cbn [reduceInst Deb.inst_repo Deb.inst_deps Deb.inst_prov Deb.inst_conf
           Deb.inst_root inst_repo inst_deps inst_prov inst_conf inst_cls
           inst_root] in Hsub, Hroot, Hcc, Hca.
      assert (HinR : forall q,
                 PkgSet.In q (debianMAResolution S) -> PkgSet.In q R).
      { intros q Hq.
        rewrite mem_debianMAResolution in Hq.
        apply Hsub in Hq; unfold reduceReal in Hq.
        exact (proj1 (SOmr.mem_map_inj _ _ _ embedPkg_injective) Hq). }
      constructor; cbn [inst_repo inst_deps inst_conf inst_prov inst_cls
                        inst_root].
      - exact HinR.
      - rewrite mem_debianMAResolution; exact Hroot.
      - intros n alpha v HpS Al HAl; set (p := ((n, alpha), v)) in *.
        pose proof HpS as HpT; rewrite mem_debianMAResolution in HpT.
        assert (Hd : Deb.Deps.In (embedPkg p, reduceClause (parch p) Al)
                       (reduceDeps D)).
        { rewrite mem_reduceDeps; exists p, Al; split;
            [exact HAl | reflexivity]. }
        destruct (Hcc (embedPkg p) HpT _ Hd) as [ea [Ha [qh [HqhS HqhM]]]].
        unfold reduceClause in Ha; apply List.in_map_iff in Ha;
          destruct Ha as [a [Hae Hat]]; subst ea.
        pose proof (Hsub _ HqhS) as HqhR.
        unfold reduceReal in *; rewrite SOmr.mem_map in HqhR; destruct HqhR as [q [HqR Hqe]]; subst qh.
        exists a; split; [exact Hat |].
        exists q; split.
        + rewrite mem_debianMAResolution; exact HqhS.
        + exact (proj2 (match_transfer R Pi M (parch p) a q HqR) HqhM).
      - intros n alpha v HpS a HG [m [alpha' [u [HqS [Hqp HCM]]]]].
        set (p := ((n, alpha), v)) in *; set (q := ((m, alpha'), u)) in *.
        pose proof HpS as HpT; rewrite mem_debianMAResolution in HpT.
        pose proof (HinR q HqS) as HqR.
        destruct (proj2 (conf_transfer R Pi M p a q HqR) HCM)
          as [c1 [c2 [c3 [Hce HM]]]].
        pose proof (reduceConfEntry_pkg p a c1 c2 c3 Hce) as Hf; subst c1.
        pose proof (reduceConfEntry_flag p a (embedPkg p) c2 c3 Hce) as Hx;
          subst c3.
        assert (HceG : Deb.Conf.In (embedPkg p, (c2, true)) (reduceConf R G M)).
        { rewrite mem_reduceConf; left; exists (p, a); split;
            [exact HG | exact Hce]. }
        apply (Hca (pname p, QAArch (parch p)) (pver p) HpT c2 true HceG).
        exists (pname q, QAArch (parch q)), (pver q); split;
          [ rewrite mem_debianMAResolution in HqS; exact HqS
          | split;
            [ intro E; apply Hqp; injection E; intros; assumption
            | split;
              [ intros _; apply Bool.not_true_is_false; intro Eg;
                apply Hqp;
                exact (proj1 (groupEq_iff (pname q) (pname p)
                                (QAArch (parch q)) (QAArch (parch p))) Eg)
              | exact HM ] ] ].
      - intros n alpha v alpha' u HpS HqS Harch.
        set (p := ((n, alpha), v)) in *; set (q := ((n, alpha'), u)) in *.
        assert (Hname : pname p = pname q) by reflexivity.
        pose proof (HinR p HpS) as HpR; pose proof (HinR q HqS) as HqR.
        pose proof HpS as HpT; rewrite mem_debianMAResolution in HpT.
        pose proof HqS as HqT; rewrite mem_debianMAResolution in HqT.
        assert (Hpq : embedPkg q <> embedPkg p).
        { intro E; apply Harch; unfold embedPkg, p, q in E; cbn in E;
            injection E; intros; congruence. }
        assert (HinCp : Deb.Conf.In
                          (embedPkg p, (fst (snd (implConfOf M p)), false))
                          (reduceConf R G M)).
        { rewrite mem_reduceConf; right; exists p; split;
            [exact HpR | symmetry; apply implConfOf_flag]. }
        assert (HinCq : Deb.Conf.In
                          (embedPkg q, (fst (snd (implConfOf M q)), false))
                          (reduceConf R G M)).
        { rewrite mem_reduceConf; right; exists q; split;
            [exact HqR | symmetry; apply implConfOf_flag]. }
        assert (HclsP : classOf M p = MASame).
        { destruct (classOf M p) eqn:Hc; try reflexivity; exfalso;
            apply (Hca (pname p, QAArch (parch p)) (pver p) HpT _ _ HinCp);
            exists (pname q, QAArch (parch q)), (pver q);
            (split;
             [ exact HqT
             | split;
               [ exact Hpq
               | split;
                 [ intro Hx; discriminate Hx
                 | apply (proj2 (impl_conf_transfer R Pi M p q HqR));
                   rewrite Hc; split;
                     [symmetry; exact Hname | exact I] ] ] ]). }
        assert (HclsQ : classOf M q = MASame).
        { destruct (classOf M q) eqn:Hc; try reflexivity; exfalso;
            apply (Hca (pname q, QAArch (parch q)) (pver q) HqT _ _ HinCq);
            exists (pname p, QAArch (parch p)), (pver p);
            (split;
             [ exact HpT
             | split;
               [ intro E; apply Hpq; symmetry; exact E
               | split;
                 [ intro Hx; discriminate Hx
                 | apply (proj2 (impl_conf_transfer R Pi M q p HpR));
                   rewrite Hc; split; [exact Hname | exact I] ] ] ]). }
        destruct (V.eq_dec (pver p) (pver q)) as [Hv | Hv].
        + split; [exact HclsP | split; [exact HclsQ | exact Hv]].
        + exfalso.
          apply (Hca (pname p, QAArch (parch p)) (pver p) HpT _ _ HinCp).
          exists (pname q, QAArch (parch q)), (pver q); split;
            [ exact HqT
            | split;
              [ exact Hpq
              | split;
                [ intro Hx; discriminate Hx
                | apply (proj2 (impl_conf_transfer R Pi M p q HqR));
                  rewrite HclsP; split;
                  [ symmetry; exact Hname
                  | intro E; apply Hv; symmetry; exact E ] ] ] ].
      - intros n v v' Hv Hv'.
        rewrite mem_debianMAResolution in Hv, Hv'.
        destruct n as [m ar].
        exact (Hvu (m, QAArch ar) v v' Hv Hv').
    Qed.

    Definition coreResolution (S : PkgSet.t) : Deb.Ver.C.PkgSet.t :=
      reduceReal S.

    Theorem debian_ma_completeness : forall I S,
        IsResolution I S ->
        Deb.IsResolution (reduceInst I) (coreResolution S).
    Proof.
      unfold coreResolution.
      intros [R D Dopt Pi G M r] S HS.
      destruct HS as [HSsub HSroot HScc HSca HSci HSvu].
      cbn [inst_repo inst_deps inst_prov inst_conf inst_cls inst_root]
        in HSsub, HSroot, HScc, HSca, HSci.
      constructor;
        cbn [reduceInst Deb.inst_repo Deb.inst_deps Deb.inst_prov Deb.inst_conf
             Deb.inst_root inst_repo inst_deps inst_prov inst_conf inst_cls
             inst_root].
      - exact (SOmr.map_mono _ _ _ _ HSsub (fun _ => eq_refl)).
      - unfold reduceReal; apply (SOmr.mem_map_inj _ _ _ embedPkg_injective).
        exact HSroot.
      - intros ph HphT A HA.
        unfold reduceReal in *; rewrite SOmr.mem_map in HphT; destruct HphT as [p [HpS Hpe]]; subst ph.
        rewrite mem_reduceDeps in HA.
        destruct HA as [p0 [Al [HD Heq]]].
        pose proof (f_equal fst Heq) as Hp2;
          pose proof (f_equal snd Heq) as HA2;
          cbn [fst snd] in Hp2, HA2.
        apply embedPkg_injective in Hp2; subst p0 A.
        destruct p as [[pn pa] pv]; set (p := ((pn, pa), pv)) in *.
        destruct (HScc pn pa pv HpS Al HD) as [a [Hat [q [HqS HqM]]]].
        exists (reduceAtom (parch p) a); split.
        { apply List.in_map; exact Hat. }
        exists (embedPkg q); split.
        { unfold reduceReal; apply (SOmr.mem_map_inj _ _ _ embedPkg_injective).
          exact HqS. }
        exact (proj1 (match_transfer R Pi M (parch p) a q (HSsub q HqS)) HqM).
      - intros phn phv HphT ea x HaG [qhn [qhv [HqhT [Hne [Hex HM]]]]].
        unfold reduceReal in *; rewrite SOmr.mem_map in HphT; destruct HphT as [p1 [Hp1S Hp1e]].
        unfold reduceReal in *; rewrite SOmr.mem_map in HqhT; destruct HqhT as [q [HqS Hqe]].
        injection Hqe as -> ->.
        set (ph := (phn, phv)) in *.
        change ((pname q, QAArch (parch q), pver q) <> ph) in Hne.
        change (Deb.Match (reduceProv R Pi M) (embedPkg q) ea) in HM.
        change (x = true -> MG.groupEq (fst (embedPkg q)) (fst ph) = false)
          in Hex.
        clearbody ph.
        rewrite mem_reduceConf in HaG.
        destruct HaG as [[e [HG Hce]] | [p0 [Hp0R Heq]]].
        + destruct e as [p0 a].
          pose proof (reduceConfEntry_pkg p0 a ph ea x Hce) as Hf.
          rewrite Hp1e in Hf; apply embedPkg_injective in Hf; subst p1.
          subst ph.
          pose proof (reduceConfEntry_flag p0 a (embedPkg p0) ea x Hce) as Hx;
            subst x.
          assert (Hnp : pname q <> pname p0).
          { intro En.
            specialize (Hex eq_refl).
            unfold embedPkg in Hex; cbn [fst] in Hex.
            rewrite (proj2 (groupEq_iff (pname q) (pname p0)
                              (QAArch (parch q)) (QAArch (parch p0))) En)
              in Hex.
            discriminate. }
          destruct p0 as [[pn pa] pv]; set (p0 := ((pn, pa), pv)) in *.
          apply (HSca pn pa pv Hp1S a HG).
          destruct q as [[qn qa] qv]; set (q := ((qn, qa), qv)) in *.
          exists qn, qa, qv; split;
            [ exact HqS
            | split;
              [ exact Hnp
              | apply (proj1 (conf_transfer R Pi M p0 a q (HSsub q HqS)));
                exists (embedPkg p0), ea, true; split;
                [exact Hce | exact HM] ] ].
        + rewrite implConfOf_pkg in Heq.
          pose proof (f_equal fst Heq) as Hf;
            pose proof (f_equal snd Heq) as Hs;
            cbn [fst snd] in Hf, Hs.
          rewrite Hp1e in Hf; apply embedPkg_injective in Hf; subst p1.
          subst ph.
          pose proof (f_equal fst Hs) as Ha; cbn [fst] in Ha; subst ea.
          pose proof (HSsub q HqS) as HqR.
          destruct (proj1 (impl_conf_transfer R Pi M p0 q HqR) HM)
            as [Hnm Hcm].
          assert (Hqp : q <> p0).
          { intro E; apply Hne; rewrite E; reflexivity. }
          destruct p0 as [[pn pa] pv]; destruct q as [[qn qa] qv].
          unfold pname, parch, pver in Hnm, Hcm; cbn [fst snd] in Hnm, Hcm.
          destruct (A.eq_dec qa pa) as [Ea | Ea].
          * subst qa.
            assert (Hin2 : PkgSet.In ((qn, pa), pv) S)
              by (rewrite Hnm; exact Hp1S).
            pose proof (HSvu (qn, pa) qv pv HqS Hin2) as Hvv.
            apply Hqp; congruence.
          * subst qn.
            destruct (HSci pn pa pv qa qv Hp1S HqS (fun E => Ea (eq_sym E)))
              as [Hc0 [Hcq Hveq]].
            rewrite Hc0 in Hcm.
            exact (Hcm (eq_sym Hveq)).
      - intros n v v' Hv Hv'.
        unfold reduceReal in *; rewrite SOmr.mem_map in Hv, Hv'.
        destruct Hv as [p [HpS Hpe]]; destruct Hv' as [p' [Hp'S Hp'e]].
        destruct p as [[pn pa] pv]; destruct p' as [[pn' pa'] pv'].
        unfold embedPkg, pname, parch, pver in Hpe, Hp'e;
          cbn [fst snd] in Hpe, Hp'e.
        pose proof (f_equal fst Hpe) as Hn1;
          pose proof (f_equal snd Hpe) as Hv1;
          pose proof (f_equal fst Hp'e) as Hn2;
          pose proof (f_equal snd Hp'e) as Hv2;
          cbn [fst snd] in Hn1, Hv1, Hn2, Hv2.
        subst v v'.
        rewrite Hn1 in Hn2.
        pose proof (f_equal fst Hn2) as Hnn;
          pose proof (f_equal snd Hn2) as Haa;
          cbn [fst snd] in Hnn, Haa.
        injection Haa as Haa.
        subst pn' pa'.
        exact (HSvu (pn, pa) pv pv' HpS Hp'S).
    Qed.

    Corollary debian_ma_core_soundness : forall I S,
        Deb.Reduction.T.IsResolution
          (Deb.Reduction.reduceReal (reduceInst I))
          (Deb.Reduction.reduceDeps (reduceInst I))
          (Deb.Reduction.embedPkg (embedPkg (inst_root I))) S ->
        IsResolution I
          (debianMAResolution (Deb.Reduction.debianResolution S)).
    Proof.
      intros I S H.
      exact (debian_ma_soundness I (Deb.Reduction.debianResolution S)
               (Deb.Reduction.debian_soundness (reduceInst I) S H)).
    Qed.

    Corollary debian_ma_core_completeness : forall I S,
        IsResolution I S ->
        Deb.Reduction.T.IsResolution
          (Deb.Reduction.reduceReal (reduceInst I))
          (Deb.Reduction.reduceDeps (reduceInst I))
          (Deb.Reduction.embedPkg (embedPkg (inst_root I)))
          (Deb.Reduction.coreResolution (reduceInst I) (coreResolution S)).
    Proof.
      intros I S H.
      exact (Deb.Reduction.debian_completeness (reduceInst I) (coreResolution S)
               (debian_ma_completeness I S H)).
    Qed.

    Module Lookup.
      Module NSet := FSetUOT N.
      Module PkgFibred := FibredRel NA V Pkg PkgSet.
      Module PkgPreimage := PreimageOfKeys N Pkg NSet PkgSet.
      Module ProvFibred := FibredLabelledRel Pkg N Deb.DTOT ProvElt Prov.
      Module ProvPreimage := PreimageOfKeys N ProvElt NSet Prov.
      Module DepsFibred := FibredRel Pkg Clause ClauseElt Deps.
      Module ConfFibred := FibredRel Pkg Atom ConfElt Conf.
      Module ClsPreimage := PreimageOfKeys Pkg ClsElt PkgSet Cls.

      Definition realAt (R : PkgSet.t) (n : N.t) (alpha : A.t) : PkgSet.t :=
        PkgFibred.tailFibre R (n, alpha).
      Definition realPreimage (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
        PkgPreimage.ofKeys pname ns R.
      Definition provPreimage (Pi : Prov.t) (ns : NSet.t) : Prov.t :=
        ProvPreimage.ofKeys ProvFibred.node ns Pi.
      Definition provFibre (Pi : Prov.t) (p : Pkg.t) : Prov.t :=
        ProvFibred.tailFibre Pi p.
      Definition depsFibre (D : Deps.t) (p : Pkg.t) : Deps.t :=
        DepsFibred.tailFibre D p.
      Definition confFibre (G : Conf.t) (p : Pkg.t) : Conf.t :=
        ConfFibred.tailFibre G p.
      Definition clsPreimage (M : Cls.t) (ps : PkgSet.t) : Cls.t :=
        ClsPreimage.ofKeys fst ps M.

      Lemma mem_realAt : forall R (n : N.t) (alpha : A.t) q,
          PkgSet.In q (realAt R n alpha) <->
          PkgSet.In q R /\ fst q = (n, alpha).
      Proof.
        intros R n alpha [[qn qb] qv]; unfold realAt.
        rewrite PkgFibred.mem_tailFibre; cbn [fst]; reflexivity.
      Qed.

      Lemma mem_realPreimage : forall R ns q,
          PkgSet.In q (realPreimage R ns) <->
          PkgSet.In q R /\ NSet.In (pname q) ns.
      Proof.
        intros R ns q; unfold realPreimage; apply PkgPreimage.mem_ofKeys.
      Qed.

      Lemma mem_provPreimage : forall Pi ns (q : Pkg.t) (m : N.t) v,
          Prov.In (q, (m, v)) (provPreimage Pi ns) <->
          Prov.In (q, (m, v)) Pi /\ NSet.In m ns.
      Proof.
        intros Pi ns q m v; unfold provPreimage; apply ProvPreimage.mem_ofKeys.
      Qed.

      Lemma mem_provFibre : forall Pi (p q : Pkg.t) (m : N.t) v,
          Prov.In (q, (m, v)) (provFibre Pi p) <->
          Prov.In (q, (m, v)) Pi /\ q = p.
      Proof.
        intros Pi p q m v; unfold provFibre; apply ProvFibred.mem_tailFibre.
      Qed.

      Lemma mem_depsFibre : forall D (p q : Pkg.t) Al,
          Deps.In (q, Al) (depsFibre D p) <-> Deps.In (q, Al) D /\ q = p.
      Proof.
        intros D p q Al; unfold depsFibre; apply DepsFibred.mem_tailFibre.
      Qed.

      Lemma mem_confFibre : forall G (p q : Pkg.t) a,
          Conf.In (q, a) (confFibre G p) <-> Conf.In (q, a) G /\ q = p.
      Proof.
        intros G p q a; unfold confFibre; apply ConfFibred.mem_tailFibre.
      Qed.

      Lemma mem_clsPreimage : forall M ps e,
          Cls.In e (clsPreimage M ps) <-> Cls.In e M /\ PkgSet.In (fst e) ps.
      Proof. intros M ps e; unfold clsPreimage;
        apply ClsPreimage.mem_ofKeys. Qed.

      Lemma reduceProv_class_sub : forall R Pi M M',
          (forall p, PkgSet.In p R -> classOf M' p = classOf M p) ->
          (forall (q : Pkg.t) (m : N.t) v,
              Prov.In (q, (m, v)) Pi -> classOf M' q = classOf M q) ->
          Deb.Prov.Subset (reduceProv R Pi M') (reduceProv R Pi M).
      Proof.
        intros R Pi M M' H1 H2 y Hy.
        rewrite mem_reduceProv in Hy |- *.
        destruct Hy as [[[q [m v]] [He Hl]] | [p0 [Hp0 Hl]]].
        - left; exists (q, (m, v)); split; [exact He |].
          unfold reduceProvEntry in Hl |- *; cbn [fst snd] in Hl |- *.
          rewrite <- (H2 q m v He); exact Hl.
        - right; exists p0; split; [exact Hp0 |].
          unfold implProvOf in Hl |- *.
          rewrite <- (H1 p0 Hp0); exact Hl.
      Qed.

      Lemma reduceConf_class_sub : forall R G M M',
          (forall p, PkgSet.In p R -> classOf M' p = classOf M p) ->
          Deb.Conf.Subset (reduceConf R G M') (reduceConf R G M).
      Proof.
        intros R G M M' H1 y Hy; rewrite mem_reduceConf in Hy |- *.
        destruct Hy as [[e [He Hl]] | [p0 [Hp0 Hl]]].
        - left; exists e; split; [exact He | exact Hl].
        - right; exists p0; split; [exact Hp0 |].
          unfold implConfOf in Hl |- *.
          rewrite <- (H1 p0 Hp0); exact Hl.
      Qed.

      Lemma classOf_clsPreimage : forall M ps p,
          PkgSet.In p ps -> classOf (clsPreimage M ps) p = classOf M p.
      Proof.
        intros M ps p Hp; unfold classOf.
        assert (E : ClsFibred.tailFibre (clsPreimage M ps) p
                    = ClsFibred.tailFibre M p).
        { apply Cls.ext; intros [q c].
          rewrite !ClsFibred.mem_tailFibre, mem_clsPreimage; cbn [fst].
          split.
          - intros [[Hm _] Hq]; split; assumption.
          - intros [Hm Hq]; split; [split; [exact Hm |] | exact Hq].
            rewrite Hq; exact Hp. }
        rewrite E; reflexivity.
      Qed.

      Lemma reduceProv_class : forall R Pi M M',
          (forall p, PkgSet.In p R -> classOf M' p = classOf M p) ->
          (forall (q : Pkg.t) (m : N.t) v,
              Prov.In (q, (m, v)) Pi -> classOf M' q = classOf M q) ->
          reduceProv R Pi M' = reduceProv R Pi M.
      Proof.
        intros R Pi M M' H1 H2; apply Deb.Prov.ext; intro y; split; intro Hy.
        - exact (reduceProv_class_sub R Pi M M' H1 H2 y Hy).
        - refine (reduceProv_class_sub R Pi M' M _ _ y Hy);
            [intros p Hp; symmetry; exact (H1 p Hp)
            | intros q m v He; symmetry; exact (H2 q m v He)].
      Qed.

      Lemma reduceConf_class : forall R G M M',
          (forall p, PkgSet.In p R -> classOf M' p = classOf M p) ->
          reduceConf R G M' = reduceConf R G M.
      Proof.
        intros R G M M' H1; apply Deb.Conf.ext; intro y; split; intro Hy.
        - exact (reduceConf_class_sub R G M M' H1 y Hy).
        - refine (reduceConf_class_sub R G M' M _ y Hy).
          intros p Hp; symmetry; exact (H1 p Hp).
      Qed.

      Module SOpo := SetOps ProvElt Pkg Prov PkgSet.
      Definition provOwners (Pi : Prov.t) : PkgSet.t := SOpo.map fst Pi.

      Lemma mem_provOwners : forall Pi q,
          PkgSet.In q (provOwners Pi) <->
          exists (m : N.t) v, Prov.In (q, (m, v)) Pi.
      Proof.
        intros Pi q; unfold provOwners; rewrite SOpo.mem_map; split.
        - intros [[q' [m v]] [He ->]]; exists m, v; exact He.
        - intros [m [v He]]; exists (q, (m, v)).
          split; [exact He | reflexivity].
      Qed.

      Definition provClsPreimage (M : Cls.t) (Rp : PkgSet.t) (Pis : Prov.t) :
          Cls.t :=
        clsPreimage M (PkgSet.union Rp (provOwners Pis)).

      Lemma reduceProv_provClsPreimage : forall Rp Pis M,
          reduceProv Rp Pis (provClsPreimage M Rp Pis) = reduceProv Rp Pis M.
      Proof.
        intros Rp Pis M; apply reduceProv_class.
        - intros p Hp; apply classOf_clsPreimage.
          apply PkgSet.union_spec; left; exact Hp.
        - intros q m v He; apply classOf_clsPreimage.
          apply PkgSet.union_spec; right; apply mem_provOwners.
          exists m, v; exact He.
      Qed.

      Lemma reduceConf_provClsPreimage : forall Rc Gs M Rp Pis,
          PkgSet.Subset Rc Rp ->
          reduceConf Rc Gs (provClsPreimage M Rp Pis) = reduceConf Rc Gs M.
      Proof.
        intros Rc Gs M Rp Pis Hsub; apply reduceConf_class.
        intros p Hp; apply classOf_clsPreimage.
        apply PkgSet.union_spec; left; exact (Hsub _ Hp).
      Qed.

      Lemma mem_reduceReal : forall R p,
          Deb.PkgSet.In p (reduceReal R) <->
          exists q : Pkg.t, PkgSet.In q R /\ p = embedPkg q.
      Proof. intros R p; unfold reduceReal; apply SOmr.mem_map. Qed.

      Lemma reduceReal_arch : forall R (n : QN.t) (v : V.t),
          Deb.PkgSet.In (n, v) (reduceReal R) -> exists b, snd n = QAArch b.
      Proof.
        intros R n v H; rewrite mem_reduceReal in H.
        destruct H as [q [_ Hq]]; exists (parch q).
        pose proof (f_equal fst Hq) as Hf; cbn [fst] in Hf.
        rewrite Hf; reflexivity.
      Qed.

      Lemma versions_restrict : forall R Rs (n : QN.t),
          PkgSet.Subset Rs R ->
          (forall q, PkgSet.In q R ->
             (pname q, QAArch (parch q)) = n -> PkgSet.In q Rs) ->
          Deb.C.versions (reduceReal Rs) n =
          Deb.C.versions (reduceReal R) n.
      Proof.
        intros R Rs n Hsub Hcov; apply Deb.VSet.ext; intro v.
        rewrite !Deb.C.mem_versions, !mem_reduceReal.
        split; intros [q [HqR Hq]]; exists q; (split; [| exact Hq]).
        - exact (Hsub _ HqR).
        - apply Hcov; [exact HqR | exact (f_equal fst (eq_sym Hq))].
      Qed.

      Definition ProvSubInst (I : Inst) (ns : NSet.t) (I' : Inst) : Prop :=
        PkgSet.Subset (inst_repo I') (inst_repo I) /\
        Prov.Subset (inst_prov I') (inst_prov I) /\
        (forall q, PkgSet.In q (inst_repo I) -> NSet.In (pname q) ns ->
           PkgSet.In q (inst_repo I')) /\
        (forall (q : Pkg.t) (m : N.t) v,
            Prov.In (q, (m, v)) (inst_prov I) -> NSet.In m ns ->
            Prov.In (q, (m, v)) (inst_prov I')).


      Lemma reduceProvEntry_shape : forall M (p0 : Pkg.t) (m0 : N.t) v0
          (q : Deb.Pkg.t) (n : QN.t) v,
          List.In (q, (n, v)) (reduceProvEntry M (p0, (m0, v0))) ->
          q = embedPkg p0 /\ fst n = m0.
      Proof.
        intros M p0 m0 v0 q n v H.
        apply in_reduceProvEntry in H; destruct H as [x [E _]].
        injection E as -> -> _; split; reflexivity.
      Qed.

      Lemma implProvOf_shape : forall M (p0 : Pkg.t)
          (q : Deb.Pkg.t) (n : QN.t) v,
          List.In (q, (n, v)) (implProvOf M p0) ->
          q = embedPkg p0 /\ fst n = pname p0.
      Proof.
        intros M p0 q n v H.
        apply in_implProvOf in H; destruct H as [x [E _]].
        injection E as -> -> _; split; reflexivity.
      Qed.

      Lemma reduceProv_mono : forall R Rp Pi Pis M,
          PkgSet.Subset Rp R -> Prov.Subset Pis Pi ->
          Deb.Prov.Subset (reduceProv Rp Pis M) (reduceProv R Pi M).
      Proof.
        intros R Rp Pi Pis M Hr Hp y Hy.
        rewrite mem_reduceProv in Hy |- *.
        destruct Hy as [[e [He Hl]] | [p0 [Hp0 Hl]]];
          [left; exists e; split; [exact (Hp _ He) | exact Hl]
          | right; exists p0; split; [exact (Hr _ Hp0) | exact Hl]].
      Qed.

      Lemma reduceProv_node : forall I ns I'
          (q : Deb.Pkg.t) (m : N.t) (x : NameArch) v,
          ProvSubInst I ns I' -> NSet.In m ns ->
          (Deb.Prov.In (q, ((m, x), v))
             (reduceProv (inst_repo I) (inst_prov I) (inst_cls I)) <->
           Deb.Prov.In (q, ((m, x), v))
             (reduceProv (inst_repo I') (inst_prov I') (inst_cls I))).
      Proof.
        intros I ns I' q m x v [Hr [Hp [Hcr Hcp]]] Hm.
        split; [| exact (reduceProv_mono _ _ _ _ (inst_cls I) Hr Hp _)].
        rewrite !mem_reduceProv.
        intros [[[e1 [e2 e3]] [He Hl]] | [p0 [Hp0 Hl]]].
        - destruct (reduceProvEntry_shape (inst_cls I) e1 e2 e3 q (m, x) v Hl)
            as [_ Hn].
          cbn [fst] in Hn.
          left; exists (e1, (e2, e3)); split; [| exact Hl].
          apply (Hcp e1 e2 e3 He); rewrite <- Hn; exact Hm.
        - destruct (implProvOf_shape (inst_cls I) p0 q (m, x) v Hl) as [_ Hn].
          cbn [fst] in Hn.
          right; exists p0; split; [| exact Hl].
          apply (Hcr p0 Hp0); rewrite <- Hn; exact Hm.
      Qed.

      Lemma provb_restrict : forall I ns I' (a' : Deb.Atom.t),
          ProvSubInst I ns I' -> NSet.In (fst (fst a')) ns ->
          Deb.Reduction.provb
            (reduceProv (inst_repo I') (inst_prov I') (inst_cls I)) a' =
          Deb.Reduction.provb
            (reduceProv (inst_repo I) (inst_prov I) (inst_cls I)) a'.
      Proof.
        intros I ns I' [[m x] phi] Hsl Hm; cbn [fst] in Hm.
        assert (Hsub := Hsl); destruct Hsub as [Hr [Hp _]].
        unfold Deb.Reduction.provb.
        apply Deb.Prov.exists_restrict.
        - exact (reduceProv_mono _ _ _ _ (inst_cls I) Hr Hp).
        - intros [q [mx v]] Hin Hb; cbn [Deb.aname Deb.aform fst snd] in Hb.
          apply andb_prop in Hb; destruct Hb as [Hn _].
          apply Deb.NEqb.eqb_true_iff in Hn as ->.
          apply (reduceProv_node I ns I' q m x v Hsl Hm); exact Hin.
      Qed.

      Lemma us_restrict : forall I ns Rr I' (a' : Deb.Atom.t),
          PkgSet.Subset Rr (inst_repo I) ->
          (forall q, PkgSet.In q (inst_repo I) -> NSet.In (pname q) ns ->
             PkgSet.In q Rr) ->
          ProvSubInst I ns I' -> NSet.In (fst (fst a')) ns ->
          Deb.Reduction.us (reduceReal Rr)
            (reduceProv (inst_repo I') (inst_prov I') (inst_cls I)) a' =
          Deb.Reduction.us (reduceReal (inst_repo I))
            (reduceProv (inst_repo I) (inst_prov I) (inst_cls I)) a'.
      Proof.
        intros I ns Rr I' [[m x] phi] Hrr Hcr Hsl Hm; cbn [fst] in Hm.
        assert (Hsub := Hsl); destruct Hsub as [Hr [Hp _]].
        assert (Hev : Deb.Reduction.evalAt (reduceReal Rr) ((m, x), phi)
                      = Deb.Reduction.evalAt (reduceReal (inst_repo I))
                        ((m, x), phi)).
        { unfold Deb.Reduction.evalAt; cbn [Deb.aname Deb.aform fst snd].
          rewrite (versions_restrict (inst_repo I) Rr (m, x) Hrr);
            [reflexivity |].
          intros q HqR Hq.
          assert (Hq2 : pname q = m) by exact (f_equal fst Hq).
          apply (Hcr q HqR); rewrite Hq2; exact Hm. }
        apply Deb.Reduction.T.VSet.ext; intro u'; unfold Deb.Reduction.us.
        rewrite !Deb.Reduction.T.VSet.union_spec, Hev.
        apply or_iff_compat_l.
        apply Deb.Reduction.SOew.filterMap_restrict.
        - exact (reduceProv_mono _ _ _ _ (inst_cls I) Hr Hp).
        - intros [q [mx v]] Hin Hf; cbn [fst snd Deb.aname Deb.aform] in Hf.
          rewrite if_some_iff, Bool.andb_true_iff, Deb.NEqb.eqb_true_iff in Hf.
          destruct Hf as [[-> _] _].
          apply (reduceProv_node I ns I' q m x v Hsl Hm); exact Hin.
      Qed.

      Lemma dependee_restrict : forall I ns Rr I' (a' : Deb.Atom.t),
          PkgSet.Subset Rr (inst_repo I) ->
          (forall q, PkgSet.In q (inst_repo I) -> NSet.In (pname q) ns ->
             PkgSet.In q Rr) ->
          ProvSubInst I ns I' -> NSet.In (fst (fst a')) ns ->
          Deb.Reduction.dependee (reduceReal Rr)
            (reduceProv (inst_repo I') (inst_prov I') (inst_cls I)) a' =
          Deb.Reduction.dependee (reduceReal (inst_repo I))
            (reduceProv (inst_repo I) (inst_prov I) (inst_cls I)) a'.
      Proof.
        intros I ns Rr I' a' Hrr Hcr Hsl Hm; unfold Deb.Reduction.dependee.
        rewrite (provb_restrict I ns I' a' Hsl Hm),
          (us_restrict I ns Rr I' a' Hrr Hcr Hsl Hm).
        destruct (Deb.Reduction.provb
                    (reduceProv (inst_repo I) (inst_prov I) (inst_cls I))
                    a'); [reflexivity |].
        unfold Deb.Reduction.evalAt.
        rewrite (versions_restrict (inst_repo I) Rr (Deb.aname a') Hrr);
          [reflexivity |].
        intros q HqR Hq.
        assert (Hq2 : pname q = fst (fst a')) by exact (f_equal fst Hq).
        apply (Hcr q HqR); rewrite Hq2; exact Hm.
      Qed.

      Lemma reduceConf_mono : forall R Rc G Gs M,
          PkgSet.Subset Rc R -> Conf.Subset Gs G ->
          Deb.Conf.Subset (reduceConf Rc Gs M) (reduceConf R G M).
      Proof.
        intros R Rc G Gs M Hr Hg y Hy.
        rewrite mem_reduceConf in Hy |- *.
        destruct Hy as [[e [He Hl]] | [p0 [Hp0 Hl]]];
          [left; exists e; split; [exact (Hg _ He) | exact Hl]
          | right; exists p0; split; [exact (Hr _ Hp0) | exact Hl]].
      Qed.

      Lemma reduceConf_pkg : forall R G M (p : Pkg.t) Rc Gs ea e,
          PkgSet.Subset Rc R -> Conf.Subset Gs G -> PkgSet.In p Rc ->
          (forall e, Conf.In e G -> fst e = p -> Conf.In e Gs) ->
          (Deb.Conf.In (embedPkg p, (ea, e)) (reduceConf R G M) <->
           Deb.Conf.In (embedPkg p, (ea, e)) (reduceConf Rc Gs M)).
      Proof.
        intros R G M p Rc Gs ea e Hr Hg Hin Hown.
        split; [| exact (reduceConf_mono R Rc G Gs M Hr Hg _)].
        rewrite !mem_reduceConf.
        intros [[[p0 a0] [He Hl]] | [p0 [Hp0 He]]].
        - pose proof (reduceConfEntry_pkg p0 a0 (embedPkg p) ea e Hl) as Hq.
          apply embedPkg_injective in Hq; subst p0.
          left; exists (p, a0); split;
            [exact (Hown (p, a0) He eq_refl) | exact Hl].
        - rewrite (implConfOf_pkg M p0) in He.
          pose proof (f_equal fst He) as Hq; cbn [fst] in Hq.
          apply embedPkg_injective in Hq; subst p0.
          right; exists p; split; [exact Hin |].
          rewrite (implConfOf_pkg M p); exact He.
      Qed.

      Lemma match_name : forall R Pi M (p : Pkg.t) (m : N.t) (x : NameArch) phi,
          PkgSet.In p R ->
          Deb.Match (reduceProv R Pi M) (embedPkg p) ((m, x), phi) ->
          m = pname p \/ exists v, Prov.In (p, (m, v)) Pi.
      Proof.
        intros R Pi M p m x phi HpR HM.
        apply (debMatch_char R Pi M p m x phi HpR) in HM.
        destruct x as [b | b | |];
          try (destruct HM as [[[Hn _] | [v [Hin _]]] _];
               [left; symmetry; exact Hn | right; exists v; exact Hin]).
        destruct HM as [Hn _]; left; symmetry; exact Hn.
      Qed.

      Lemma realPreimage_sub : forall R ns, PkgSet.Subset (realPreimage R ns) R.
      Proof.
        intros R ns q Hq; exact (proj1 (proj1 (mem_realPreimage R ns q) Hq)).
      Qed.

      Lemma realPreimage_cov : forall R ns q,
          PkgSet.In q R -> NSet.In (pname q) ns ->
          PkgSet.In q (realPreimage R ns).
      Proof. intros R ns q H1 H2; apply mem_realPreimage; split;
        assumption. Qed.

      Lemma provPreimage_sub : forall Pi ns,
        Prov.Subset (provPreimage Pi ns) Pi.
      Proof.
        intros Pi ns [q [m v]] He;
          exact (proj1 (proj1 (mem_provPreimage Pi ns q m v) He)).
      Qed.

      Lemma preimageProvSubInst : forall I ns,
          ProvSubInst I ns
            (MkInst (realPreimage (inst_repo I) ns) (inst_deps I) (inst_rec I)
               (provPreimage (inst_prov I) ns) (inst_conf I) (inst_cls I)
               (inst_root I)).
      Proof.
        intros I ns; unfold ProvSubInst; cbn [inst_repo inst_prov];
          repeat split.
        - apply realPreimage_sub.
        - apply provPreimage_sub.
        - apply realPreimage_cov.
        - intros q m v He Hm; apply mem_provPreimage; split; assumption.
      Qed.

      Module SOan := SetOps Atom N AtomSet NSet.
      Definition clauseNames (Al : Clause.t) : NSet.t :=
        SOan.map aname (clauseAtoms Al).

      Lemma mem_clauseNames : forall Al (m : N.t),
          NSet.In m (clauseNames Al) <->
          exists a, List.In a Al /\ aname a = m.
      Proof.
        intros Al m; unfold clauseNames; rewrite SOan.mem_map.
        split; intros [a [Ha Hm]]; exists a; rewrite mem_clauseAtoms in *;
          split; solve [exact Ha | symmetry; exact Hm].
      Qed.

      Module SOcn := SetOps ClauseElt N Deps NSet.
      Definition atomNames (D : Deps.t) (p : Pkg.t) : NSet.t :=
        SOcn.unionMap (fun c =>
            if Pkg.eq_dec (fst c) p then clauseNames (snd c) else NSet.empty)
          D.

      Lemma mem_atomNames : forall D (p : Pkg.t) (m : N.t),
          NSet.In m (atomNames D p) <->
          exists Al, Deps.In (p, Al) D /\ NSet.In m (clauseNames Al).
      Proof.
        intros D p m; unfold atomNames; rewrite SOcn.mem_unionMap_dec.
        split; [intros [[q Al] [Hc [Hq Hm]]]; cbn in Hq; subst q; eauto |].
        intros [Al [Hc Hm]]; exists (p, Al); auto.
      Qed.

      Module SOpn := SetOps ProvElt N Prov NSet.
      Definition providerNames (Pi : Prov.t) (n : N.t) : NSet.t :=
        SOpn.filterMap (fun e =>
            if N.eq_dec (fst (snd e)) n then Some (pname (fst e)) else None) Pi.

      Lemma mem_providerNames : forall Pi (n m : N.t),
          NSet.In m (providerNames Pi n) <->
          exists q v, Prov.In (q, (n, v)) Pi /\ pname q = m.
      Proof.
        intros Pi n m; unfold providerNames; rewrite SOpn.mem_filterMap_dec.
        split; [intros [[q [m0 v]] [He [Hm ->]]]; cbn in Hm; subst m0; eauto |].
        intros [q [v [He <-]]]; exists (q, (n, v)); auto.
      Qed.

      Module SOgn := SetOps ConfElt N Conf NSet.
      Definition confAtomNames (G : Conf.t) (p : Pkg.t) : NSet.t :=
        NSet.add (pname p)
          (SOgn.unionMap (fun e =>
               if Pkg.eq_dec (fst e) p then NSet.singleton (aname (snd e))
               else NSet.empty)
             G).

      Lemma mem_confAtomNames : forall G (p : Pkg.t) (m : N.t),
          NSet.In m (confAtomNames G p) <->
          m = pname p \/ exists a, Conf.In (p, a) G /\ m = aname a.
      Proof.
        intros G p m; unfold confAtomNames.
        rewrite NSet.add_spec, SOgn.mem_unionMap_dec.
        apply or_iff_compat_l; setoid_rewrite NSet.singleton_spec.
        split; [intros [[q a] [Hg [Hq Hm]]]; cbn in Hq; subst q; eauto |].
        intros [a [Hg Hm]]; exists (p, a); auto.
      Qed.

      Module SOnn := SetOps N N NSet NSet.
      Definition confRead (Pi : Prov.t) (G : Conf.t) (p : Pkg.t) : NSet.t :=
        SOnn.unionMap (fun n => NSet.add n (providerNames Pi n))
          (confAtomNames G p).

      Lemma mem_confRead : forall Pi G (p : Pkg.t) (m : N.t),
          NSet.In m (confRead Pi G p) <->
          exists n, NSet.In n (confAtomNames G p) /\
                    (m = n \/ NSet.In m (providerNames Pi n)).
      Proof.
        intros Pi G p m; unfold confRead; rewrite SOnn.mem_unionMap.
        split; intros [n [Hm Hm']]; exists n; (split; [exact Hm |]);
          [apply NSet.add_spec in Hm'; exact Hm' | apply NSet.add_spec; exact Hm'].
      Qed.

      Lemma reduceConf_confAtom : forall R G M (p : Pkg.t) (ea : Deb.Atom.t) e,
          Deb.Conf.In (embedPkg p, (ea, e)) (reduceConf R G M) ->
          NSet.In (fst (fst ea)) (confAtomNames G p).
      Proof.
        intros R G M p ea e H; rewrite mem_reduceConf in H.
        apply mem_confAtomNames.
        destruct H as [[[p0 a0] [He Hl]] | [p0 [_ He]]].
        - pose proof (reduceConfEntry_pkg p0 a0 (embedPkg p) ea e Hl) as Hq.
          apply embedPkg_injective in Hq; subst p0.
          right; exists a0; split;
            [exact He | exact (reduceConfEntry_name p a0 (embedPkg p) ea e Hl)].
        - left.
          pose proof (f_equal (fun e => fst (fst (snd e))) He) as Hn.
          cbn [fst snd] in Hn; rewrite (implConfOf_atomName M p0) in Hn.
          rewrite (implConfOf_pkg M p0) in He.
          pose proof (f_equal fst He) as Hq; cbn [fst] in Hq.
          apply embedPkg_injective in Hq; subst p0.
          exact (f_equal fst Hn).
      Qed.

      Lemma matchb_node_restrict : forall I ns I' (q : Deb.Pkg.t)
          (a' : Deb.Atom.t),
          ProvSubInst I ns I' -> NSet.In (fst (fst a')) ns ->
          Deb.matchb (reduceProv (inst_repo I') (inst_prov I') (inst_cls I))
            q a' =
          Deb.matchb (reduceProv (inst_repo I) (inst_prov I) (inst_cls I)) q a'.
      Proof.
        intros I ns I' q [[m x] phi] Hsl Hm; cbn [fst] in Hm.
        assert (Hsub := Hsl); destruct Hsub as [Hr [Hp _]].
        unfold Deb.matchb; f_equal.
        apply Deb.Prov.exists_restrict.
        - exact (reduceProv_mono _ _ _ _ (inst_cls I) Hr Hp).
        - intros [q' [mx v]] Hin Hb; cbn [fst snd Deb.aname Deb.aform] in Hb.
          apply andb_prop in Hb; destruct Hb as [Hq Hb].
          apply andb_prop in Hb; destruct Hb as [Hn _].
          apply Deb.PkgEqb.eqb_true_iff in Hq as ->.
          apply Deb.NEqb.eqb_true_iff in Hn as ->.
          apply (reduceProv_node I ns I' q m x v Hsl Hm); exact Hin.
      Qed.

      Lemma confNames_restrict : forall I ns Rr I' (a' : Deb.Atom.t),
          PkgSet.Subset Rr (inst_repo I) ->
          (forall q, PkgSet.In q (inst_repo I) -> NSet.In (pname q) ns ->
             PkgSet.In q Rr) ->
          ProvSubInst I ns I' -> NSet.In (fst (fst a')) ns ->
          (forall (q : Pkg.t) v, Prov.In (q, (fst (fst a'), v)) (inst_prov I) ->
                                  NSet.In (pname q) ns) ->
          Deb.Reduction.confNames (reduceReal Rr)
            (reduceProv (inst_repo I') (inst_prov I') (inst_cls I)) a' =
          Deb.Reduction.confNames (reduceReal (inst_repo I))
            (reduceProv (inst_repo I) (inst_prov I) (inst_cls I)) a'.
      Proof.
        intros I ns Rr I' a' Hrr Hcr Hsl Hm Hpn.
        apply Deb.Reduction.NSet.ext; intro qn;
          rewrite !Deb.Reduction.mem_confNames.
        split; intros [u [HR Hmb]]; exists u.
        - rewrite mem_reduceReal in HR |- *.
          destruct HR as [q [Hq Hqe]].
          split; [exists q; split; [exact (Hrr _ Hq) | exact Hqe] |].
          rewrite <- (matchb_node_restrict I ns I' _ a' Hsl Hm);
            exact Hmb.
        - rewrite (matchb_node_restrict I ns I' _ a' Hsl Hm).
          split; [| exact Hmb].
          rewrite mem_reduceReal in HR |- *.
          destruct HR as [q [Hq Hqe]]; exists q; split; [| exact Hqe].
          apply Hcr; [exact Hq |].
          destruct a' as [[m x] phi]; cbn [fst] in Hm, Hpn.
          rewrite Hqe in Hmb.
          apply Deb.matchb_iff in Hmb.
          destruct
            (match_name (inst_repo I) (inst_prov I) (inst_cls I) q m x phi
                      Hq Hmb) as [-> | [v Hin]];
            [exact Hm | exact (Hpn q v Hin)].
      Qed.

      Lemma confNames_inNs : forall R Pi M ns (a' : Deb.Atom.t) (m : QN.t),
          NSet.In (fst (fst a')) ns ->
          (forall (q : Pkg.t) v, Prov.In (q, (fst (fst a'), v)) Pi ->
                                  NSet.In (pname q) ns) ->
          Deb.Reduction.NSet.In m
            (Deb.Reduction.confNames (reduceReal R) (reduceProv R Pi M) a') ->
          NSet.In (fst m) ns.
      Proof.
        intros R Pi M ns [[m x] phi] qn Hm Hpn Hqn; cbn [fst] in Hm, Hpn.
        apply Deb.Reduction.mem_confNames in Hqn; destruct Hqn as [u [HR Hmb]].
        rewrite mem_reduceReal in HR; destruct HR as [q [Hq Hqe]].
        assert (E : fst qn = pname q).
        { pose proof (f_equal fst Hqe) as E1; cbn [fst] in E1.
          rewrite E1; reflexivity. }
        rewrite E; rewrite Hqe in Hmb.
        apply Deb.matchb_iff in Hmb.
        destruct (match_name R Pi M q m x phi Hq Hmb) as [-> | [v Hin]];
          [exact Hm | exact (Hpn q v Hin)].
      Qed.

      Lemma complementVS_restrict : forall I ns Rr I' (a' : Deb.Atom.t)
          (m : QN.t),
          PkgSet.Subset Rr (inst_repo I) ->
          (forall q, PkgSet.In q (inst_repo I) -> NSet.In (pname q) ns ->
             PkgSet.In q Rr) ->
          ProvSubInst I ns I' -> NSet.In (fst (fst a')) ns ->
          NSet.In (fst m) ns ->
          Deb.Reduction.complementVS (reduceReal Rr)
            (reduceProv (inst_repo I') (inst_prov I') (inst_cls I)) a' m =
          Deb.Reduction.complementVS (reduceReal (inst_repo I))
            (reduceProv (inst_repo I) (inst_prov I) (inst_cls I)) a' m.
      Proof.
        intros I ns Rr I' a' qn Hrr Hcr Hsl Hm Hqn.
        apply Deb.Reduction.T.VSet.ext; intro w;
          rewrite !Deb.Reduction.mem_complementVS.
        apply or_iff_compat_l.
        split; intros [u [HR [Hmb Hw]]]; exists u;
          rewrite mem_reduceReal in HR |- *; destruct HR as [q [Hq Hqe]].
        - rewrite <- (matchb_node_restrict I ns I' _ a' Hsl Hm).
          split; [exists q; split; [exact (Hrr _ Hq) | exact Hqe] | auto].
        - rewrite (matchb_node_restrict I ns I' _ a' Hsl Hm).
          split; [| auto].
          exists q; split; [| exact Hqe].
          apply Hcr; [exact Hq |].
          assert (E : fst qn = pname q).
          { pose proof (f_equal fst Hqe) as E1; cbn [fst] in E1.
            rewrite E1; reflexivity. }
          rewrite <- E; exact Hqn.
      Qed.

      Lemma singleton_clause : forall (p : Pkg.t) Al,
          Deps.In (p, Al) (Deps.singleton (p, Al)).
      Proof. intros p Al; apply Deps.singleton_spec; reflexivity. Qed.

      Lemma occursAtomb_reduceDeps : forall D (p : Pkg.t) Al a,
          Deps.In (p, Al) D -> List.In a Al ->
          Deb.Reduction.occursAtomb (reduceDeps D) (reduceAtom (parch p) a) =
            true.
      Proof.
        intros D p Al a HD Ha; apply Deb.Reduction.occursAtomb_iff.
        exists (embedPkg p), (reduceClause (parch p) Al); split.
        - rewrite mem_reduceDeps; exists p, Al; split; [exact HD | reflexivity].
        - apply mem_reduceClause; exists a; split; [exact Ha | reflexivity].
      Qed.

      Lemma reduceDeps_fibre : forall D (p : Pkg.t) A,
          Deb.Deps.In (embedPkg p, A) (reduceDeps D) <->
          Deb.Deps.In (embedPkg p, A) (reduceDeps (depsFibre D p)).
      Proof.
        intros D p A; rewrite !mem_reduceDeps; split.
        - intros [p0 [Al [HD Heq]]].
          pose proof (f_equal fst Heq) as Hf; cbn [fst] in Hf.
          apply embedPkg_injective in Hf; subst p0.
          exists p, Al; split; [| exact Heq].
          apply mem_depsFibre; split; [exact HD | reflexivity].
        - intros [p0 [Al [HD Heq]]].
          apply mem_depsFibre in HD; destruct HD as [HD _].
          exists p0, Al; split; [exact HD | exact Heq].
      Qed.

      Lemma reduceDeps_atomNames : forall D (p : Pkg.t) A (a' : Deb.Atom.t),
          Deb.Deps.In (embedPkg p, A) (reduceDeps D) ->
          Deb.AtomSet.In a' (Deb.clauseAtoms A) ->
          NSet.In (fst (fst a')) (atomNames D p).
      Proof.
        intros D p A a' HA Ha.
        rewrite mem_reduceDeps in HA; destruct HA as [p0 [Al [HD Heq]]].
        pose proof (f_equal fst Heq) as Hf; cbn [fst] in Hf.
        apply embedPkg_injective in Hf; subst p0.
        pose proof (f_equal snd Heq) as Hs; cbn [snd] in Hs; subst A.
        rewrite mem_reduceClause in Ha.
        destruct Ha as [a0 [Ha0 ->]].
        apply mem_atomNames; exists Al; split; [exact HD |].
        apply mem_clauseNames; exists a0; split; [exact Ha0 | reflexivity].
      Qed.

      Theorem versions_lookupOrig : forall I (n : N.t) (alpha : A.t),
          Deb.Reduction.versions (reduceInst I)
            (Deb.Reduction.Name.Orig (n, QAArch alpha)) =
          Deb.Reduction.versions
            (Deb.MkInst (reduceReal (realAt (inst_repo I) n alpha))
               Deb.Deps.empty Deb.Deps.empty Deb.Prov.empty Deb.Conf.empty
               (embedPkg (inst_root I)))
            (Deb.Reduction.Name.Orig (n, QAArch alpha)).
      Proof.
        intros I n alpha; cbn [Deb.Reduction.versions reduceInst Deb.inst_repo].
        rewrite (versions_restrict (inst_repo I) (realAt (inst_repo I) n alpha)
                   (n, QAArch alpha));
          [reflexivity | |].
        - intros q Hq;
            exact (proj1 (proj1 (mem_realAt (inst_repo I) n alpha q) Hq)).
        - intros q HqR Hq; apply mem_realAt; split; [exact HqR |].
          destruct q as [[qn qb] qv]; unfold pname, parch in Hq;
            cbn [fst snd] in Hq.
          injection Hq as -> ->; reflexivity.
      Qed.

      Theorem versions_lookupOrig_pseudo :
        forall I (n : N.t) (x : NameArch),
          (forall b, x <> QAArch b) ->
          Deb.Reduction.versions (reduceInst I)
            (Deb.Reduction.Name.Orig (n, x)) =
          Deb.Reduction.T.VSet.empty.
      Proof.
        intros I n x Hx; cbn [Deb.Reduction.versions reduceInst Deb.inst_repo].
        destruct (Deb.VSet.is_empty
                    (Deb.C.versions (reduceReal (inst_repo I)) (n, x))) eqn:He;
          [reflexivity | exfalso].
        destruct (Deb.VSet.choose
                    (Deb.C.versions (reduceReal (inst_repo I)) (n, x)))
          as [v |] eqn:Hc.
        - apply Deb.VSet.choose_spec1, Deb.C.mem_versions in Hc.
          destruct (reduceReal_arch (inst_repo I) (n, x) v Hc) as [b Hb].
          exact (Hx b Hb).
        - apply Deb.VSet.choose_spec2, Deb.VSet.is_empty_spec in Hc.
          congruence.
      Qed.

      Theorem dependees_lookupOrig : forall I (p : Pkg.t),
          PkgSet.In p (inst_repo I) ->
          Deb.Reduction.dependees (reduceInst I)
            (Deb.Reduction.embedPkg (embedPkg p)) =
          let ns := NSet.union (atomNames (inst_deps I) p)
                      (confRead (inst_prov I) (inst_conf I) p) in
          let Rp := PkgSet.add p (realPreimage (inst_repo I) ns) in
          let Pis := Prov.union (provPreimage (inst_prov I) ns)
                       (provFibre (inst_prov I) p) in
          let Mp := provClsPreimage (inst_cls I) Rp Pis in
          Deb.Reduction.dependees
            (Deb.MkInst (reduceReal (realPreimage (inst_repo I) ns))
               (reduceDeps (depsFibre (inst_deps I) p))
               (reduceRec (depsFibre (inst_rec I) p))
               (reduceProv Rp Pis Mp)
               (reduceConf (PkgSet.singleton p) (confFibre (inst_conf I) p) Mp)
               (embedPkg (inst_root I)))
            (Deb.Reduction.embedPkg (embedPkg p)).
      Proof.
        intros I p HpR; cbv zeta.
        rewrite reduceProv_provClsPreimage, reduceConf_provClsPreimage
          by (intros q Hq; apply PkgSet.singleton_spec in Hq;
              apply PkgSet.add_spec; left; exact Hq).
        set (ns := NSet.union (atomNames (inst_deps I) p)
                     (confRead (inst_prov I) (inst_conf I) p)).
        set (Rr := realPreimage (inst_repo I) ns).
        set (Rp := PkgSet.add p Rr).
        set (Pis := Prov.union (provPreimage (inst_prov I) ns)
                      (provFibre (inst_prov I) p)).
        set (Rc := PkgSet.singleton p).
        set (Gs := confFibre (inst_conf I) p).
        assert (HRr : PkgSet.Subset Rr (inst_repo I)) by apply realPreimage_sub.
        assert (HcovR : forall q, PkgSet.In q (inst_repo I) ->
                          NSet.In (pname q) ns ->
                          PkgSet.In q Rr) by apply realPreimage_cov.
        assert (HRp : PkgSet.Subset Rp (inst_repo I)).
        { intros q Hq; apply PkgSet.add_spec in Hq;
            destruct Hq as [-> | Hq]; [exact HpR | exact (HRr _ Hq)]. }
        assert (HPis : Prov.Subset Pis (inst_prov I)).
        { intros [q [m v]] He; apply Prov.union_spec in He;
            destruct He as [He | He];
            [ exact (proj1 (proj1 (mem_provPreimage (inst_prov I) ns q m v) He))
            | exact
              (proj1 (proj1 (mem_provFibre (inst_prov I) p q m v) He)) ]. }
        set (Ip := MkInst Rp (inst_deps I) (inst_rec I) Pis (inst_conf I)
                     (inst_cls I) (inst_root I)).
        assert (Hsl : ProvSubInst I ns Ip).
        { unfold ProvSubInst, Ip; cbn [inst_repo inst_prov]; repeat split;
            [ exact HRp | exact HPis
            | intros q Hq Hn; apply PkgSet.add_spec; right;
              exact (HcovR q Hq Hn)
            | intros q m v He Hn; apply Prov.union_spec; left;
              apply mem_provPreimage; split; [exact He | exact Hn] ]. }
        assert (Hinp : PkgSet.In p Rc)
          by (apply PkgSet.singleton_spec; reflexivity).
        assert (HRc : PkgSet.Subset Rc (inst_repo I)).
        { intros q Hq; apply PkgSet.singleton_spec in Hq; rewrite Hq;
           exact HpR. }
        assert (HGs : Conf.Subset Gs (inst_conf I)).
        { intros [q a0] He;
            exact (proj1 (proj1 (mem_confFibre (inst_conf I) p q a0) He)). }
        assert (Hown : forall e, Conf.In e (inst_conf I) -> fst e = p ->
                       Conf.In e Gs).
        { intros [q a0] He Hq; cbn [fst] in Hq; apply mem_confFibre; split;
            [exact He | exact Hq]. }
        assert (Hatom : forall an,
                   NSet.In an (atomNames (inst_deps I) p) -> NSet.In an ns)
          by (intros an Ha; apply NSet.union_spec; left; exact Ha).
        assert (Hcn : forall (ea : Deb.Atom.t) e,
                   Deb.Conf.In (embedPkg p, (ea, e))
                     (reduceConf (inst_repo I) (inst_conf I) (inst_cls I)) ->
                   NSet.In (fst (fst ea)) ns).
        { intros ea e Hg; apply NSet.union_spec; right; apply mem_confRead.
          exists (fst (fst ea)); split;
            [exact (reduceConf_confAtom _ _ _ p ea e Hg) | left; reflexivity]. }
        assert (Hcp : forall (ea : Deb.Atom.t) e,
                   Deb.Conf.In (embedPkg p, (ea, e))
                     (reduceConf (inst_repo I) (inst_conf I) (inst_cls I)) ->
                   forall (q : Pkg.t) v,
                     Prov.In (q, (fst (fst ea), v)) (inst_prov I) ->
                     NSet.In (pname q) ns).
        { intros ea e Hg q v Hin; apply NSet.union_spec; right.
          apply mem_confRead; exists (fst (fst ea)); split;
            [exact (reduceConf_confAtom _ _ _ p ea e Hg) | right].
          apply mem_providerNames; exists q, v; split;
            [exact Hin | reflexivity]. }
        replace (Deb.Reduction.embedPkg (embedPkg p))
          with (Deb.Reduction.Name.Orig (pname p, QAArch (parch p)),
                Deb.Reduction.Version.Orig (pver p)) by reflexivity.
        apply Deb.Reduction.T.DependeesSet.ext; intro y.
        rewrite !Deb.Reduction.dependees_orig_spec.
        cbn [reduceInst Deb.inst_repo Deb.inst_deps Deb.inst_rec Deb.inst_prov
             Deb.inst_conf].
        change (reduceProv Rp Pis (inst_cls I))
          with (reduceProv (inst_repo Ip) (inst_prov Ip) (inst_cls I)).
        split.
        - intros [[A [HA Hcase]] |
                  [[A [HA Hy]] |
                   [a0 [e [qn [Hg [Hqn [Hne [Hx Hy]]]]]]]]].
          + left; exists A; split;
              [exact (proj1 (reduceDeps_fibre (inst_deps I) p A) HA) |].
            destruct Hcase as [[Hcard [a1 [Hmin Hy]]] | [Hcard Hy]].
            * left; split; [exact Hcard |].
              exists a1; split; [exact Hmin |].
              rewrite Hy; symmetry.
              apply (dependee_restrict I ns Rr _ a1 HRr HcovR Hsl).
              exact (Hatom _ (reduceDeps_atomNames (inst_deps I) p A a1 HA
                                (Deb.AtomSet.min_elt_spec1 Hmin))).
            * right; split; [exact Hcard | exact Hy].
          + right; left; exists A; split;
              [exact (proj1 (reduceDeps_fibre (inst_rec I) p A) HA) | exact Hy].
          + right; right; exists a0, e, qn.
            split;
              [exact
                (proj1 (reduceConf_pkg _ _ _ p Rc Gs a0 e HRc HGs Hinp Hown)
                        Hg) |].
            split;
              [rewrite (confNames_restrict I ns Rr _ a0 HRr HcovR Hsl
                          (Hcn a0 e Hg) (Hcp a0 e Hg)); exact Hqn |].
            split; [exact Hne |].
            split; [exact Hx |].
            rewrite (complementVS_restrict I ns Rr _ a0 qn HRr HcovR Hsl
                       (Hcn a0 e Hg)
                       (confNames_inNs _ _ _ ns a0 qn (Hcn a0 e Hg)
                          (Hcp a0 e Hg)
                          Hqn)).
            exact Hy.
        - intros [[A [HA Hcase]] |
                  [[A [HA Hy]] |
                   [a0 [e [qn [Hg [Hqn [Hne [Hx Hy]]]]]]]]].
          + assert (HA' : Deb.Deps.In (embedPkg p, A)
                            (reduceDeps (inst_deps I)))
              by exact (proj2 (reduceDeps_fibre (inst_deps I) p A) HA).
            left; exists A; split; [exact HA' |].
            destruct Hcase as [[Hcard [a1 [Hmin Hy]]] | [Hcard Hy]].
            * left; split; [exact Hcard |].
              exists a1; split; [exact Hmin |].
              rewrite Hy.
              apply (dependee_restrict I ns Rr _ a1 HRr HcovR Hsl).
              exact (Hatom _ (reduceDeps_atomNames (inst_deps I) p A a1 HA'
                                (Deb.AtomSet.min_elt_spec1 Hmin))).
            * right; split; [exact Hcard | exact Hy].
          + right; left; exists A; split;
              [exact (proj2 (reduceDeps_fibre (inst_rec I) p A) HA) | exact Hy].
          + assert (Hg' : Deb.Conf.In (embedPkg p, (a0, e))
                            (reduceConf (inst_repo I) (inst_conf I)
                               (inst_cls I)))
              by exact (proj2 (reduceConf_pkg _ _ _ p Rc Gs a0 e HRc HGs Hinp
                                 Hown)
                          Hg).
            rewrite (confNames_restrict I ns Rr _ a0 HRr HcovR Hsl
                       (Hcn a0 e Hg') (Hcp a0 e Hg')) in Hqn.
            rewrite (complementVS_restrict I ns Rr _ a0 qn HRr HcovR Hsl
                       (Hcn a0 e Hg')
                       (confNames_inNs _ _ _ ns a0 qn (Hcn a0 e Hg')
                          (Hcp a0 e Hg') Hqn)) in Hy.
            right; right; exists a0, e, qn.
            split; [exact Hg' |].
            split; [exact Hqn |].
            split; [exact Hne |].
            split; [exact Hx | exact Hy].
      Qed.

      Theorem dependees_lookupDisjunct :
        forall I (p : Pkg.t) Al (a' : Deb.Atom.t),
          Deb.Reduction.T.PkgSet.In
            (Deb.Reduction.Name.Disjunct (reduceClause (parch p) Al),
             Deb.Reduction.Version.Atom a')
            (Deb.Reduction.reduceReal (reduceInst I)) ->
          Deb.Reduction.dependees (reduceInst I)
            (Deb.Reduction.Name.Disjunct (reduceClause (parch p) Al),
             Deb.Reduction.Version.Atom a') =
          let Rs := realPreimage (inst_repo I)
            (NSet.singleton (fst (fst a'))) in
          let Pis := provPreimage (inst_prov I)
            (NSet.singleton (fst (fst a'))) in
          Deb.Reduction.T.DependeesSet.singleton
            (Deb.Reduction.dependee (reduceReal Rs)
               (reduceProv Rs Pis (provClsPreimage (inst_cls I) Rs Pis)) a').
      Proof.
        intros I p Al [[m x] phi] H; cbv zeta.
        rewrite reduceProv_provClsPreimage.
        assert (Hm : NSet.In m (NSet.singleton m))
          by (apply NSet.singleton_spec; reflexivity).
        etransitivity;
          [exact (Deb.Reduction.Lookup.dependees_lookupDisjunct
                    (reduceInst I)
                    (reduceClause (parch p) Al) (m, x) phi H) |].
        rewrite Deb.Reduction.Lookup.dependee_filter; f_equal; symmetry.
        exact (dependee_restrict I (NSet.singleton m)
                 (realPreimage (inst_repo I) (NSet.singleton m)) _ ((m, x), phi)
                 (realPreimage_sub _ _) (realPreimage_cov _ _)
                 (preimageProvSubInst I _) Hm).
      Qed.

      Theorem versions_lookupSoft : forall I (p : Pkg.t) Al,
          Deps.In (p, Al) (inst_rec I) ->
          Deb.Reduction.versions (reduceInst I)
            (Deb.Reduction.Name.Soft (reduceClause (parch p) Al)) =
          Deb.Reduction.versionsSoft (reduceClause (parch p) Al).
      Proof. intros; reflexivity. Qed.

      Theorem dependees_lookupSoft :
        forall I (p : Pkg.t) Al (a' : Deb.Atom.t),
          Deb.Reduction.T.PkgSet.In
            (Deb.Reduction.Name.Soft (reduceClause (parch p) Al),
               Deb.Reduction.Version.Atom a')
            (Deb.Reduction.reduceReal (reduceInst I)) ->
          Deb.Reduction.dependees (reduceInst I)
            (Deb.Reduction.Name.Soft (reduceClause (parch p) Al),
             Deb.Reduction.Version.Atom a') =
          let Rs := realPreimage (inst_repo I)
            (NSet.singleton (fst (fst a'))) in
          let Pis := provPreimage (inst_prov I)
            (NSet.singleton (fst (fst a'))) in
          Deb.Reduction.T.DependeesSet.singleton
            (Deb.Reduction.dependee (reduceReal Rs)
               (reduceProv Rs Pis (provClsPreimage (inst_cls I) Rs Pis)) a').
      Proof.
        intros I p Al [[m x] phi] H; cbv zeta.
        rewrite reduceProv_provClsPreimage.
        assert (Hm : NSet.In m (NSet.singleton m))
          by (apply NSet.singleton_spec; reflexivity).
        etransitivity;
          [exact (Deb.Reduction.Lookup.dependees_lookupSoft
                    (reduceInst I)
                    (reduceClause (parch p) Al) (m, x) phi H) |].
        rewrite Deb.Reduction.Lookup.dependee_filter; f_equal; symmetry.
        exact (dependee_restrict I (NSet.singleton m)
                 (realPreimage (inst_repo I) (NSet.singleton m)) _ ((m, x), phi)
                 (realPreimage_sub _ _) (realPreimage_cov _ _)
                 (preimageProvSubInst I _) Hm).
      Qed.

      Theorem versions_lookupSelectorAgree :
        forall I (D' Dopt' : Deb.Deps.t) (p : Pkg.t) (a : Atom.t),
          Deb.Reduction.occursAtomb
            (Deb.Reduction.allClauses (reduceDeps (inst_deps I))
               (reduceRec (inst_rec I)))
            (reduceAtom (parch p) a) =
          Deb.Reduction.occursAtomb (Deb.Reduction.allClauses D' Dopt')
            (reduceAtom (parch p) a) ->
          Deb.Reduction.versions (reduceInst I)
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a)) =
          let Rs := realPreimage (inst_repo I) (NSet.singleton (aname a)) in
          let Pis := provPreimage (inst_prov I) (NSet.singleton (aname a)) in
          Deb.Reduction.versions
            (Deb.MkInst (reduceReal Rs) D' Dopt'
               (reduceProv Rs Pis (provClsPreimage (inst_cls I) Rs Pis))
               Deb.Conf.empty (embedPkg (inst_root I)))
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a)).
      Proof.
        intros I D' Dopt' p a _; cbv zeta.
        rewrite reduceProv_provClsPreimage.
        assert (Hm : NSet.In (fst (fst (reduceAtom (parch p) a)))
                       (NSet.singleton (aname a)))
          by (apply NSet.singleton_spec; reflexivity).
        assert (Hus := us_restrict I (NSet.singleton (aname a))
                         (realPreimage (inst_repo I) (NSet.singleton (aname a)))
                         _ (reduceAtom (parch p) a) (realPreimage_sub _ _)
                         (realPreimage_cov _ _) (preimageProvSubInst I _) Hm).
        cbn [inst_repo inst_prov] in Hus.
        cbn [Deb.Reduction.versions reduceInst Deb.inst_repo Deb.inst_prov].
        rewrite Hus; reflexivity.
      Qed.

      Theorem dependees_lookupSelectorAgree :
        forall I (D' Dopt' : Deb.Deps.t) (p : Pkg.t) (a : Atom.t)
               (v : Deb.Reduction.Version.t),
          Deb.Reduction.occursAtomb
            (Deb.Reduction.allClauses (reduceDeps (inst_deps I))
               (reduceRec (inst_rec I)))
            (reduceAtom (parch p) a) =
          Deb.Reduction.occursAtomb (Deb.Reduction.allClauses D' Dopt')
            (reduceAtom (parch p) a) ->
          Deb.Reduction.dependees (reduceInst I)
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a), v) =
          let Rs := realPreimage (inst_repo I) (NSet.singleton (aname a)) in
          let Pis := provPreimage (inst_prov I) (NSet.singleton (aname a)) in
          Deb.Reduction.dependees
            (Deb.MkInst (reduceReal Rs) D' Dopt'
               (reduceProv Rs Pis (provClsPreimage (inst_cls I) Rs Pis))
               Deb.Conf.empty (embedPkg (inst_root I)))
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a), v).
      Proof.
        intros I D' Dopt' p a v _; destruct v; reflexivity.
      Qed.

      Theorem versions_lookupSelector :
        forall I (p : Pkg.t) Al (a : Atom.t),
          Deps.In (p, Al) (inst_deps I) -> List.In a Al ->
          Deb.Reduction.versions (reduceInst I)
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a)) =
          let Rs := realPreimage (inst_repo I) (NSet.singleton (aname a)) in
          let Pis := provPreimage (inst_prov I) (NSet.singleton (aname a)) in
          Deb.Reduction.versions
            (Deb.MkInst (reduceReal Rs)
               (reduceDeps (Deps.singleton (p, Al))) Deb.Deps.empty
               (reduceProv Rs Pis (provClsPreimage (inst_cls I) Rs Pis))
               Deb.Conf.empty (embedPkg (inst_root I)))
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a)).
      Proof.
        intros I p Al a HD Ha.
        apply versions_lookupSelectorAgree.
        rewrite
          (Deb.Reduction.occursAtomb_allClausesL (reduceDeps (inst_deps I))
                   (reduceRec (inst_rec I)) (reduceAtom (parch p) a)
                   (occursAtomb_reduceDeps (inst_deps I) p Al a HD Ha)),
          (Deb.Reduction.occursAtomb_allClausesL
             (reduceDeps (Deps.singleton (p, Al)))
             Deb.Deps.empty (reduceAtom (parch p) a)
             (occursAtomb_reduceDeps (Deps.singleton (p, Al)) p Al a
                (singleton_clause p Al) Ha)).
        reflexivity.
      Qed.

      Theorem dependees_lookupSelector :
        forall I (p : Pkg.t) Al (a : Atom.t) (v : Deb.Reduction.Version.t),
          Deps.In (p, Al) (inst_deps I) -> List.In a Al ->
          Deb.Reduction.dependees (reduceInst I)
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a), v) =
          let Rs := realPreimage (inst_repo I) (NSet.singleton (aname a)) in
          let Pis := provPreimage (inst_prov I) (NSet.singleton (aname a)) in
          Deb.Reduction.dependees
            (Deb.MkInst (reduceReal Rs)
               (reduceDeps (Deps.singleton (p, Al))) Deb.Deps.empty
               (reduceProv Rs Pis (provClsPreimage (inst_cls I) Rs Pis))
               Deb.Conf.empty (embedPkg (inst_root I)))
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a), v).
      Proof.
        intros I p Al a v HD Ha.
        apply dependees_lookupSelectorAgree.
        rewrite
          (Deb.Reduction.occursAtomb_allClausesL (reduceDeps (inst_deps I))
                   (reduceRec (inst_rec I)) (reduceAtom (parch p) a)
                   (occursAtomb_reduceDeps (inst_deps I) p Al a HD Ha)),
          (Deb.Reduction.occursAtomb_allClausesL
             (reduceDeps (Deps.singleton (p, Al)))
             Deb.Deps.empty (reduceAtom (parch p) a)
             (occursAtomb_reduceDeps (Deps.singleton (p, Al)) p Al a
                (singleton_clause p Al) Ha)).
        reflexivity.
      Qed.

      Theorem versions_lookupSelectorRec :
        forall I (p : Pkg.t) Al (a : Atom.t),
          Deps.In (p, Al) (inst_rec I) -> List.In a Al ->
          Deb.Reduction.versions (reduceInst I)
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a)) =
          let Rs := realPreimage (inst_repo I) (NSet.singleton (aname a)) in
          let Pis := provPreimage (inst_prov I) (NSet.singleton (aname a)) in
          Deb.Reduction.versions
            (Deb.MkInst (reduceReal Rs)
               Deb.Deps.empty (reduceRec (Deps.singleton (p, Al)))
               (reduceProv Rs Pis (provClsPreimage (inst_cls I) Rs Pis))
               Deb.Conf.empty (embedPkg (inst_root I)))
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a)).
      Proof.
        intros I p Al a HRec Ha.
        apply versions_lookupSelectorAgree.
        rewrite
          (Deb.Reduction.occursAtomb_allClausesR (reduceDeps (inst_deps I))
                   (reduceRec (inst_rec I)) (reduceAtom (parch p) a)
                   (occursAtomb_reduceDeps (inst_rec I) p Al a HRec Ha)),
          (Deb.Reduction.occursAtomb_allClausesR Deb.Deps.empty
             (reduceRec (Deps.singleton (p, Al))) (reduceAtom (parch p) a)
             (occursAtomb_reduceDeps (Deps.singleton (p, Al)) p Al a
                (singleton_clause p Al) Ha)).
        reflexivity.
      Qed.

      Theorem dependees_lookupSelectorRec :
        forall I (p : Pkg.t) Al (a : Atom.t) (v : Deb.Reduction.Version.t),
          Deps.In (p, Al) (inst_rec I) -> List.In a Al ->
          Deb.Reduction.dependees (reduceInst I)
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a), v) =
          let Rs := realPreimage (inst_repo I) (NSet.singleton (aname a)) in
          let Pis := provPreimage (inst_prov I) (NSet.singleton (aname a)) in
          Deb.Reduction.dependees
            (Deb.MkInst (reduceReal Rs)
               Deb.Deps.empty (reduceRec (Deps.singleton (p, Al)))
               (reduceProv Rs Pis (provClsPreimage (inst_cls I) Rs Pis))
               Deb.Conf.empty (embedPkg (inst_root I)))
            (Deb.Reduction.Name.Selector (reduceAtom (parch p) a), v).
      Proof.
        intros I p Al a v HRec Ha.
        apply dependees_lookupSelectorAgree.
        rewrite
          (Deb.Reduction.occursAtomb_allClausesR (reduceDeps (inst_deps I))
                   (reduceRec (inst_rec I)) (reduceAtom (parch p) a)
                   (occursAtomb_reduceDeps (inst_rec I) p Al a HRec Ha)),
          (Deb.Reduction.occursAtomb_allClausesR Deb.Deps.empty
             (reduceRec (Deps.singleton (p, Al))) (reduceAtom (parch p) a)
             (occursAtomb_reduceDeps (Deps.singleton (p, Al)) p Al a
                (singleton_clause p Al) Ha)).
        reflexivity.
      Qed.

    End Lookup.

    Theorem debian_ma_retraction : forall S,
        debianMAResolution (coreResolution S) = S.
    Proof.
      intro S; apply PkgSet.ext; intro q.
      rewrite mem_debianMAResolution; unfold coreResolution, reduceReal.
      exact (SOmr.mem_map_inj _ _ _ embedPkg_injective).
    Qed.

    Corollary debian_ma_core_retraction : forall I S,
        debianMAResolution
          (Deb.Reduction.debianResolution
             (Deb.Reduction.coreResolution (reduceInst I) (coreResolution S))) =
               S.
    Proof.
      intros I S.
      rewrite Deb.Reduction.debian_retraction.
      apply debian_ma_retraction.
    Qed.
  End Reduction.
End DebianMA.
