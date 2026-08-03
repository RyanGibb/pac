(* The direct semantics (IsResolution) follows the
   MultiarchSpec where it speaks and apt 3.1 where it is silent, and a
   translation compiles instances into the single-arch Debian calculus at
   names N * NameArch. Implicit cross-arch exclusion targets a group
   pseudo-name (QAGroup) that only real group members provide, so ordinary
   providers can never be hit by implicit conflicts. *)

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
  | QAArch (a : A.t)
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
  (* Mangled names group by base name: an owner's conflicts exempt every
     arch instance of its own package, per dpkg's name-scoped conflicts. *)
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

  (* Multi-Arch classes; arch:all packages are rewritten to the native
     arch by the frontend (apt does the same), and all+same is downgraded
     to no before instances are built. *)
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
  (* Total class lookup with default MANo; instances are expected to be
     functional in the package. *)
  Definition classOf (M : Cls.t) (p : Pkg.t) : MAClass :=
    match Cls.min_elt (ClsFibred.tailFibre M p) with
    | Some e => snd e
    | None => MANo
    end.

  (* Dependency-Atom architecture qualifiers (Policy 7.1 + MultiarchSpec):
     unqualified, :any, :native, or an explicit :arch. *)
  Inductive Qual : Type :=
  | QUnq
  | QAny
  | QNative
  | QArch (a : A.t).

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
  Module ClauseElt := PairUOT Pkg AtomSet.AsUOT.
  Module Deps := FSetUOT ClauseElt.

  Module Provided := PairUOT N Deb.DTOT.
  Module ProvElt := PairUOT Pkg Provided.
  Module Prov := FSetUOT ProvElt.

  Module ConfElt := PairUOT Pkg Atom.
  Module Conf := FSetUOT ConfElt.

  (* Name/Formula satisfaction ignoring architecture: q is named n and its
     version satisfies f, or q provides n at a matching version. *)
  Definition BaseMatch (Pi : Prov.t) (n : N.t) (f : Deb.Ver.Formula)
      (q : Pkg.t) : Prop :=
    (pname q = n /\ Deb.vfHolds f (pver q) = true) \/
    (exists vt, Prov.In (q, (n, vt)) Pi /\ Deb.vtMatchb vt f = true).

  (* Arch reach (MultiarchSpec): a same-arch candidate always reaches;
     M-A: foreign reaches any target arch; :any atoms reach any arch but
     only M-A: allowed candidates. *)
  Definition MAMatch (Pi : Prov.t) (M : Cls.t) (da : A.t)
      (a : Atom.t) (q : Pkg.t) : Prop :=
    BaseMatch Pi (aname a) (aform a) q /\
    match aqual a with
    | QUnq => parch q = da \/ classOf M q = MAForeign
    | QNative => parch q = AP.native \/ classOf M q = MAForeign
    | QArch b => parch q = b \/ classOf M q = MAForeign
    | QAny => classOf M q = MAAllowed
    end.

  (* Conflict-side match: an unqualified negative applies to every
     architecture (apt replicates it across the group). *)
  Definition MAConfMatch (Pi : Prov.t) (M : Cls.t)
      (a : Atom.t) (q : Pkg.t) : Prop :=
    BaseMatch Pi (aname a) (aform a) q /\
    match aqual a with
    | QUnq => True
    | QNative => parch q = AP.native \/ classOf M q = MAForeign
    | QArch b => parch q = b \/ classOf M q = MAForeign
    | QAny => classOf M q = MAAllowed
    end.

  (* Direct multiarch semantics. The declarer's base-name group is exempt from
     its own negatives, which is apt's first ignorable rule (a negative never
     applies to a provider whose owner shares the declarer's group); apt's
     second -- an implicit cross-arch negative never reaches a provider of
     another group -- holds here by construction rather than as a side
     condition, since implicit negatives land on the group pseudo-name and
     only real group members provide it. *)
  Record IsResolution
      (R : PkgSet.t) (D : Deps.t) (Pi : Prov.t) (G : Conf.t)
      (M : Cls.t) (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_clause_closure :
        forall p, PkgSet.In p S ->
        forall Al, Deps.In (p, Al) D ->
        exists a, AtomSet.In a Al /\
          exists q, PkgSet.In q S /\ MAMatch Pi M (parch p) a q
    ; res_conflict_avoidance :
        forall p, PkgSet.In p S ->
        forall a, Conf.In (p, a) G ->
        ~ exists q, PkgSet.In q S /\ pname q <> pname p /\
            MAConfMatch Pi M a q
    ; res_lockstep :
        forall p q, PkgSet.In p S -> PkgSet.In q S ->
        pname p = pname q -> parch p <> parch q ->
        classOf M p = MASame /\ classOf M q = MASame /\ pver p = pver q
    ; res_version_unique : C.VersionUnique S }.

  Definition embedPkg (p : Pkg.t) : Deb.Ver.C.Pkg.t :=
    ((pname p, QAArch (parch p)), pver p).

  Module SOmr := SetOps Pkg Deb.Ver.C.Pkg PkgSet Deb.Ver.C.PkgSet.
  Definition reduceReal (R : PkgSet.t) : Deb.Ver.C.PkgSet.t :=
    SOmr.map embedPkg R.

  Definition reduceAtom (da : A.t) (a : Atom.t) : Deb.Atom.t :=
    ((aname a,
      match aqual a with
      | QUnq => QAArch da
      | QNative => QAArch AP.native
      | QArch b => QAArch b
      | QAny => QAAny
      end), aform a).

  Module SOcl := SetOps Atom Deb.Atom AtomSet Deb.AtomSet.
  Definition reduceClause (da : A.t) (Al : AtomSet.t) : Deb.AtomSet.t :=
    SOcl.map (reduceAtom da) Al.

  Module SOdp := SetOps ClauseElt Deb.ClauseElt Deps Deb.Deps.
  Definition reduceDeps (D : Deps.t) : Deb.Deps.t :=
    SOdp.map (fun c =>
        (embedPkg (fst c), reduceClause (parch (fst c)) (snd c)))
      D.

  (* Declared Provides, replicated by the provider's class: no/same reach
     the provider's own arch, foreign every arch, allowed additionally the
     :any pseudo-name. *)
  Definition reduceProvEntry (M : Cls.t) (e : ProvElt.t) :
      list Deb.ProvElt.t :=
    let p := fst e in
    let m := fst (snd e) in
    let vt := snd (snd e) in
    match classOf M p with
    | MAForeign =>
        List.map (fun b => (embedPkg p, ((m, QAArch b), vt))) A.enum
    | MAAllowed =>
        (embedPkg p, ((m, QAAny), vt))
          :: (embedPkg p, ((m, QAArch (parch p)), vt)) :: nil
    | _ => (embedPkg p, ((m, QAArch (parch p)), vt)) :: nil
    end.

  (* Implicit provides: every real package provides its group pseudo-name
     at its own version (carrier of the implicit cross-arch exclusion);
     M-A: foreign packages provide their own name at every arch;
     M-A: allowed packages provide their own :any pseudo-name. *)
  Definition implProvOf (M : Cls.t) (p : Pkg.t) : list Deb.ProvElt.t :=
    (embedPkg p, ((pname p, QAGroup), Deb.DTVal (pver p)))
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

  (* Hand-written negatives: unqualified negatives target the group
     pseudo-name so they reach every architecture's real packages, plus
     the per-arch and :any provider names. *)
  Definition reduceConfEntry (e : ConfElt.t) : list Deb.ConfElt.t :=
    let p := fst e in
    let a := snd e in
    let n := aname a in
    let f := aform a in
    match aqual a with
    | QUnq =>
        (embedPkg p, (((n, QAGroup), f), true))
          :: (embedPkg p, (((n, QAAny), f), true))
          :: List.map (fun b => (embedPkg p, (((n, QAArch b), f), true))) A.enum
    | QNative => (embedPkg p, (((n, QAArch AP.native), f), true)) :: nil
    | QArch b => (embedPkg p, (((n, QAArch b), f), true)) :: nil
    | QAny => (embedPkg p, (((n, QAAny), f), true)) :: nil
    end.

  (* Implicit sibling exclusion via the group pseudo-name: non-same
     packages exclude every other group member; M-A: same packages exclude
     only version-skewed members (the lockstep Breaks (!= v)). *)
  Definition implConfOf (M : Cls.t) (p : Pkg.t) : Deb.ConfElt.t :=
    match classOf M p with
    | MASame =>
        (embedPkg p, (((pname p, QAGroup), Deb.Ver.FCmp OpNe (pver p)), false))
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

  Definition tryInvPkg (s : Deb.Ver.C.Pkg.t) : option Pkg.t :=
    match s with
    | ((n, QAArch b), v) => Some ((n, b), v)
    | _ => None
    end.

  Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
  Proof.
    intros [[n b] v]; unfold tryInvPkg, embedPkg, pname, parch, pver;
      cbn [fst snd]; reflexivity.
  Qed.

  Lemma tryInvPkg_some : forall (s : Deb.Ver.C.Pkg.t) (p : Pkg.t),
      tryInvPkg s = Some p -> embedPkg p = s.
  Proof.
    intros [[n [b | |]] v] p H; cbn [tryInvPkg] in H; try discriminate.
    injection H as <-; unfold embedPkg, pname, parch, pver;
      cbn [fst snd]; reflexivity.
  Qed.

  Module SOpre := SetOps Deb.Ver.C.Pkg Pkg Deb.Ver.C.PkgSet PkgSet.
  Definition multiarchResolution (S : Deb.Ver.C.PkgSet.t) : PkgSet.t :=
    SOpre.filterMap tryInvPkg S.

  Lemma embedPkg_injective : forall p q, embedPkg p = embedPkg q -> p = q.
  Proof. exact (SOpre.emb_injective tryInvPkg embedPkg tryInvPkg_embed). Qed.

  Lemma mem_multiarchResolution : forall S q,
      PkgSet.In q (multiarchResolution S) <-> Deb.Ver.C.PkgSet.In (embedPkg q) S.
  Proof.
    unfold multiarchResolution.
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
    - intros [p [Al [Hc ->]]]; exists (p, Al); split; [exact Hc | reflexivity].
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

  (* Which mangled atoms a real package matches, per target-name
     shape: the shared engine behind the three transfer lemmas. *)
  Lemma debMatch_char : forall R Pi M q n x f,
      PkgSet.In q R ->
      (Deb.Match (reduceProv R Pi M) (embedPkg q) ((n, x), f) <->
       match x with
       | QAArch b =>
           BaseMatch Pi n f q /\ (parch q = b \/ classOf M q = MAForeign)
       | QAAny => BaseMatch Pi n f q /\ classOf M q = MAAllowed
       | QAGroup => pname q = n /\ Deb.vfHolds f (pver q) = true
       end).
  Proof.
    intros R Pi M [[qn qa] qv] n x f HqR.
    unfold Deb.Match; cbn [Deb.aname Deb.aform fst snd].
    split.
    - intros [[He Hv] | [vt [Hin Hvt]]].
      + injection He; intros; subst.
        split; [left; split; [reflexivity | exact Hv] | left; reflexivity].
      + rewrite mem_reduceProv in Hin.
        destruct Hin as [[e [HePi Hle]] | [p [HpR Hlp]]].
        * destruct e as [[[pn pa] pv] [m vt']].
          unfold reduceProvEntry in Hle; cbn [fst snd] in Hle.
          destruct (classOf M ((pn, pa), pv)) eqn:Hcls.
          -- destruct Hle as [Heq | []].
             injection Heq; intros; subst;
             cbn [pname parch pver fst snd] in *; subst.
             split;
               [right; exists vt; split; [exact HePi | exact Hvt]
               | left; reflexivity].
          -- destruct Hle as [Heq | []].
             injection Heq; intros; subst;
             cbn [pname parch pver fst snd] in *; subst.
             split;
               [right; exists vt; split; [exact HePi | exact Hvt]
               | left; reflexivity].
          -- apply in_map_iff in Hle; destruct Hle as [b [Heq Hb]].
             injection Heq; intros; subst;
             cbn [pname parch pver fst snd] in *; subst.
             split;
               [right; exists vt; split; [exact HePi | exact Hvt]
               | right; exact Hcls].
          -- destruct Hle as [Heq | [Heq | []]].
             ++ injection Heq; intros; subst;
             cbn [pname parch pver fst snd] in *; subst.
                split;
                  [right; exists vt; split; [exact HePi | exact Hvt]
                  | exact Hcls].
             ++ injection Heq; intros; subst;
             cbn [pname parch pver fst snd] in *; subst.
                split;
                  [right; exists vt; split; [exact HePi | exact Hvt]
                  | left; reflexivity].
        * destruct p as [[pn pa] pv].
          unfold implProvOf in Hlp; simpl in Hlp.
          destruct Hlp as [Heq | Htail].
          -- injection Heq; intros; subst;
             cbn [pname parch pver fst snd] in *; subst.
             split; [reflexivity | exact Hvt].
          -- destruct (classOf M ((pn, pa), pv)) eqn:Hcls; simpl in Htail;
               try contradiction.
             ++ apply in_map_iff in Htail; destruct Htail as [b [Heq Hb]].
                injection Heq; intros; subst;
             cbn [pname parch pver fst snd] in *; subst.
                split;
                  [left; split; [reflexivity | exact Hvt]
                  | right; exact Hcls].
             ++ destruct Htail as [Heq | []].
                injection Heq; intros; subst;
             cbn [pname parch pver fst snd] in *; subst.
                split;
                  [left; split; [reflexivity | exact Hvt] | exact Hcls].
    - destruct x as [b | |].
      + intros [HB Harch].
        destruct HB as [[Hn Hv] | [vt [HPi Hvt]]].
        * destruct Harch as [Hb | Hf].
          -- subst; left; split; [reflexivity | exact Hv].
          -- subst n; right; exists (Deb.DTVal qv); split; [| exact Hv].
             rewrite mem_reduceProv; right.
             exists ((qn, qa), qv); split; [exact HqR |].
             unfold implProvOf; rewrite Hf; simpl.
             right; apply in_map_iff.
             exists b; split; [reflexivity | apply A.enum_complete].
        * right; exists vt; split; [| exact Hvt].
          rewrite mem_reduceProv; left.
          exists (((qn, qa), qv), (n, vt)); split; [exact HPi |].
          unfold reduceProvEntry; cbn [fst snd].
          destruct (classOf M ((qn, qa), qv)) eqn:Hc.
          -- destruct Harch as [Hb | Hf];
               [subst b; left; reflexivity | congruence].
          -- destruct Harch as [Hb | Hf];
               [subst b; left; reflexivity | congruence].
          -- apply in_map_iff;
               exists b; split; [reflexivity | apply A.enum_complete].
          -- destruct Harch as [Hb | Hf];
               [subst b; right; left; reflexivity | congruence].
      + intros [HB Hall].
        destruct HB as [[Hn Hv] | [vt [HPi Hvt]]].
        * subst n; right; exists (Deb.DTVal qv); split; [| exact Hv].
          rewrite mem_reduceProv; right.
          exists ((qn, qa), qv); split; [exact HqR |].
          unfold implProvOf; rewrite Hall; simpl.
          right; left; reflexivity.
        * right; exists vt; split; [| exact Hvt].
          rewrite mem_reduceProv; left.
          exists (((qn, qa), qv), (n, vt)); split; [exact HPi |].
          unfold reduceProvEntry; cbn [fst snd]; rewrite Hall.
          left; reflexivity.
      + intros [Hn Hv].
        subst n; right; exists (Deb.DTVal qv); split; [| exact Hv].
        rewrite mem_reduceProv; right.
        exists ((qn, qa), qv); split; [exact HqR |].
        unfold implProvOf; left; reflexivity.
  Qed.

  Lemma match_transfer : forall R Pi M da a q,
      PkgSet.In q R ->
      (MAMatch Pi M da a q <->
       Deb.Match (reduceProv R Pi M) (embedPkg q) (reduceAtom da a)).
  Proof.
    intros R Pi M da a q HqR.
    unfold MAMatch, reduceAtom.
    destruct (aqual a) as [ | | | b].
    - exact (iff_sym
        (debMatch_char R Pi M q (aname a) (QAArch da) (aform a) HqR)).
    - exact (iff_sym
        (debMatch_char R Pi M q (aname a) QAAny (aform a) HqR)).
    - exact (iff_sym
        (debMatch_char R Pi M q (aname a) (QAArch AP.native) (aform a)
           HqR)).
    - exact (iff_sym
        (debMatch_char R Pi M q (aname a) (QAArch b) (aform a) HqR)).
  Qed.

  Lemma conf_transfer : forall R Pi M (p : Pkg.t) a q,
      PkgSet.In q R ->
      ((exists q' ea x, List.In (q', (ea, x)) (reduceConfEntry (p, a)) /\
          Deb.Match (reduceProv R Pi M) (embedPkg q) ea) <->
       MAConfMatch Pi M a q).
  Proof.
    intros R Pi M p a q HqR.
    unfold MAConfMatch, reduceConfEntry; cbn [fst snd].
    destruct (aqual a) as [ | | | b].
    - split.
      + intros [q' [ea [x [Hce HM]]]].
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
        destruct HB as [[Hn Hv] | [vt [HPi Hvt]]].
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
             split; [right; exists vt; split; assumption | left; reflexivity].
    - split.
      + intros [q' [ea [x [Hce HM]]]].
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
      + intros [q' [ea [x [Hce HM]]]].
        destruct Hce as [E | []].
        injection E as _ <- _.
        exact (proj1 (debMatch_char R Pi M q (aname a) (QAArch AP.native)
                        (aform a) HqR) HM).
      + intros H.
        exists (embedPkg p), ((aname a, QAArch AP.native), aform a), true.
        split; [left; reflexivity |].
        exact (proj2 (debMatch_char R Pi M q (aname a) (QAArch AP.native)
                        (aform a) HqR) H).
    - split.
      + intros [q' [ea [x [Hce HM]]]].
        destruct Hce as [E | []].
        injection E as _ <- _.
        exact (proj1 (debMatch_char R Pi M q (aname a) (QAArch b)
                        (aform a) HqR) HM).
      + intros H.
        exists (embedPkg p), ((aname a, QAArch b), aform a), true.
        split; [left; reflexivity |].
        exact (proj2 (debMatch_char R Pi M q (aname a) (QAArch b)
                        (aform a) HqR) H).
  Qed.

  (* The implicit group conflict of p is matched by (mangled) q iff q is a
     same-name group member that p excludes: everyone for non-same classes,
     version-skewed members under the M-A: same lockstep. *)
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

  Lemma reduceConfEntry_pkg : forall p a q ea x,
      List.In (q, (ea, x)) (reduceConfEntry (p, a)) -> q = embedPkg p.
  Proof.
    intros p a q ea x H; unfold reduceConfEntry in H; cbn [fst snd] in H.
    destruct (aqual a) as [ | | | b]; simpl in H;
      repeat (destruct H as [E | H]; [congruence |]);
      try contradiction.
    apply in_map_iff in H; destruct H as [b' [E _]]; congruence.
  Qed.

  Lemma reduceConfEntry_flag : forall p a q ea x,
      List.In (q, (ea, x)) (reduceConfEntry (p, a)) -> x = true.
  Proof.
    intros p a q ea x H; unfold reduceConfEntry in H; cbn [fst snd] in H.
    destruct (aqual a) as [ | | | b]; simpl in H;
      repeat (destruct H as [E | H]; [congruence |]);
      try contradiction.
    apply in_map_iff in H; destruct H as [b' [E _]]; congruence.
  Qed.

  Lemma reduceConfEntry_name : forall (p : Pkg.t) (a : Atom.t)
      (q : Deb.Ver.C.Pkg.t) (ea : Deb.Atom.t) (x : bool),
      List.In (q, (ea, x)) (reduceConfEntry (p, a)) ->
      fst (fst ea) = aname a.
  Proof.
    intros p a q ea x H; unfold reduceConfEntry in H; cbn [fst snd] in H.
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

  Theorem debian_ma_soundness : forall R D Pi G M r S,
      Deb.IsResolution (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
        (reduceConf R G M) (embedPkg r) S ->
      IsResolution R D Pi G M r (multiarchResolution S).
  Proof.
    intros R D Pi G M r S HT.
    destruct HT as [Hsub Hroot Hcc Hca Hvu].
    assert (HinR : forall q,
               PkgSet.In q (multiarchResolution S) -> PkgSet.In q R).
    { intros q Hq.
      rewrite mem_multiarchResolution in Hq.
      apply Hsub in Hq.
      unfold reduceReal in *; rewrite SOmr.mem_map in Hq.
      destruct Hq as [p [HpR Hpe]].
      apply embedPkg_injective in Hpe; subst q; exact HpR. }
    constructor.
    - exact HinR.
    - rewrite mem_multiarchResolution; exact Hroot.
    - intros p HpS Al HAl.
      pose proof HpS as HpT; rewrite mem_multiarchResolution in HpT.
      assert (Hd : Deb.Deps.In (embedPkg p, reduceClause (parch p) Al)
                     (reduceDeps D)).
      { rewrite mem_reduceDeps; exists p, Al; split;
          [exact HAl | reflexivity]. }
      destruct (Hcc (embedPkg p) HpT _ Hd) as [ea [Ha [qh [HqhS HqhM]]]].
      unfold reduceClause in *; rewrite SOcl.mem_map in Ha; destruct Ha as [a [Hat Hae]]; subst ea.
      pose proof (Hsub _ HqhS) as HqhR.
      unfold reduceReal in *; rewrite SOmr.mem_map in HqhR; destruct HqhR as [q [HqR Hqe]]; subst qh.
      exists a; split; [exact Hat |].
      exists q; split.
      + rewrite mem_multiarchResolution; exact HqhS.
      + exact (proj2 (match_transfer R Pi M (parch p) a q HqR) HqhM).
    - intros p HpS a HG [q [HqS [Hqp HCM]]].
      pose proof HpS as HpT; rewrite mem_multiarchResolution in HpT.
      pose proof (HinR q HqS) as HqR.
      destruct (proj2 (conf_transfer R Pi M p a q HqR) HCM)
        as [c1 [c2 [c3 [Hce HM]]]].
      pose proof (reduceConfEntry_pkg p a c1 c2 c3 Hce) as Hf; subst c1.
      pose proof (reduceConfEntry_flag p a (embedPkg p) c2 c3 Hce) as Hx;
        subst c3.
      assert (HceG : Deb.Conf.In (embedPkg p, (c2, true)) (reduceConf R G M)).
      { rewrite mem_reduceConf; left; exists (p, a); split;
          [exact HG | exact Hce]. }
      apply (Hca (embedPkg p) HpT c2 true HceG).
      exists (embedPkg q); split;
        [ rewrite mem_multiarchResolution in HqS; exact HqS
        | split;
          [ intro E; apply Hqp; rewrite (embedPkg_injective _ _ E); reflexivity
          | split;
            [ intros _; apply Bool.not_true_is_false; intro Eg;
              apply Hqp;
              exact (proj1 (groupEq_iff (pname q) (pname p)
                              (QAArch (parch q)) (QAArch (parch p))) Eg)
            | exact HM ] ] ].
    - intros p q HpS HqS Hname Harch.
      pose proof (HinR p HpS) as HpR; pose proof (HinR q HqS) as HqR.
      pose proof HpS as HpT; rewrite mem_multiarchResolution in HpT.
      pose proof HqS as HqT; rewrite mem_multiarchResolution in HqT.
      assert (Hpq : embedPkg q <> embedPkg p).
      { intro E; apply Harch; unfold embedPkg in E; injection E; intros;
          congruence. }
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
          apply (Hca (embedPkg p) HpT _ _ HinCp);
          exists (embedPkg q);
          (split;
           [ exact HqT
           | split;
             [ exact Hpq
             | split;
               [ intro Hx; discriminate Hx
               | apply (proj2 (impl_conf_transfer R Pi M p q HqR));
                 rewrite Hc; split; [symmetry; exact Hname | exact I] ] ] ]). }
      assert (HclsQ : classOf M q = MASame).
      { destruct (classOf M q) eqn:Hc; try reflexivity; exfalso;
          apply (Hca (embedPkg q) HqT _ _ HinCq);
          exists (embedPkg p);
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
        apply (Hca (embedPkg p) HpT _ _ HinCp).
        exists (embedPkg q); split;
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
      rewrite mem_multiarchResolution in Hv, Hv'.
      destruct n as [nm ar].
      exact (Hvu (nm, QAArch ar) v v' Hv Hv').
  Qed.

  Theorem debian_ma_completeness : forall R D Pi G M r S,
      IsResolution R D Pi G M r S ->
      Deb.IsResolution (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
        (reduceConf R G M) (embedPkg r) (reduceReal S).
  Proof.
    intros R D Pi G M r S HS.
    destruct HS as [HSsub HSroot HScc HSca HSci HSvu].
    constructor.
    - intros x Hx.
      unfold reduceReal in *; rewrite SOmr.mem_map in Hx; unfold reduceReal; rewrite SOmr.mem_map.
      destruct Hx as [p [HpS Hpe]]; exists p; split;
        [exact (HSsub p HpS) | exact Hpe].
    - unfold reduceReal; rewrite SOmr.mem_map; exists r; split; [exact HSroot | reflexivity].
    - intros ph HphT A HA.
      unfold reduceReal in *; rewrite SOmr.mem_map in HphT; destruct HphT as [p [HpS Hpe]]; subst ph.
      rewrite mem_reduceDeps in HA.
      destruct HA as [p0 [Al [HD Heq]]].
      pose proof (f_equal fst Heq) as Hp2; pose proof (f_equal snd Heq) as HA2;
        cbn [fst snd] in Hp2, HA2.
      apply embedPkg_injective in Hp2; subst p0 A.
      destruct (HScc p HpS Al HD) as [a [Hat [q [HqS HqM]]]].
      exists (reduceAtom (parch p) a); split.
      { unfold reduceClause; rewrite SOcl.mem_map; exists a; split; [exact Hat | reflexivity]. }
      exists (embedPkg q); split.
      { unfold reduceReal; rewrite SOmr.mem_map; exists q; split; [exact HqS | reflexivity]. }
      exact (proj1 (match_transfer R Pi M (parch p) a q (HSsub q HqS)) HqM).
    - intros ph HphT ea x HaG [qh [HqhT [Hne [Hex HM]]]].
      unfold reduceReal in *; rewrite SOmr.mem_map in HphT; destruct HphT as [p1 [Hp1S Hp1e]].
      unfold reduceReal in *; rewrite SOmr.mem_map in HqhT; destruct HqhT as [q [HqS Hqe]]; subst qh.
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
                            (QAArch (parch q)) (QAArch (parch p0))) En) in Hex.
          discriminate. }
        apply (HSca p0 Hp1S a HG).
        exists q; split;
          [ exact HqS
          | split;
            [ exact Hnp
            | apply (proj1 (conf_transfer R Pi M p0 a q (HSsub q HqS)));
              exists (embedPkg p0), ea, true; split;
              [exact Hce | exact HM] ] ].
      + rewrite implConfOf_pkg in Heq.
        pose proof (f_equal fst Heq) as Hf; pose proof (f_equal snd Heq) as Hs;
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
        * destruct (HSci ((pn, pa), pv) ((qn, qa), qv) Hp1S HqS
                      (eq_sym Hnm) (fun E => Ea (eq_sym E)))
            as [Hc0 [Hcq Hveq]].
          rewrite Hc0 in Hcm.
          exact (Hcm (eq_sym Hveq)).
    - intros n v v' Hv Hv'.
      unfold reduceReal in *; rewrite SOmr.mem_map in Hv, Hv'.
      destruct Hv as [p [HpS Hpe]]; destruct Hv' as [p' [Hp'S Hp'e]].
      destruct p as [[pn pa] pv]; destruct p' as [[pn' pa'] pv'].
      unfold embedPkg, pname, parch, pver in Hpe, Hp'e;
        cbn [fst snd] in Hpe, Hp'e.
      pose proof (f_equal fst Hpe) as Hn1; pose proof (f_equal snd Hpe) as Hv1;
        pose proof (f_equal fst Hp'e) as Hn2;
        pose proof (f_equal snd Hp'e) as Hv2;
        cbn [fst snd] in Hn1, Hv1, Hn2, Hv2.
      subst v v'.
      rewrite Hn1 in Hn2.
      pose proof (f_equal fst Hn2) as Hnn; pose proof (f_equal snd Hn2) as Haa;
        cbn [fst snd] in Hnn, Haa.
      injection Haa as Haa.
      subst pn' pa'.
      exact (HSvu (pn, pa) pv pv' HpS Hp'S).
  Qed.

  (* reduceReal is the completeness witness and multiarchResolution the
     decoder; embedPkg is injective, so the round trip is the identity. *)
  Corollary multiarchResolution_reduceReal : forall S,
      multiarchResolution (reduceReal S) = S.
  Proof.
    intro S; apply PkgSet.ext; intro q.
    rewrite mem_multiarchResolution; unfold reduceReal; rewrite SOmr.mem_map.
    split.
    - intros [p [HpS Hp]]; rewrite (embedPkg_injective _ _ Hp); exact HpS.
    - intro H; exists q; split; [exact H | reflexivity].
  Qed.

  (* The two reductions compose into one Core instance; a Core resolution of
     it decodes, through both decoders in turn, to a multiarch resolution. *)
  Corollary debian_ma_core_soundness : forall R D Pi G M r S,
      Deb.T.IsResolution
        (Deb.reduceReal (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
           (reduceConf R G M))
        (Deb.reduceDeps (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
           (reduceConf R G M))
        (Deb.embedPkg (embedPkg r)) S ->
      IsResolution R D Pi G M r
        (multiarchResolution (Deb.debianResolution S)).
  Proof.
    intros R D Pi G M r S H.
    exact (debian_ma_soundness R D Pi G M r (Deb.debianResolution S)
             (Deb.debian_soundness _ _ _ _ (embedPkg r) S H)).
  Qed.

  Corollary debian_ma_core_completeness : forall R D Pi G M r S,
      IsResolution R D Pi G M r S ->
      Deb.T.IsResolution
        (Deb.reduceReal (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
           (reduceConf R G M))
        (Deb.reduceDeps (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
           (reduceConf R G M))
        (Deb.embedPkg (embedPkg r))
        (Deb.coreResolution (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
           (reduceConf R G M) (reduceReal S)).
  Proof.
    intros R D Pi G M r S H.
    exact (Deb.debian_completeness _ _ _ _ (embedPkg r) (reduceReal S)
             (debian_ma_completeness R D Pi G M r S H)).
  Qed.

  Corollary multiarchResolution_core : forall R D Pi G M S,
      multiarchResolution
        (Deb.debianResolution
           (Deb.coreResolution (reduceReal R) (reduceDeps D)
              (reduceProv R Pi M) (reduceConf R G M) (reduceReal S))) = S.
  Proof.
    intros R D Pi G M S.
    rewrite Deb.debianResolution_coreResolution.
    apply multiarchResolution_reduceReal.
  Qed.

  (* Slice justification for the multiarch solving path: a Core query at a
     mangled name is answered by translating a small MA-side slice, and each
     theorem below pins a slice whose translation the Debian lookup theorems
     cannot tell apart from the whole instance's. Provider and conflict
     slices span a base name's whole group across architectures, because
     every real package implicitly provides its group pseudo-name -- and, at
     M-A: foreign, its own name at every architecture -- so a mangled name's
     providers are not confined to one arch's fibre. *)
  Module Lookup.
    Module NSet := FSetUOT N.
    Module PkgFibred := FibredRel NA V Pkg PkgSet.
    Module PkgPreimage := PreimageOfKeys N Pkg NSet PkgSet.
    Module ProvFibred := FibredLabelledRel Pkg N Deb.DTOT ProvElt Prov.
    Module ProvPreimage := PreimageOfKeys N ProvElt NSet Prov.
    Module DepsFibred := FibredRel Pkg AtomSet.AsUOT ClauseElt Deps.
    Module ConfFibred := FibredRel Pkg Atom ConfElt Conf.
    Module ConfPreimage := PreimageOfKeys N ConfElt NSet Conf.
    Module ClsPreimage := PreimageOfKeys Pkg ClsElt PkgSet Cls.

    Definition realAt (R : PkgSet.t) (n : N.t) (b : A.t) : PkgSet.t :=
      PkgFibred.tailFibre R (n, b).
    Definition groupOf (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
      PkgPreimage.ofKeys pname ns R.
    Definition provOf (Pi : Prov.t) (ns : NSet.t) : Prov.t :=
      ProvPreimage.ofKeys ProvFibred.node ns Pi.
    Definition provBy (Pi : Prov.t) (p : Pkg.t) : Prov.t :=
      ProvFibred.tailFibre Pi p.
    Definition depsOf (D : Deps.t) (p : Pkg.t) : Deps.t :=
      DepsFibred.tailFibre D p.
    Definition confBy (G : Conf.t) (p : Pkg.t) : Conf.t :=
      ConfFibred.tailFibre G p.
    Definition confOn (G : Conf.t) (ns : NSet.t) : Conf.t :=
      ConfPreimage.ofKeys (fun e => aname (snd e)) ns G.
    Definition clsOf (M : Cls.t) (P : PkgSet.t) : Cls.t :=
      ClsPreimage.ofKeys fst P M.

    Lemma mem_realAt : forall R (n : N.t) (b : A.t) q,
        PkgSet.In q (realAt R n b) <-> PkgSet.In q R /\ fst q = (n, b).
    Proof.
      intros R n b [[qn qb] qv]; unfold realAt.
      rewrite PkgFibred.mem_tailFibre; cbn [fst]; reflexivity.
    Qed.

    Lemma mem_groupOf : forall R ns q,
        PkgSet.In q (groupOf R ns) <-> PkgSet.In q R /\ NSet.In (pname q) ns.
    Proof. intros R ns q; unfold groupOf; apply PkgPreimage.mem_ofKeys. Qed.

    Lemma mem_provOf : forall Pi ns (q : Pkg.t) (m : N.t) vt,
        Prov.In (q, (m, vt)) (provOf Pi ns) <->
        Prov.In (q, (m, vt)) Pi /\ NSet.In m ns.
    Proof.
      intros Pi ns q m vt; unfold provOf; apply ProvPreimage.mem_ofKeys.
    Qed.

    Lemma mem_provBy : forall Pi (p q : Pkg.t) (m : N.t) vt,
        Prov.In (q, (m, vt)) (provBy Pi p) <->
        Prov.In (q, (m, vt)) Pi /\ q = p.
    Proof.
      intros Pi p q m vt; unfold provBy; apply ProvFibred.mem_tailFibre.
    Qed.

    Lemma mem_depsOf : forall D (p q : Pkg.t) Al,
        Deps.In (q, Al) (depsOf D p) <-> Deps.In (q, Al) D /\ q = p.
    Proof. intros D p q Al; unfold depsOf; apply DepsFibred.mem_tailFibre. Qed.

    Lemma mem_confBy : forall G (p q : Pkg.t) a,
        Conf.In (q, a) (confBy G p) <-> Conf.In (q, a) G /\ q = p.
    Proof. intros G p q a; unfold confBy; apply ConfFibred.mem_tailFibre. Qed.

    Lemma mem_confOn : forall G ns e,
        Conf.In e (confOn G ns) <->
        Conf.In e G /\ NSet.In (aname (snd e)) ns.
    Proof. intros G ns e; unfold confOn; apply ConfPreimage.mem_ofKeys. Qed.

    Lemma mem_clsOf : forall M P e,
        Cls.In e (clsOf M P) <-> Cls.In e M /\ PkgSet.In (fst e) P.
    Proof. intros M P e; unfold clsOf; apply ClsPreimage.mem_ofKeys. Qed.

    (* classOf reads only the fibre at its argument, so a class table cut
       down to a package set answers unchanged inside that set. *)
    Lemma classOf_clsOf : forall M P p,
        PkgSet.In p P -> classOf (clsOf M P) p = classOf M p.
    Proof.
      intros M P p Hp; unfold classOf.
      assert (E : ClsFibred.tailFibre (clsOf M P) p
                  = ClsFibred.tailFibre M p).
      { apply Cls.ext; intros [q c].
        rewrite !ClsFibred.mem_tailFibre, mem_clsOf; cbn [fst].
        split.
        - intros [[Hm _] Hq]; split; assumption.
        - intros [Hm Hq]; split; [split; [exact Hm |] | exact Hq].
          rewrite Hq; exact Hp. }
      rewrite E; reflexivity.
    Qed.

    Lemma reduceProv_class_sub : forall R Pi M M',
        (forall p, PkgSet.In p R -> classOf M' p = classOf M p) ->
        (forall (q : Pkg.t) (m : N.t) vt,
            Prov.In (q, (m, vt)) Pi -> classOf M' q = classOf M q) ->
        Deb.Prov.Subset (reduceProv R Pi M') (reduceProv R Pi M).
    Proof.
      intros R Pi M M' H1 H2 y Hy.
      rewrite mem_reduceProv in Hy |- *.
      destruct Hy as [[[q [m vt]] [He Hl]] | [p0 [Hp0 Hl]]].
      - left; exists (q, (m, vt)); split; [exact He |].
        unfold reduceProvEntry in Hl |- *; cbn [fst snd] in Hl |- *.
        rewrite <- (H2 q m vt He); exact Hl.
      - right; exists p0; split; [exact Hp0 |].
        unfold implProvOf in Hl |- *.
        rewrite <- (H1 p0 Hp0); exact Hl.
    Qed.

    (* The class table is read only at packages of R and at the packages
       declaring the Provides, so the driver's per-query class slice is
       invisible to the translation. *)
    Lemma reduceProv_class : forall R Pi M M',
        (forall p, PkgSet.In p R -> classOf M' p = classOf M p) ->
        (forall (q : Pkg.t) (m : N.t) vt,
            Prov.In (q, (m, vt)) Pi -> classOf M' q = classOf M q) ->
        reduceProv R Pi M' = reduceProv R Pi M.
    Proof.
      intros R Pi M M' H1 H2; apply Deb.Prov.ext; intro y; split; intro Hy.
      - exact (reduceProv_class_sub R Pi M M' H1 H2 y Hy).
      - refine (reduceProv_class_sub R Pi M' M _ _ y Hy);
          [intros p Hp; symmetry; exact (H1 p Hp)
          | intros q m vt He; symmetry; exact (H2 q m vt He)].
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

    Lemma reduceConf_class : forall R G M M',
        (forall p, PkgSet.In p R -> classOf M' p = classOf M p) ->
        reduceConf R G M' = reduceConf R G M.
    Proof.
      intros R G M M' H1; apply Deb.Conf.ext; intro y; split; intro Hy.
      - exact (reduceConf_class_sub R G M M' H1 y Hy).
      - refine (reduceConf_class_sub R G M' M _ y Hy).
        intros p Hp; symmetry; exact (H1 p Hp).
    Qed.

    Lemma mem_reduceReal : forall R y,
        Deb.PkgSet.In y (reduceReal R) <->
        exists q : Pkg.t, PkgSet.In q R /\ y = embedPkg q.
    Proof. intros R y; unfold reduceReal; apply SOmr.mem_map. Qed.

    (* embedPkg mints only QAArch names, so the :any and group pseudo-names
       carry no real packages at all. *)
    Lemma reduceReal_arch : forall R (nx : QN.t) (v : V.t),
        Deb.PkgSet.In (nx, v) (reduceReal R) -> exists b, snd nx = QAArch b.
    Proof.
      intros R nx v H; rewrite mem_reduceReal in H.
      destruct H as [q [_ Hq]]; exists (parch q).
      pose proof (f_equal fst Hq) as Hf; cbn [fst] in Hf.
      rewrite Hf; reflexivity.
    Qed.

    Lemma realVersions_restrict : forall R Rs (nx : QN.t),
        PkgSet.Subset Rs R ->
        (forall q, PkgSet.In q R ->
           (pname q, QAArch (parch q)) = nx -> PkgSet.In q Rs) ->
        Deb.Ver.realVersions (reduceReal Rs) nx =
        Deb.Ver.realVersions (reduceReal R) nx.
    Proof.
      intros R Rs nx Hsub Hcov; apply Deb.VSet.ext; intro v.
      rewrite !Deb.Ver.realVersions_spec, !mem_reduceReal.
      split; intros [q [HqR Hq]]; exists q; (split; [| exact Hq]).
      - exact (Hsub _ HqR).
      - apply Hcov; [exact HqR | exact (f_equal fst (eq_sym Hq))].
    Qed.

    (* A slice that keeps every real package and every declared Provides
       reaching a base name in ns; reduceProv agrees with the whole
       instance's at every mangled name over ns. *)
    Definition ProvSlice (R : PkgSet.t) (Pi : Prov.t) (ns : NSet.t)
        (Rp : PkgSet.t) (Pis : Prov.t) : Prop :=
      PkgSet.Subset Rp R /\ Prov.Subset Pis Pi /\
      (forall q, PkgSet.In q R -> NSet.In (pname q) ns -> PkgSet.In q Rp) /\
      (forall (q : Pkg.t) (m : N.t) vt,
          Prov.In (q, (m, vt)) Pi -> NSet.In m ns -> Prov.In (q, (m, vt)) Pis).

    (* A slice that keeps p itself and p's own Provides; matchb at the
       mangled p agrees with the whole instance's. *)
    Definition PkgProvSlice (R : PkgSet.t) (Pi : Prov.t) (p : Pkg.t)
        (Rp : PkgSet.t) (Pis : Prov.t) : Prop :=
      PkgSet.Subset Rp R /\ Prov.Subset Pis Pi /\ PkgSet.In p Rp /\
      (forall (m : N.t) vt,
          Prov.In (p, (m, vt)) Pi -> Prov.In (p, (m, vt)) Pis).

    (* A slice that keeps p's own group, p's own negatives, and every
       negative naming something p answers to. *)
    Definition ConfSlice (R : PkgSet.t) (G : Conf.t) (ns : NSet.t)
        (p : Pkg.t) (Rc : PkgSet.t) (Gs : Conf.t) : Prop :=
      PkgSet.Subset Rc R /\ Conf.Subset Gs G /\ PkgSet.In p Rc /\
      (forall q, PkgSet.In q R -> pname q = pname p -> PkgSet.In q Rc) /\
      (forall e, Conf.In e G -> fst e = p -> Conf.In e Gs) /\
      (forall e, Conf.In e G -> NSet.In (aname (snd e)) ns -> Conf.In e Gs).

    Lemma reduceProvEntry_shape : forall M (p0 : Pkg.t) (m0 : N.t) vt0
        (q : Deb.Pkg.t) (mx : QN.t) vt,
        List.In (q, (mx, vt)) (reduceProvEntry M (p0, (m0, vt0))) ->
        q = embedPkg p0 /\ fst mx = m0.
    Proof.
      intros M p0 m0 vt0 q mx vt H.
      unfold reduceProvEntry in H; cbn [fst snd] in H.
      destruct (classOf M p0);
        [ destruct H as [E | []] | destruct H as [E | []]
        | apply in_map_iff in H; destruct H as [b [E _]]
        | destruct H as [E | [E | []]] ];
        injection E as <- <- <-; cbn [fst]; split; reflexivity.
    Qed.

    Lemma implProvOf_shape : forall M (p0 : Pkg.t)
        (q : Deb.Pkg.t) (mx : QN.t) vt,
        List.In (q, (mx, vt)) (implProvOf M p0) ->
        q = embedPkg p0 /\ fst mx = pname p0.
    Proof.
      intros M p0 q mx vt H; unfold implProvOf in H.
      destruct H as [E | H]; [injection E as <- <- <-; split; reflexivity |].
      destruct (classOf M p0); cbn [List.In] in H; try contradiction.
      - apply in_map_iff in H; destruct H as [b [E _]];
          injection E as <- <- <-; split; reflexivity.
      - destruct H as [E | []]; injection E as <- <- <-;
          split; reflexivity.
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

    Lemma reduceProv_node : forall R Pi M ns Rp Pis
        (q : Deb.Pkg.t) (m : N.t) (x : NameArch) vt,
        ProvSlice R Pi ns Rp Pis -> NSet.In m ns ->
        (Deb.Prov.In (q, ((m, x), vt)) (reduceProv R Pi M) <->
         Deb.Prov.In (q, ((m, x), vt)) (reduceProv Rp Pis M)).
    Proof.
      intros R Pi M ns Rp Pis q m x vt [Hr [Hp [Hcr Hcp]]] Hm.
      split; [| exact (reduceProv_mono R Rp Pi Pis M Hr Hp _)].
      rewrite !mem_reduceProv.
      intros [[[e1 [e2 e3]] [He Hl]] | [p0 [Hp0 Hl]]].
      - destruct (reduceProvEntry_shape M e1 e2 e3 q (m, x) vt Hl) as [_ Hn].
        cbn [fst] in Hn.
        left; exists (e1, (e2, e3)); split; [| exact Hl].
        apply (Hcp e1 e2 e3 He); rewrite <- Hn; exact Hm.
      - destruct (implProvOf_shape M p0 q (m, x) vt Hl) as [_ Hn].
        cbn [fst] in Hn.
        right; exists p0; split; [| exact Hl].
        apply (Hcr p0 Hp0); rewrite <- Hn; exact Hm.
    Qed.

    Lemma reduceProv_pkg : forall R Pi M (p : Pkg.t) Rp Pis (mx : QN.t) vt,
        PkgProvSlice R Pi p Rp Pis ->
        (Deb.Prov.In (embedPkg p, (mx, vt)) (reduceProv R Pi M) <->
         Deb.Prov.In (embedPkg p, (mx, vt)) (reduceProv Rp Pis M)).
    Proof.
      intros R Pi M p Rp Pis mx vt [Hr [Hp [Hin Hcp]]].
      split; [| exact (reduceProv_mono R Rp Pi Pis M Hr Hp _)].
      rewrite !mem_reduceProv.
      intros [[[e1 [e2 e3]] [He Hl]] | [p0 [Hp0 Hl]]].
      - destruct (reduceProvEntry_shape M e1 e2 e3 (embedPkg p) mx vt Hl)
          as [Hq _].
        apply embedPkg_injective in Hq; subst e1.
        left; exists (p, (e2, e3)); split; [exact (Hcp e2 e3 He) | exact Hl].
      - destruct (implProvOf_shape M p0 (embedPkg p) mx vt Hl) as [Hq _].
        apply embedPkg_injective in Hq; subst p0.
        right; exists p; split; [exact Hin | exact Hl].
    Qed.

    Lemma provb_restrict : forall R Pi M ns Rp Pis (a' : Deb.Atom.t),
        ProvSlice R Pi ns Rp Pis -> NSet.In (fst (fst a')) ns ->
        Deb.provb (reduceProv Rp Pis M) a' =
        Deb.provb (reduceProv R Pi M) a'.
    Proof.
      intros R Pi M ns Rp Pis [[m x] f] Hsl Hm; cbn [fst] in Hm.
      assert (Hsub := Hsl); destruct Hsub as [Hr [Hp _]].
      unfold Deb.provb.
      apply Deb.Prov.exists_restrict.
      - exact (reduceProv_mono R Rp Pi Pis M Hr Hp).
      - intros [q [mx vt]] Hin Hb; cbn [Deb.aname Deb.aform fst snd] in Hb.
        apply andb_prop in Hb; destruct Hb as [Hn _].
        apply Deb.NEqb.eqb_true_iff in Hn as ->.
        apply (reduceProv_node R Pi M ns Rp Pis q m x vt Hsl Hm); exact Hin.
    Qed.

    Lemma us_restrict : forall R Pi M ns Rr Rp Pis (a' : Deb.Atom.t),
        PkgSet.Subset Rr R ->
        (forall q, PkgSet.In q R -> NSet.In (pname q) ns -> PkgSet.In q Rr) ->
        ProvSlice R Pi ns Rp Pis -> NSet.In (fst (fst a')) ns ->
        Deb.us (reduceReal Rr) (reduceProv Rp Pis M) a' =
        Deb.us (reduceReal R) (reduceProv R Pi M) a'.
    Proof.
      intros R Pi M ns Rr Rp Pis [[m x] f] Hrr Hcr Hsl Hm; cbn [fst] in Hm.
      assert (Hsub := Hsl); destruct Hsub as [Hr [Hp _]].
      assert (Hev : Deb.evalAt (reduceReal Rr) ((m, x), f)
                    = Deb.evalAt (reduceReal R) ((m, x), f)).
      { unfold Deb.evalAt; cbn [Deb.aname Deb.aform fst snd].
        rewrite (realVersions_restrict R Rr (m, x) Hrr); [reflexivity |].
        intros q HqR Hq.
        assert (Hq2 : pname q = m) by exact (f_equal fst Hq).
        apply (Hcr q HqR); rewrite Hq2; exact Hm. }
      apply Deb.T.VSet.ext; intro y; unfold Deb.us.
      rewrite !Deb.T.VSet.union_spec, Hev.
      apply or_iff_compat_l.
      apply Deb.SOew.filterMap_restrict.
      - exact (reduceProv_mono R Rp Pi Pis M Hr Hp).
      - intros [q [mx vt]] Hin Hf; cbn [fst snd Deb.aname Deb.aform] in Hf.
        destruct (Deb.NEqb.eqb mx (m, x)) eqn:Hn; [| discriminate Hf].
        apply Deb.NEqb.eqb_true_iff in Hn as ->.
        apply (reduceProv_node R Pi M ns Rp Pis q m x vt Hsl Hm); exact Hin.
    Qed.

    Lemma tgt_restrict : forall R Pi M ns Rr Rp Pis (a' : Deb.Atom.t),
        PkgSet.Subset Rr R ->
        (forall q, PkgSet.In q R -> NSet.In (pname q) ns -> PkgSet.In q Rr) ->
        ProvSlice R Pi ns Rp Pis -> NSet.In (fst (fst a')) ns ->
        Deb.tgt (reduceReal Rr) (reduceProv Rp Pis M) a' =
        Deb.tgt (reduceReal R) (reduceProv R Pi M) a'.
    Proof.
      intros R Pi M ns Rr Rp Pis a' Hrr Hcr Hsl Hm; unfold Deb.tgt.
      rewrite (provb_restrict R Pi M ns Rp Pis a' Hsl Hm),
        (us_restrict R Pi M ns Rr Rp Pis a' Hrr Hcr Hsl Hm).
      destruct (Deb.provb (reduceProv R Pi M) a'); [reflexivity |].
      unfold Deb.evalAt.
      rewrite (realVersions_restrict R Rr (Deb.aname a') Hrr); [reflexivity |].
      intros q HqR Hq.
      assert (Hq2 : pname q = fst (fst a')) by exact (f_equal fst Hq).
      apply (Hcr q HqR); rewrite Hq2; exact Hm.
    Qed.

    Lemma matchb_restrict : forall R Pi M (p : Pkg.t) Rp Pis (a' : Deb.Atom.t),
        PkgProvSlice R Pi p Rp Pis ->
        Deb.matchb (reduceProv Rp Pis M) (embedPkg p) a' =
        Deb.matchb (reduceProv R Pi M) (embedPkg p) a'.
    Proof.
      intros R Pi M p Rp Pis a' Hsl.
      assert (Hsub := Hsl); destruct Hsub as [Hr [Hp _]].
      unfold Deb.matchb; f_equal.
      apply Deb.Prov.exists_restrict.
      - exact (reduceProv_mono R Rp Pi Pis M Hr Hp).
      - intros [q [mx vt]] Hin Hb; cbn [fst snd Deb.aname Deb.aform] in Hb.
        apply andb_prop in Hb; destruct Hb as [Hq _].
        apply Deb.PkgEqb.eqb_true_iff in Hq as ->.
        apply (reduceProv_pkg R Pi M p Rp Pis mx vt Hsl); exact Hin.
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

    Lemma reduceConf_owner : forall R G M (q : Deb.Pkg.t) ea z,
        Deb.Conf.In (q, (ea, z)) (reduceConf R G M) ->
        exists p : Pkg.t, q = embedPkg p.
    Proof.
      intros R G M q ea z H; rewrite mem_reduceConf in H.
      destruct H as [[[p0 a0] [_ Hl]] | [p0 [_ He]]].
      - exists p0; exact (reduceConfEntry_pkg p0 a0 q ea z Hl).
      - exists p0; rewrite (implConfOf_pkg M p0) in He.
        exact (f_equal fst He).
    Qed.

    Lemma reduceConf_pkg : forall R G M (p : Pkg.t) Rc Gs ea z,
        PkgSet.Subset Rc R -> Conf.Subset Gs G -> PkgSet.In p Rc ->
        (forall e, Conf.In e G -> fst e = p -> Conf.In e Gs) ->
        (Deb.Conf.In (embedPkg p, (ea, z)) (reduceConf R G M) <->
         Deb.Conf.In (embedPkg p, (ea, z)) (reduceConf Rc Gs M)).
    Proof.
      intros R G M p Rc Gs ea z Hr Hg Hin Hown.
      split; [| exact (reduceConf_mono R Rc G Gs M Hr Hg _)].
      rewrite !mem_reduceConf.
      intros [[[p0 a0] [He Hl]] | [p0 [Hp0 He]]].
      - pose proof (reduceConfEntry_pkg p0 a0 (embedPkg p) ea z Hl) as Hq.
        apply embedPkg_injective in Hq; subst p0.
        left; exists (p, a0); split;
          [exact (Hown (p, a0) He eq_refl) | exact Hl].
      - rewrite (implConfOf_pkg M p0) in He.
        pose proof (f_equal fst He) as Hq; cbn [fst] in Hq.
        apply embedPkg_injective in Hq; subst p0.
        right; exists p; split; [exact Hin |].
        rewrite (implConfOf_pkg M p); exact He.
    Qed.

    (* A mangled atom that p answers to names p's own base name or one of
       p's declared Provides: nothing else reaches p. *)
    Lemma match_name : forall R Pi M (p : Pkg.t) (m : N.t) (x : NameArch) f,
        PkgSet.In p R ->
        Deb.Match (reduceProv R Pi M) (embedPkg p) ((m, x), f) ->
        m = pname p \/ exists vt, Prov.In (p, (m, vt)) Pi.
    Proof.
      intros R Pi M p m x f HpR HM.
      apply (debMatch_char R Pi M p m x f HpR) in HM.
      destruct x as [b | |].
      - destruct HM as [[[Hn _] | [vt [Hin _]]] _];
          [left; symmetry; exact Hn | right; exists vt; exact Hin].
      - destruct HM as [[[Hn _] | [vt [Hin _]]] _];
          [left; symmetry; exact Hn | right; exists vt; exact Hin].
      - destruct HM as [Hn _]; left; symmetry; exact Hn.
    Qed.

    Lemma reduceConf_target : forall R Pi G M ns (p : Pkg.t) Rc Gs
        (q : Deb.Pkg.t) (ea : Deb.Atom.t) z,
        PkgSet.In p R -> ConfSlice R G ns p Rc Gs ->
        NSet.In (pname p) ns ->
        (forall (m : N.t) vt, Prov.In (p, (m, vt)) Pi -> NSet.In m ns) ->
        Deb.Match (reduceProv R Pi M) (embedPkg p) ea ->
        (Deb.Conf.In (q, (ea, z)) (reduceConf R G M) <->
         Deb.Conf.In (q, (ea, z)) (reduceConf Rc Gs M)).
    Proof.
      intros R Pi G M ns p Rc Gs q [[m x] f] z HpR
        [Hr [Hg [_ [Hgrp [_ Hname]]]]] Hpn Hprov HM.
      split; [| exact (reduceConf_mono R Rc G Gs M Hr Hg _)].
      rewrite !mem_reduceConf.
      intros [[[p0 a0] [He Hl]] | [p0 [Hp0 He]]].
      - pose proof (reduceConfEntry_name p0 a0 q ((m, x), f) z Hl) as Hn.
        cbn [fst] in Hn.
        left; exists (p0, a0); split; [| exact Hl].
        apply (Hname (p0, a0) He); cbn [snd]; rewrite <- Hn.
        destruct (match_name R Pi M p m x f HpR HM) as [Hm | [vt Hvt]].
        + rewrite Hm; exact Hpn.
        + exact (Hprov m vt Hvt).
      - right; exists p0; split; [| exact He].
        pose proof (f_equal (fun e => fst (fst (snd e))) He) as Hn.
        cbn [fst snd] in Hn.
        rewrite (implConfOf_atomName M p0) in Hn; cbn [fst] in Hn.
        pose proof (f_equal snd Hn) as Hx; cbn [snd] in Hx.
        pose proof (f_equal fst Hn) as Hm; cbn [fst] in Hm.
        subst x.
        destruct (proj1 (debMatch_char R Pi M p m QAGroup f HpR) HM)
          as [Hpm _].
        apply (Hgrp p0 Hp0); rewrite <- Hm; symmetry; exact Hpm.
    Qed.

    Lemma embedPkg_eq : forall (q : Pkg.t) (n : N.t) (x : NameArch) (v : V.t),
        ((n, x), v) = embedPkg q ->
        x = QAArch (parch q) /\ n = pname q /\ v = pver q.
    Proof.
      intros q n x v H.
      pose proof (f_equal fst H) as Hf; pose proof (f_equal snd H) as Hs.
      cbn [fst snd] in Hf, Hs.
      pose proof (f_equal fst Hf) as Hn; pose proof (f_equal snd Hf) as Hx.
      cbn [fst snd] in Hn, Hx.
      split; [exact Hx | split; [exact Hn | exact Hs]].
    Qed.

    Lemma groupOf_sub : forall R ns, PkgSet.Subset (groupOf R ns) R.
    Proof.
      intros R ns q Hq; exact (proj1 (proj1 (mem_groupOf R ns q) Hq)).
    Qed.

    Lemma groupOf_cov : forall R ns q,
        PkgSet.In q R -> NSet.In (pname q) ns -> PkgSet.In q (groupOf R ns).
    Proof. intros R ns q H1 H2; apply mem_groupOf; split; assumption. Qed.

    Lemma provOf_sub : forall Pi ns, Prov.Subset (provOf Pi ns) Pi.
    Proof.
      intros Pi ns [q [m vt]] He;
        exact (proj1 (proj1 (mem_provOf Pi ns q m vt) He)).
    Qed.

    Lemma groupProvSlice : forall R Pi ns,
        ProvSlice R Pi ns (groupOf R ns) (provOf Pi ns).
    Proof.
      intros R Pi ns; unfold ProvSlice; repeat split.
      - apply groupOf_sub.
      - apply provOf_sub.
      - apply groupOf_cov.
      - intros q m vt He Hm; apply mem_provOf; split; assumption.
    Qed.

    Module SOan := SetOps Atom N AtomSet NSet.
    Definition clauseNames (Al : AtomSet.t) : NSet.t := SOan.map aname Al.

    Lemma mem_clauseNames : forall Al (m : N.t),
        NSet.In m (clauseNames Al) <->
        exists a, AtomSet.In a Al /\ aname a = m.
    Proof.
      intros Al m; unfold clauseNames; rewrite SOan.mem_map.
      split; intros [a [Ha Hm]]; exists a; split;
        solve [exact Ha | symmetry; exact Hm].
    Qed.

    Module SOcn := SetOps ClauseElt N Deps NSet.
    (* The base names p's own clauses mention: a dependency atom's mangled
       name only ever qualifies one of these. *)
    Definition atomNames (D : Deps.t) (p : Pkg.t) : NSet.t :=
      SOcn.unionMap (fun c =>
          if Pkg.eq_dec (fst c) p then clauseNames (snd c) else NSet.empty)
        D.

    Lemma mem_atomNames : forall D (p : Pkg.t) (m : N.t),
        NSet.In m (atomNames D p) <->
        exists Al, Deps.In (p, Al) D /\ NSet.In m (clauseNames Al).
    Proof.
      intros D p m; unfold atomNames; rewrite SOcn.mem_unionMap.
      split.
      - intros [[q Al] [Hc Hm]]; cbn [fst snd] in Hm.
        destruct (Pkg.eq_dec q p) as [-> | NE];
          [| exfalso; exact (SOcn.empty_in _ Hm)].
        exists Al; split; assumption.
      - intros [Al [Hc Hm]]; exists (p, Al); split; [exact Hc | cbn [fst snd]].
        destruct (Pkg.eq_dec p p) as [_ | NE];
          [exact Hm | contradiction NE; reflexivity].
    Qed.

    Module SOpn := SetOps ProvElt N Prov NSet.
    Definition provNames (Pi : Prov.t) (p : Pkg.t) : NSet.t :=
      SOpn.filterMap (fun e =>
          if Pkg.eq_dec (fst e) p then Some (fst (snd e)) else None) Pi.

    Lemma mem_provNames : forall Pi (p : Pkg.t) (m : N.t),
        NSet.In m (provNames Pi p) <-> exists vt, Prov.In (p, (m, vt)) Pi.
    Proof.
      intros Pi p m; unfold provNames; rewrite SOpn.mem_filterMap.
      split.
      - intros [[q [m0 vt]] [He Hf]]; cbn [fst snd] in Hf.
        destruct (Pkg.eq_dec q p) as [-> | NE]; [| discriminate].
        injection Hf as <-; exists vt; exact He.
      - intros [vt He]; exists (p, (m, vt)); split; [exact He | cbn [fst snd]].
        destruct (Pkg.eq_dec p p) as [_ | NE];
          [reflexivity | contradiction NE; reflexivity].
    Qed.

    Lemma singleton_clause : forall (p : Pkg.t) Al,
        Deps.In (p, Al) (Deps.singleton (p, Al)).
    Proof. intros p Al; apply Deps.singleton_spec; reflexivity. Qed.

    Lemma hasClauseb_reduceDeps : forall D (p : Pkg.t) Al,
        Deps.In (p, Al) D ->
        Deb.hasClauseb (reduceDeps D) (reduceClause (parch p) Al) = true.
    Proof.
      intros D p Al HD; apply Deb.hasClauseb_iff.
      exists (embedPkg p); rewrite mem_reduceDeps.
      exists p, Al; split; [exact HD | reflexivity].
    Qed.

    Lemma occursAtomb_reduceDeps : forall D (p : Pkg.t) Al a,
        Deps.In (p, Al) D -> AtomSet.In a Al ->
        Deb.occursAtomb (reduceDeps D) (reduceAtom (parch p) a) = true.
    Proof.
      intros D p Al a HD Ha; apply Deb.occursAtomb_iff.
      exists (embedPkg p), (reduceClause (parch p) Al); split.
      - rewrite mem_reduceDeps; exists p, Al; split; [exact HD | reflexivity].
      - unfold reduceClause; rewrite SOcl.mem_map;
          exists a; split; [exact Ha | reflexivity].
    Qed.

    Lemma reduceDeps_fibre : forall D (p : Pkg.t) A,
        Deb.Deps.In (embedPkg p, A) (reduceDeps D) <->
        Deb.Deps.In (embedPkg p, A) (reduceDeps (depsOf D p)).
    Proof.
      intros D p A; rewrite !mem_reduceDeps; split.
      - intros [p0 [Al [HD Heq]]].
        pose proof (f_equal fst Heq) as Hf; cbn [fst] in Hf.
        apply embedPkg_injective in Hf; subst p0.
        exists p, Al; split; [| exact Heq].
        apply mem_depsOf; split; [exact HD | reflexivity].
      - intros [p0 [Al [HD Heq]]].
        apply mem_depsOf in HD; destruct HD as [HD _].
        exists p0, Al; split; [exact HD | exact Heq].
    Qed.

    Lemma reduceDeps_atomNames : forall D (p : Pkg.t) A (a' : Deb.Atom.t),
        Deb.Deps.In (embedPkg p, A) (reduceDeps D) ->
        Deb.AtomSet.In a' A ->
        NSet.In (fst (fst a')) (atomNames D p).
    Proof.
      intros D p A a' HA Ha.
      rewrite mem_reduceDeps in HA; destruct HA as [p0 [Al [HD Heq]]].
      pose proof (f_equal fst Heq) as Hf; cbn [fst] in Hf.
      apply embedPkg_injective in Hf; subst p0.
      pose proof (f_equal snd Heq) as Hs; cbn [snd] in Hs; subst A.
      unfold reduceClause in Ha; rewrite SOcl.mem_map in Ha.
      destruct Ha as [a0 [Ha0 ->]].
      apply mem_atomNames; exists Al; split; [exact HD |].
      apply mem_clauseNames; exists a0; split; [exact Ha0 | reflexivity].
    Qed.

    (* Real packages live only at QAArch names, so the arch fibre of one
       mangled name is the whole slice a versions query at it can read. *)
    Theorem versions_lookupOrigMA : forall R D Pi G M (n : N.t) (b : A.t),
        Deb.versions (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M) (Deb.Name.Orig (n, QAArch b)) =
        Deb.versions (reduceReal (realAt R n b)) Deb.Deps.empty
          Deb.Prov.empty Deb.Conf.empty (Deb.Name.Orig (n, QAArch b)).
    Proof.
      intros R D Pi G M n b; apply Deb.T.VSet.ext; intro w.
      rewrite !Deb.versions_orig_spec.
      split; intros [v [Hv Hw]]; exists v; (split; [| exact Hw]);
        rewrite mem_reduceReal in Hv |- *;
        destruct Hv as [q [HqR Hq]]; exists q; (split; [| exact Hq]).
      - apply mem_realAt; split; [exact HqR |].
        destruct (embedPkg_eq q n (QAArch b) v Hq) as [Hx [Hn _]].
        injection Hx as Hb.
        destruct q as [[qn qb] qv]; unfold pname, parch in Hn, Hb;
          cbn [fst snd] in Hn, Hb; subst; reflexivity.
      - exact (proj1 (proj1 (mem_realAt R n b q) HqR)).
    Qed.

    Theorem versions_lookupOrigMA_pseudo :
      forall R D Pi G M (n : N.t) (x : NameArch),
        (forall b, x <> QAArch b) ->
        Deb.versions (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M) (Deb.Name.Orig (n, x)) = Deb.T.VSet.empty.
    Proof.
      intros R D Pi G M n x Hx; apply Deb.T.VSet.ext; intro w.
      rewrite Deb.versions_orig_spec.
      split.
      - intros [v [Hv _]]; exfalso.
        destruct (reduceReal_arch R (n, x) v Hv) as [b Hb]; cbn [snd] in Hb.
        exact (Hx b Hb).
      - intro Hw; exfalso; exact (Deb.SOvw.empty_in _ Hw).
    Qed.

    Theorem versions_lookupDisjunctMA : forall R D Pi G M (p : Pkg.t) Al,
        Deps.In (p, Al) D ->
        Deb.versions (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M)
          (Deb.Name.Disjunct (reduceClause (parch p) Al)) =
        Deb.versions Deb.PkgSet.empty (reduceDeps (Deps.singleton (p, Al)))
          Deb.Prov.empty Deb.Conf.empty
          (Deb.Name.Disjunct (reduceClause (parch p) Al)).
    Proof.
      intros R D Pi G M p Al HD; apply Deb.T.VSet.ext; intro w.
      rewrite !Deb.versions_disjunct_spec,
        (hasClauseb_reduceDeps D p Al HD),
        (hasClauseb_reduceDeps (Deps.singleton (p, Al)) p Al
           (singleton_clause p Al)).
      reflexivity.
    Qed.

    (* An atom's providers are its base name's whole group across
       architectures, plus that name's declared providers. *)
    Theorem versions_lookupSelectorMA :
      forall R D Pi G M (p : Pkg.t) Al (a : Atom.t),
        Deps.In (p, Al) D -> AtomSet.In a Al ->
        Deb.versions (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M) (Deb.Name.Selector (reduceAtom (parch p) a)) =
        Deb.versions (reduceReal (groupOf R (NSet.singleton (aname a))))
          (reduceDeps (Deps.singleton (p, Al)))
          (reduceProv (groupOf R (NSet.singleton (aname a)))
             (provOf Pi (NSet.singleton (aname a))) M)
          Deb.Conf.empty (Deb.Name.Selector (reduceAtom (parch p) a)).
    Proof.
      intros R D Pi G M p Al a HD Ha.
      assert (Hm : NSet.In (fst (fst (reduceAtom (parch p) a)))
                     (NSet.singleton (aname a)))
        by (apply NSet.singleton_spec; reflexivity).
      apply Deb.T.VSet.ext; intro w.
      rewrite !Deb.versions_selector_spec,
        (occursAtomb_reduceDeps D p Al a HD Ha),
        (occursAtomb_reduceDeps (Deps.singleton (p, Al)) p Al a
           (singleton_clause p Al) Ha),
        (provb_restrict R Pi M (NSet.singleton (aname a))
           (groupOf R (NSet.singleton (aname a)))
           (provOf Pi (NSet.singleton (aname a)))
           (reduceAtom (parch p) a) (groupProvSlice R Pi _) Hm),
        (us_restrict R Pi M (NSet.singleton (aname a))
           (groupOf R (NSet.singleton (aname a)))
           (groupOf R (NSet.singleton (aname a)))
           (provOf Pi (NSet.singleton (aname a)))
           (reduceAtom (parch p) a) (groupOf_sub R _) (groupOf_cov R _)
           (groupProvSlice R Pi _) Hm).
      reflexivity.
    Qed.

    Theorem versions_lookupGuardMA : forall R D Pi G M (q : Pkg.t) ea z,
        PkgSet.In q R ->
        Deb.versions (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M) (Deb.Name.Guard (embedPkg q) ea z) =
        Deb.versions Deb.PkgSet.empty Deb.Deps.empty Deb.Prov.empty
          (reduceConf (PkgSet.singleton q) (confBy G q) M)
          (Deb.Name.Guard (embedPkg q) ea z).
    Proof.
      intros R D Pi G M q ea z HqR.
      assert (Hr : PkgSet.Subset (PkgSet.singleton q) R).
      { intros y Hy; apply PkgSet.singleton_spec in Hy; subst y; exact HqR. }
      assert (Hg : Conf.Subset (confBy G q) G).
      { intros [y1 y2] Hy; exact (proj1 (proj1 (mem_confBy G q y1 y2) Hy)). }
      assert (Hin : PkgSet.In q (PkgSet.singleton q))
        by (apply PkgSet.singleton_spec; reflexivity).
      assert (Hown : forall e,
                 Conf.In e G -> fst e = q -> Conf.In e (confBy G q)).
      { intros [y1 y2] He Hy; cbn [fst] in Hy;
          apply mem_confBy; split; [exact He | exact Hy]. }
      apply Deb.T.VSet.ext; intro w.
      rewrite !Deb.versions_guard_spec.
      split; intros [Hc Hw]; split; try exact Hw.
      - exact (proj1 (reduceConf_pkg R G M q (PkgSet.singleton q)
                        (confBy G q) ea z Hr Hg Hin Hown) Hc).
      - exact (proj2 (reduceConf_pkg R G M q (PkgSet.singleton q)
                        (confBy G q) ea z Hr Hg Hin Hown) Hc).
    Qed.

    Theorem versions_lookupGuardMA_pseudo :
      forall R D Pi G M (n : N.t) (x : NameArch) (v : V.t) ea z,
        (forall b, x <> QAArch b) ->
        Deb.versions (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M) (Deb.Name.Guard ((n, x), v) ea z) =
        Deb.T.VSet.empty.
    Proof.
      intros R D Pi G M n x v ea z Hx; apply Deb.T.VSet.ext; intro w.
      rewrite Deb.versions_guard_spec.
      split.
      - intros [Hc _]; exfalso.
        destruct (reduceConf_owner R G M ((n, x), v) ea z Hc) as [p Hp].
        destruct (embedPkg_eq p n x v Hp) as [Hxx _].
        exact (Hx (parch p) Hxx).
      - intro Hw; exfalso; exact (Deb.SOvw.empty_in _ Hw).
    Qed.

    Theorem dependees_lookupDisjunctMA :
      forall R D Pi G M (p : Pkg.t) Al (a' : Deb.Atom.t),
        Deps.In (p, Al) D ->
        Deb.dependees (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M)
          (Deb.Name.Disjunct (reduceClause (parch p) Al),
           Deb.Version.Atom a') =
        Deb.dependees
          (reduceReal (groupOf R (NSet.singleton (fst (fst a')))))
          (reduceDeps (Deps.singleton (p, Al)))
          (reduceProv (groupOf R (NSet.singleton (fst (fst a'))))
             (provOf Pi (NSet.singleton (fst (fst a')))) M)
          Deb.Conf.empty
          (Deb.Name.Disjunct (reduceClause (parch p) Al),
           Deb.Version.Atom a').
    Proof.
      intros R D Pi G M p Al a' HD.
      assert (Hm : NSet.In (fst (fst a')) (NSet.singleton (fst (fst a'))))
        by (apply NSet.singleton_spec; reflexivity).
      apply Deb.T.DependeesSet.ext; intro y.
      rewrite !Deb.dependees_disjunct_spec,
        (hasClauseb_reduceDeps D p Al HD),
        (hasClauseb_reduceDeps (Deps.singleton (p, Al)) p Al
           (singleton_clause p Al)),
        (tgt_restrict R Pi M (NSet.singleton (fst (fst a')))
           (groupOf R (NSet.singleton (fst (fst a'))))
           (groupOf R (NSet.singleton (fst (fst a'))))
           (provOf Pi (NSet.singleton (fst (fst a')))) a'
           (groupOf_sub R _) (groupOf_cov R _) (groupProvSlice R Pi _) Hm).
      reflexivity.
    Qed.

    (* every candidate shape at once: a provided and a real candidate under
       the same selector read the same slice, and the rest are empty *)
    Theorem dependees_lookupSelectorMA :
      forall R D Pi G M (p : Pkg.t) Al (a : Atom.t) (y : Deb.Version.t),
        Deps.In (p, Al) D -> AtomSet.In a Al ->
        Deb.dependees (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M)
          (Deb.Name.Selector (reduceAtom (parch p) a), y) =
        Deb.dependees (reduceReal (groupOf R (NSet.singleton (aname a))))
          (reduceDeps (Deps.singleton (p, Al)))
          (reduceProv (groupOf R (NSet.singleton (aname a)))
             (provOf Pi (NSet.singleton (aname a))) M)
          Deb.Conf.empty
          (Deb.Name.Selector (reduceAtom (parch p) a), y).
    Proof.
      intros R D Pi G M p Al a y HD Ha.
      assert (Hm : NSet.In (fst (fst (reduceAtom (parch p) a)))
                     (NSet.singleton (aname a)))
        by (apply NSet.singleton_spec; reflexivity).
      assert (Ho := occursAtomb_reduceDeps D p Al a HD Ha).
      assert (Ho1 := occursAtomb_reduceDeps (Deps.singleton (p, Al)) p Al a
                       (singleton_clause p Al) Ha).
      assert (Hpb := provb_restrict R Pi M (NSet.singleton (aname a))
                       (groupOf R (NSet.singleton (aname a)))
                       (provOf Pi (NSet.singleton (aname a)))
                       (reduceAtom (parch p) a) (groupProvSlice R Pi _) Hm).
      assert (Hus := us_restrict R Pi M (NSet.singleton (aname a))
                       (groupOf R (NSet.singleton (aname a)))
                       (groupOf R (NSet.singleton (aname a)))
                       (provOf Pi (NSet.singleton (aname a)))
                       (reduceAtom (parch p) a) (groupOf_sub R _)
                       (groupOf_cov R _) (groupProvSlice R Pi _) Hm).
      destruct y; try reflexivity;
        apply Deb.T.DependeesSet.ext; intro z.
      - rewrite !Deb.dependees_selector_spec, Ho, Ho1, Hpb, Hus; reflexivity.
      - rewrite !Deb.dependees_selector_real_spec, Ho, Ho1, Hpb, Hus;
          reflexivity.
    Qed.

    Theorem dependees_lookupGuardMA :
      forall R D Pi G M (pq : Deb.Pkg.t) (ea : Deb.Atom.t) z w,
        Deb.dependees (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M) (Deb.Name.Guard pq ea z, w) =
        Deb.T.DependeesSet.empty.
    Proof.
      intros R D Pi G M pq ea z w; apply Deb.Lookup.dependees_lookupGuard.
    Qed.

    (* The crux: p's own row pulls three slices. Dependency targets need the
       whole group of every base name p's clauses mention (implicit group,
       foreign and :any provides come from any architecture's member);
       matchb at p needs p itself and p's own Provides in the reduceProv
       carrier; and the conflicts that can reach p are p's own negatives,
       every negative naming p's name or something p provides, and the
       implicit group exclusions of p's own group. *)
    Theorem dependees_lookupOrigMA : forall R D Pi G M (p : Pkg.t),
        PkgSet.In p R ->
        Deb.dependees (reduceReal R) (reduceDeps D) (reduceProv R Pi M)
          (reduceConf R G M) (Deb.embedPkg (embedPkg p)) =
        Deb.dependees (reduceReal (groupOf R (atomNames D p)))
          (reduceDeps (depsOf D p))
          (reduceProv (PkgSet.add p (groupOf R (atomNames D p)))
             (Prov.union (provOf Pi (atomNames D p)) (provBy Pi p)) M)
          (reduceConf (PkgSet.add p (groupOf R (NSet.singleton (pname p))))
             (Conf.union (confBy G p)
                (confOn G (NSet.add (pname p) (provNames Pi p)))) M)
          (Deb.embedPkg (embedPkg p)).
    Proof.
      intros R D Pi G M p HpR.
      set (ns := atomNames D p).
      set (Rr := groupOf R ns).
      set (Rp := PkgSet.add p Rr).
      set (Pis := Prov.union (provOf Pi ns) (provBy Pi p)).
      set (ns2 := NSet.add (pname p) (provNames Pi p)).
      set (Rc := PkgSet.add p (groupOf R (NSet.singleton (pname p)))).
      set (Gs := Conf.union (confBy G p) (confOn G ns2)).
      assert (HRr : PkgSet.Subset Rr R) by apply groupOf_sub.
      assert (HcovR : forall q, PkgSet.In q R -> NSet.In (pname q) ns ->
                        PkgSet.In q Rr) by apply groupOf_cov.
      assert (HRp : PkgSet.Subset Rp R).
      { intros q Hq; apply PkgSet.add_spec in Hq;
          destruct Hq as [-> | Hq]; [exact HpR | exact (HRr _ Hq)]. }
      assert (HPis : Prov.Subset Pis Pi).
      { intros [q [m vt]] He; apply Prov.union_spec in He;
          destruct He as [He | He];
          [ exact (proj1 (proj1 (mem_provOf Pi ns q m vt) He))
          | exact (proj1 (proj1 (mem_provBy Pi p q m vt) He)) ]. }
      assert (Hsl : ProvSlice R Pi ns Rp Pis).
      { unfold ProvSlice; repeat split;
          [ exact HRp | exact HPis
          | intros q Hq Hn; apply PkgSet.add_spec; right;
            exact (HcovR q Hq Hn)
          | intros q m vt He Hn; apply Prov.union_spec; left;
            apply mem_provOf; split; [exact He | exact Hn] ]. }
      assert (Hpsl : PkgProvSlice R Pi p Rp Pis).
      { unfold PkgProvSlice; repeat split;
          [ exact HRp | exact HPis
          | apply PkgSet.add_spec; left; reflexivity
          | intros m vt He; apply Prov.union_spec; right;
            apply mem_provBy; split; [exact He | reflexivity] ]. }
      assert (Hinp : PkgSet.In p Rc)
        by (apply PkgSet.add_spec; left; reflexivity).
      assert (HRc : PkgSet.Subset Rc R).
      { intros q Hq; apply PkgSet.add_spec in Hq;
          destruct Hq as [-> | Hq];
          [exact HpR | exact (groupOf_sub R _ q Hq)]. }
      assert (HGs : Conf.Subset Gs G).
      { intros [q a0] He; apply Conf.union_spec in He;
          destruct He as [He | He];
          [ exact (proj1 (proj1 (mem_confBy G p q a0) He))
          | exact (proj1 (proj1 (mem_confOn G ns2 (q, a0)) He)) ]. }
      assert (Hown : forall e, Conf.In e G -> fst e = p -> Conf.In e Gs).
      { intros [q a0] He Hq; cbn [fst] in Hq; apply Conf.union_spec; left;
          apply mem_confBy; split; [exact He | exact Hq]. }
      assert (Hgrp : forall q, PkgSet.In q R -> pname q = pname p ->
                       PkgSet.In q Rc).
      { intros q Hq Hn; apply PkgSet.add_spec; right;
          apply groupOf_cov; [exact Hq | apply NSet.singleton_spec; exact Hn]. }
      assert (Hname : forall e, Conf.In e G ->
                        NSet.In (aname (snd e)) ns2 -> Conf.In e Gs).
      { intros e He Hn; apply Conf.union_spec; right;
          apply mem_confOn; split; [exact He | exact Hn]. }
      assert (Hcsl : ConfSlice R G ns2 p Rc Gs)
        by (unfold ConfSlice; repeat split; assumption).
      assert (Hpn : NSet.In (pname p) ns2)
        by (apply NSet.add_spec; left; reflexivity).
      assert (Hprovns : forall (m : N.t) vt,
                 Prov.In (p, (m, vt)) Pi -> NSet.In m ns2).
      { intros m vt He; apply NSet.add_spec; right; apply mem_provNames;
          exists vt; exact He. }
      assert (Hmb : forall a' : Deb.Atom.t,
                 Deb.matchb (reduceProv Rp Pis M)
                   ((pname p, QAArch (parch p)), pver p) a'
                 = Deb.matchb (reduceProv R Pi M)
                     ((pname p, QAArch (parch p)), pver p) a')
        by (intro a'; exact (matchb_restrict R Pi M p Rp Pis a' Hpsl)).
      replace (Deb.embedPkg (embedPkg p))
        with (Deb.Name.Orig (pname p, QAArch (parch p)),
              Deb.Version.Orig (pver p)) by reflexivity.
      apply Deb.T.DependeesSet.ext; intro y.
      rewrite !Deb.dependees_orig_spec.
      split.
      - intros [[A [HA Hcase]] |
                [[a0 [z [Ha0 Hy]]] |
                 [m0 [u0 [a0 [z [Hg [Hmbt [Hne [Hex Hy]]]]]]]]]].
        + left; exists A; split;
            [exact (proj1 (reduceDeps_fibre D p A) HA) |].
          destruct Hcase as [[Hcard [a1 [Hmin Hy]]] | [Hcard Hy]].
          * left; split; [exact Hcard |].
            exists a1; split; [exact Hmin |].
            rewrite Hy; symmetry.
            apply (tgt_restrict R Pi M ns Rr Rp Pis a1 HRr HcovR Hsl).
            exact (reduceDeps_atomNames D p A a1 HA
                     (Deb.AtomSet.min_elt_spec1 Hmin)).
          * right; split; [exact Hcard | exact Hy].
        + right; left; exists a0, z; split; [| exact Hy].
          exact (proj1 (reduceConf_pkg R G M p Rc Gs a0 z HRc HGs Hinp Hown)
                   Ha0).
        + right; right; exists m0, u0, a0, z.
          split;
            [ exact (proj1 (reduceConf_target R Pi G M ns2 p Rc Gs
                              (m0, u0) a0 z HpR Hcsl Hpn Hprovns
                              (proj1 (Deb.matchb_iff _ _ _) Hmbt)) Hg)
            | split; [rewrite Hmb; exact Hmbt
                     | split; [exact Hne
                              | split; [exact Hex | exact Hy]]]].
      - intros [[A [HA Hcase]] |
                [[a0 [z [Ha0 Hy]]] |
                 [m0 [u0 [a0 [z [Hg [Hmbt [Hne [Hex Hy]]]]]]]]]].
        + assert (HA' : Deb.Deps.In (embedPkg p, A) (reduceDeps D))
            by exact (proj2 (reduceDeps_fibre D p A) HA).
          left; exists A; split; [exact HA' |].
          destruct Hcase as [[Hcard [a1 [Hmin Hy]]] | [Hcard Hy]].
          * left; split; [exact Hcard |].
            exists a1; split; [exact Hmin |].
            rewrite Hy.
            apply (tgt_restrict R Pi M ns Rr Rp Pis a1 HRr HcovR Hsl).
            exact (reduceDeps_atomNames D p A a1 HA'
                     (Deb.AtomSet.min_elt_spec1 Hmin)).
          * right; split; [exact Hcard | exact Hy].
        + right; left; exists a0, z; split; [| exact Hy].
          exact (proj2 (reduceConf_pkg R G M p Rc Gs a0 z HRc HGs Hinp Hown)
                   Ha0).
        + assert (Hmbt' : Deb.matchb (reduceProv R Pi M)
                            ((pname p, QAArch (parch p)), pver p) a0 = true)
            by (rewrite <- Hmb; exact Hmbt).
          right; right; exists m0, u0, a0, z.
          split;
            [ exact (proj2 (reduceConf_target R Pi G M ns2 p Rc Gs
                              (m0, u0) a0 z HpR Hcsl Hpn Hprovns
                              (proj1 (Deb.matchb_iff _ _ _) Hmbt')) Hg)
            | split; [exact Hmbt'
                     | split; [exact Hne
                              | split; [exact Hex | exact Hy]]]].
    Qed.
  End Lookup.
End DebianMA.
