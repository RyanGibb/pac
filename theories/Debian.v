From Stdlib Require Import MSets Lia PeanoNat.
From PackageCalculus Require Import Prelude Core Versions.

Create HintDb cmp_deb.
Create Rewrite HintDb cmp_deb.

(* Name grouping: a decidable equivalence coarser than name equality,
   exempting a conflict owner's whole group from provider matching (dpkg
   treats all instances of a package name as one conflict scope). The
   trivial instance groups nothing beyond equality. *)
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

  (* Pointwise Formula satisfaction v |= phi; Ver.eval is its edge-wise
     form over Ver.realVersions. *)
  Fixpoint vfHolds (f : Ver.Formula) (v : V.t) : bool :=
    match f with
    | Ver.FTop => true
    | Ver.FBot => false
    | Ver.FConj f1 f2 => andb (vfHolds f1 v) (vfHolds f2 v)
    | Ver.FDisj f1 f2 => orb (vfHolds f1 v) (vfHolds f2 v)
    | Ver.FCmp op c => Ver.cmpOpEval op v c
    end.

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
  (* A provider's top version satisfies only the unconstrained Formula. *)
  Definition vtMatchb (vt : DTop) (f : Ver.Formula) : bool :=
    match vt with
    | DTVal v => vfHolds f v
    | DTTop => FEqb.eqb f Ver.FTop
    end.

  Module Atom := PairUOT N Ver.FOT.

  Definition aname (a : Atom.t) : N.t := fst a.
  Definition aform (a : Atom.t) : Ver.Formula := snd a.

  Module AtomSet := FSetUOT Atom.
  Module ClauseElt := PairUOT Pkg AtomSet.AsUOT.
  Module Deps := FSetUOT ClauseElt.

  Module DTOT := UOTFromCompare DTComp.
  Module Provided := PairUOT N DTOT.
  Module ProvElt := PairUOT Pkg Provided.
  Module Prov := FSetUOT ProvElt.

  (* Conflict entries carry an exemption flag: true exempts the owner's
     whole name group from provider matching (dpkg's conflict scope is the
     package name across instances); implicit entries use false. *)
  Module Conflictees := PairUOT Atom BoolOT.
  Module ConfElt := PairUOT Pkg Conflictees.
  Module Conf := FSetUOT ConfElt.

  Definition Match (Pi : Prov.t) (q : Pkg.t) (a : Atom.t) : Prop :=
    (fst q = aname a /\ vfHolds (aform a) (snd q) = true) \/
    (exists vt, Prov.In (q, (aname a, vt)) Pi /\
       vtMatchb vt (aform a) = true).

  Module NEqb := UOTEqb N.
  Module PkgEqb := UOTEqb Pkg.

  Definition matchb (Pi : Prov.t) (q : Pkg.t) (a : Atom.t) : bool :=
    orb
      (andb (NEqb.eqb (fst q) (aname a)) (vfHolds (aform a) (snd q)))
      (Prov.exists_ (fun '(p, (m, vt)) =>
           andb (PkgEqb.eqb p q)
             (andb (NEqb.eqb m (aname a)) (vtMatchb vt (aform a))))
         Pi).

  Lemma matchb_iff : forall Pi q a, matchb Pi q a = true <-> Match Pi q a.
  Proof.
    intros Pi q a; unfold matchb, Match, aname, aform.
    rewrite Bool.orb_true_iff, Bool.andb_true_iff.
    rewrite Prov.exists_spec'.
    unfold Prov.Exists; split.
    - intros [[He Hv] | [e [He Hb]]].
      + left; split; [apply NEqb.eqb_true_iff; exact He | exact Hv].
      + right; destruct e as [q' [n' vt]]; cbn beta iota in Hb.
        apply andb_prop in Hb; destruct Hb as [Hq Hb].
        apply andb_prop in Hb; destruct Hb as [Hn Hm].
        apply PkgEqb.eqb_true_iff in Hq as ->.
        apply NEqb.eqb_true_iff in Hn as ->.
        exists vt; split; assumption.
    - intros [[He Hv] | [vt [Hin Hm]]].
      + left; split; [apply NEqb.eqb_true_iff; exact He | exact Hv].
      + right; exists (q, (fst a, vt)); split; [exact Hin | cbn [fst snd]].
        rewrite PkgEqb.eqb_refl, NEqb.eqb_refl; cbn [andb]; exact Hm.
  Qed.

  Record IsResolution
      (R : PkgSet.t) (D : Deps.t) (Pi : Prov.t) (G : Conf.t)
      (r : Pkg.t) (S : PkgSet.t) : Prop :=
    { res_subset : PkgSet.Subset S R
    ; res_root_mem : PkgSet.In r S
    ; res_clause_closure :
        forall p, PkgSet.In p S ->
        forall A, Deps.In (p, A) D ->
        exists a, AtomSet.In a A /\
          exists q, PkgSet.In q S /\ Match Pi q a
    ; res_conflict_avoidance :
        forall p, PkgSet.In p S ->
        forall a x, Conf.In (p, (a, x)) G ->
        ~ exists q, PkgSet.In q S /\ q <> p /\
            (x = true -> NG.groupEq (fst q) (fst p) = false) /\
            Match Pi q a
    ; res_version_unique : C.VersionUnique S }.

  Module AtomF := UOTCompareFacts Atom.

  Module NF := UOTCompareFacts N.
  Module ASF := UOTCompareFacts AtomSet.AsUOT.
  Module ConfEltF := UOTCompareFacts ConfElt.
  #[local] Hint Rewrite AtomF.compare_eq_iff NF.compare_eq_iff
    ASF.compare_eq_iff ConfEltF.compare_eq_iff : cmp_deb.
  #[local] Hint Extern 1 => cmp_by AtomF.compare_antisym : cmp_deb.
  #[local] Hint Extern 1 => cmp_by NF.compare_antisym : cmp_deb.
  #[local] Hint Extern 1 => cmp_by ASF.compare_antisym : cmp_deb.
  #[local] Hint Extern 1 => cmp_by ConfEltF.compare_antisym : cmp_deb.
  #[local] Hint Extern 1 => cmp_by AtomF.compare_lt_trans : cmp_deb.
  #[local] Hint Extern 1 => cmp_by NF.compare_lt_trans : cmp_deb.
  #[local] Hint Extern 1 => cmp_by ASF.compare_lt_trans : cmp_deb.
  #[local] Hint Extern 1 => cmp_by ConfEltF.compare_lt_trans : cmp_deb.

  Module Name.
    Inductive name : Type :=
    | Orig (n : N.t)
    | Disjunct (A : AtomSet.t)
    | Selector (a : Atom.t)
    | Guard (p : Pkg.t) (a : Atom.t) (x : bool).
    Definition t := name.

    Definition compare (x y : t) : comparison :=
      match x, y with
      | Orig n1, Orig n2 => N.compare n1 n2
      | Orig _, _ => Lt
      | Disjunct _, Orig _ => Gt
      | Disjunct A1, Disjunct A2 => AtomSet.AsUOT.compare A1 A2
      | Disjunct _, _ => Lt
      | Selector a1, Selector a2 => Atom.compare a1 a2
      | Selector _, Guard _ _ _ => Lt
      | Selector _, _ => Gt
      | Guard p1 a1 x1, Guard p2 a2 x2 =>
          ConfElt.compare (p1, (a1, x1)) (p2, (a2, x2))
      | Guard _ _ _, _ => Gt
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
    (* a candidate whose name is necessarily the selector's own: carrying no
       name is what makes "this one is the real package, not an alias
       claiming its name" unforgeable, and so visible to a comparator that
       sees versions and never the name they hang under *)
    | RefReal (w : V.t)
    | Zero
    | One.
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
      | RefReal _, One => Lt
      | RefReal _, _ => Gt
      | Zero, One => Lt
      | Zero, Zero => Eq
      | Zero, _ => Gt
      | One, One => Eq
      | One, _ => Gt
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
    Ver.eval (aform a) (Ver.realVersions R (aname a)).

  Definition provb (Pi : Prov.t) (a : Atom.t) : bool :=
    Prov.exists_ (fun '(_, (m, vt)) =>
        andb (NEqb.eqb m (aname a)) (vtMatchb vt (aform a)))
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

  Definition tgt (R : PkgSet.t) (Pi : Prov.t) (a : Atom.t) :
      Name.t * T.VSet.t :=
    if provb Pi a
    then (Name.Selector a, us R Pi a)
    else (Name.Orig (aname a), embedVS (evalAt R a)).

  Module SOaw := SetOps Atom VersionOT AtomSet T.VSet.
  Definition versionsDisj (A : AtomSet.t) : T.VSet.t :=
    SOaw.map (fun a => Version.Atom a) A.

  Module ASEqb := UOTEqb AtomSet.AsUOT.
  Definition hasClauseb (D : Deps.t) (A : AtomSet.t) : bool :=
    Deps.exists_ (fun '(_, Al) => ASEqb.eqb Al A) D.

  Definition occursAtomb (D : Deps.t) (a : Atom.t) : bool :=
    Deps.exists_ (fun '(_, A) => AtomSet.mem a A) D.

  Definition exemptb (x : bool) (m n : N.t) : bool :=
    andb x (NG.groupEq m n).

  Definition zeroOne : T.VSet.t :=
    T.VSet.add Version.Zero (T.VSet.singleton Version.One).

  Definition versions (R : PkgSet.t) (D : Deps.t) (Pi : Prov.t)
      (G : Conf.t) (n' : Name.t) : T.VSet.t :=
    match n' with
    | Name.Orig n => embedVS (Ver.realVersions R n)
    | Name.Disjunct A =>
        if andb (hasClauseb D A) (2 <=? AtomSet.cardinal A)
        then versionsDisj A else T.VSet.empty
    | Name.Selector a =>
        if andb (occursAtomb D a) (provb Pi a)
        then us R Pi a else T.VSet.empty
    | Name.Guard p a x =>
        if Conf.mem (p, (a, x)) G then zeroOne else T.VSet.empty
    end.

  Module SOde := SetOps ClauseElt T.Dependees Deps T.DependeesSet.
  Module SOge := SetOps ConfElt T.Dependees Conf T.DependeesSet.
  Definition dependees (R : PkgSet.t) (D : Deps.t) (Pi : Prov.t)
      (G : Conf.t) (s : T.Pkg.t) : T.DependeesSet.t :=
    match s with
    | (Name.Orig n, Version.Orig v) =>
        T.DependeesSet.union
          (SOde.filterMap (fun c =>
               if Pkg.eq_dec (fst c) (n, v)
               then if AtomSet.cardinal (snd c) =? 1
                    then match AtomSet.min_elt (snd c) with
                         | Some a => Some (tgt R Pi a)
                         | None => None
                         end
                    else Some (Name.Disjunct (snd c), versionsDisj (snd c))
               else None)
             D)
          (T.DependeesSet.union
             (SOge.filterMap (fun e =>
                  if Pkg.eq_dec (fst e) (n, v)
                  then Some (Name.Guard (n, v) (fst (snd e)) (snd (snd e)),
                             T.VSet.singleton Version.One)
                  else None)
                G)
             (SOge.filterMap (fun e =>
                  if andb (matchb Pi (n, v) (fst (snd e)))
                       (andb
                          (negb (if Pkg.eq_dec (fst e) (n, v)
                                 then true else false))
                          (negb (exemptb (snd (snd e)) n (fst (fst e)))))
                  then Some (Name.Guard (fst e) (fst (snd e)) (snd (snd e)),
                             T.VSet.singleton Version.Zero)
                  else None)
                G))
    | (Name.Disjunct A, Version.Atom a) =>
        if andb (hasClauseb D A)
             (andb (2 <=? AtomSet.cardinal A) (AtomSet.mem a A))
        then T.DependeesSet.singleton (tgt R Pi a)
        else T.DependeesSet.empty
    | (Name.Selector a, Version.Ref m w) =>
        if andb (occursAtomb D a)
             (andb (provb Pi a) (T.VSet.mem (Version.Ref m w) (us R Pi a)))
        then T.DependeesSet.singleton
               (Name.Orig m, T.VSet.singleton (Version.Orig w))
        else T.DependeesSet.empty
    (* the back edge to a real candidate needs its name, and the constructor
       does not carry one -- it does not have to, since the selector it hangs
       under is the only name it could have had *)
    | (Name.Selector a, Version.RefReal w) =>
        if andb (occursAtomb D a)
             (andb (provb Pi a) (T.VSet.mem (Version.RefReal w) (us R Pi a)))
        then T.DependeesSet.singleton
               (Name.Orig (aname a), T.VSet.singleton (Version.Orig w))
        else T.DependeesSet.empty
    | _ => T.DependeesSet.empty
    end.

  Definition embedPkg (p : Pkg.t) : T.Pkg.t :=
    (Name.Orig (fst p), Version.Orig (snd p)).

  Module SOrp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
  Definition realOrig (R : PkgSet.t) : T.PkgSet.t :=
    SOrp.map embedPkg R.

  Module SOap := SetOps Atom T.Pkg AtomSet T.PkgSet.
  Definition disjunctAtoms (A : AtomSet.t) : T.PkgSet.t :=
    SOap.map (fun a => (Name.Disjunct A, Version.Atom a)) A.

  Module SOcp := SetOps ClauseElt T.Pkg Deps T.PkgSet.
  Definition realDisjunct (D : Deps.t) : T.PkgSet.t :=
    SOcp.unionMap (fun '(_, A) =>
        if 2 <=? AtomSet.cardinal A
        then disjunctAtoms A
        else T.PkgSet.empty)
      D.

  Module SOwp := SetOps VersionOT T.Pkg T.VSet T.PkgSet.
  Definition selectorVers (a : Atom.t) (ws : T.VSet.t) : T.PkgSet.t :=
    SOwp.map (fun w => (Name.Selector a, w)) ws.

  Definition selectorAtoms (R : PkgSet.t) (Pi : Prov.t) (A : AtomSet.t) :
      T.PkgSet.t :=
    SOap.unionMap (fun a =>
        if provb Pi a
        then selectorVers a (us R Pi a)
        else T.PkgSet.empty)
      A.

  Definition realSelector (R : PkgSet.t) (D : Deps.t) (Pi : Prov.t) :
      T.PkgSet.t :=
    SOcp.unionMap (fun '(_, A) => selectorAtoms R Pi A) D.

  Module SOgp := SetOps ConfElt T.Pkg Conf T.PkgSet.
  Definition realGuard (G : Conf.t) : T.PkgSet.t :=
    SOgp.unionMap (fun '(p, (a, x)) =>
        T.PkgSet.add (Name.Guard p a x, Version.Zero)
          (T.PkgSet.singleton (Name.Guard p a x, Version.One)))
      G.

  Definition reduceReal (R : PkgSet.t) (D : Deps.t) (Pi : Prov.t)
      (G : Conf.t) : T.PkgSet.t :=
    T.PkgSet.union (realOrig R)
      (T.PkgSet.union (realDisjunct D)
         (T.PkgSet.union (realSelector R D Pi) (realGuard G))).

  Module SOee := SetOps T.Dependees T.DepElt T.DependeesSet T.DepRel.
  Definition depEdges (s : T.Pkg.t) (es : T.DependeesSet.t) : T.DepRel.t :=
    SOee.map (fun e => (s, e)) es.

  Module SOse := SetOps T.Pkg T.DepElt T.PkgSet T.DepRel.
  Definition reduceDeps (R : PkgSet.t) (D : Deps.t) (Pi : Prov.t)
      (G : Conf.t) : T.DepRel.t :=
    SOse.unionMap (fun s => depEdges s (dependees R D Pi G s))
      (reduceReal R D Pi G).

  Lemma provb_iff : forall Pi (n : N.t) (f : Ver.Formula),
      provb Pi (n, f) = true <->
      exists q vt, Prov.In (q, (n, vt)) Pi /\ vtMatchb vt f = true.
  Proof.
    intros Pi n f; unfold provb.
    rewrite Prov.exists_spec'.
    unfold Prov.Exists; split.
    - intros [e [He Hb]]; destruct e as [q [n' vt]];
        cbn [aname aform fst snd] in Hb.
      apply andb_prop in Hb; destruct Hb as [Hn Hm].
      apply NEqb.eqb_true_iff in Hn as ->.
      exists q, vt; split; assumption.
    - intros [q [vt [Hin Hm]]].
      exists (q, (n, vt)); split; [exact Hin | cbn [aname aform fst snd]].
      rewrite NEqb.eqb_refl; cbn [andb]; exact Hm.
  Qed.

  Lemma mem_us : forall R Pi (n : N.t) (f : Ver.Formula) y,
      T.VSet.In y (us R Pi (n, f)) <->
      (exists u, VSet.In u (evalAt R (n, f)) /\ y = Version.RefReal u) \/
      (exists m u vt, Prov.In ((m, u), (n, vt)) Pi /\
         vtMatchb vt f = true /\ y = Version.Ref m u).
  Proof.
    intros R Pi n f y; unfold us; cbn [aname aform fst snd].
    rewrite T.VSet.union_spec, SOvw.mem_map, SOew.mem_filterMap.
    split.
    - intros [[u [Hu Hy]] | [[[m u] [n' vt]] [He Hy]]].
      + left; exists u; split; assumption.
      + cbn [fst snd] in Hy.
        destruct (andb (NEqb.eqb n' n) (vtMatchb vt f)) eqn:Hc;
          [| discriminate].
        apply andb_prop in Hc; destruct Hc as [Hn Hm].
        apply NEqb.eqb_true_iff in Hn as ->.
        injection Hy as <-.
        right; exists m, u, vt; repeat split; assumption.
    - intros [[u [Hu ->]] | [m [u [vt [Hin [Hm ->]]]]]].
      + left; exists u; split; [exact Hu | reflexivity].
      + right; exists ((m, u), (n, vt)); split;
          [exact Hin | cbn [fst snd]].
        rewrite NEqb.eqb_refl, Hm; reflexivity.
  Qed.

  Lemma hasClauseb_iff : forall D A,
      hasClauseb D A = true <-> exists p, Deps.In (p, A) D.
  Proof.
    intros D A; unfold hasClauseb.
    rewrite Deps.exists_spec'.
    unfold Deps.Exists; split.
    - intros [c [Hc Hb]]; destruct c as [p Al]; cbn beta iota in Hb.
      apply ASEqb.eqb_true_iff in Hb as ->; exists p; exact Hc.
    - intros [p Hc].
      exists (p, A); split; [exact Hc | apply ASEqb.eqb_refl].
  Qed.

  Lemma occursAtomb_iff : forall D a,
      occursAtomb D a = true <->
      exists p Al, Deps.In (p, Al) D /\ AtomSet.In a Al.
  Proof.
    intros D a; unfold occursAtomb.
    rewrite Deps.exists_spec'.
    unfold Deps.Exists; split.
    - intros [c [Hc Hm]]; destruct c as [p Al]; simpl in Hm.
      exists p, Al; split; [exact Hc | apply AtomSet.mem_spec; exact Hm].
    - intros [p [Al [Hc Hm]]].
      exists (p, Al); split; [exact Hc | simpl].
      apply AtomSet.mem_spec; exact Hm.
  Qed.

  Lemma exemptb_iff : forall x (m n : N.t),
      exemptb x m n = false <-> (x = true -> NG.groupEq m n = false).
  Proof.
    intros x m n; unfold exemptb; destruct x; cbn [andb].
    - split; [intros H _; exact H | intro H; exact (H eq_refl)].
    - split; [intros _ H; discriminate H | intros _; reflexivity].
  Qed.

  Lemma mem_zeroOne : forall w,
      T.VSet.In w zeroOne <-> w = Version.Zero \/ w = Version.One.
  Proof.
    intro w; unfold zeroOne.
    rewrite SOvw.add_in, SOvw.singleton_in; reflexivity.
  Qed.

  Lemma mem_realOrig : forall R y,
      T.PkgSet.In y (realOrig R) <->
      exists n v, PkgSet.In (n, v) R /\ y = (Name.Orig n, Version.Orig v).
  Proof.
    intros R y; unfold realOrig; rewrite SOrp.mem_map.
    split.
    - intros [[n v] [Hp Hy]]; unfold embedPkg in Hy; cbn [fst snd] in Hy.
      exists n, v; split; assumption.
    - intros [n [v [Hp ->]]]; exists (n, v); split; [exact Hp | reflexivity].
  Qed.

  Lemma mem_disjunctAtoms : forall A y,
      T.PkgSet.In y (disjunctAtoms A) <->
      exists a, AtomSet.In a A /\ y = (Name.Disjunct A, Version.Atom a).
  Proof.
    intros A y; unfold disjunctAtoms; rewrite SOap.mem_map; tauto.
  Qed.

  Lemma mem_realDisjunct : forall D y,
      T.PkgSet.In y (realDisjunct D) <->
      exists p Al, Deps.In (p, Al) D /\
        (2 <=? AtomSet.cardinal Al) = true /\
        exists a, AtomSet.In a Al /\ y = (Name.Disjunct Al, Version.Atom a).
  Proof.
    intros D y; unfold realDisjunct; rewrite SOcp.mem_unionMap.
    split.
    - intros [[p Al] [Hc Hy]]; cbn beta iota in Hy.
      destruct (2 <=? AtomSet.cardinal Al) eqn:Hcard;
        [| exfalso; exact (SOcp.empty_in _ Hy)].
      apply mem_disjunctAtoms in Hy.
      destruct Hy as [a [Ha Hy]].
      exists p, Al; split; [exact Hc |].
      split; [exact Hcard |].
      exists a; split; assumption.
    - intros [p [Al [Hc [Hcard [a [Ha ->]]]]]].
      exists (p, Al); split; [exact Hc | cbn beta iota].
      rewrite Hcard.
      apply mem_disjunctAtoms.
      exists a; split; [exact Ha | reflexivity].
  Qed.

  Lemma mem_selectorVers : forall a ws y,
      T.PkgSet.In y (selectorVers a ws) <->
      exists w, T.VSet.In w ws /\ y = (Name.Selector a, w).
  Proof.
    intros a ws y; unfold selectorVers; rewrite SOwp.mem_map; tauto.
  Qed.

  Lemma mem_selectorAtoms : forall R Pi A y,
      T.PkgSet.In y (selectorAtoms R Pi A) <->
      exists a, AtomSet.In a A /\ provb Pi a = true /\
        exists w, T.VSet.In w (us R Pi a) /\ y = (Name.Selector a, w).
  Proof.
    intros R Pi A y; unfold selectorAtoms.
    rewrite SOap.mem_unionMap.
    split.
    - intros [a [Ha Hy]]; cbn beta iota in Hy.
      destruct (provb Pi a) eqn:Hp; [| exfalso; exact (SOap.empty_in _ Hy)].
      apply mem_selectorVers in Hy.
      destruct Hy as [w [Hw Hy]].
      exists a; split; [exact Ha |].
      split; [exact Hp |].
      exists w; split; assumption.
    - intros [a [Ha [Hp [w [Hw ->]]]]].
      exists a; split; [exact Ha | cbn beta iota].
      rewrite Hp.
      apply mem_selectorVers.
      exists w; split; [exact Hw | reflexivity].
  Qed.

  Lemma mem_realSelector : forall R D Pi y,
      T.PkgSet.In y (realSelector R D Pi) <->
      exists p Al, Deps.In (p, Al) D /\
        exists a, AtomSet.In a Al /\ provb Pi a = true /\
          exists w, T.VSet.In w (us R Pi a) /\ y = (Name.Selector a, w).
  Proof.
    intros R D Pi y; unfold realSelector; rewrite SOcp.mem_unionMap.
    split.
    - intros [[p Al] [Hc Hy]]; cbn beta iota in Hy.
      apply mem_selectorAtoms in Hy.
      exists p, Al; split; assumption.
    - intros [p [Al [Hc Hy]]].
      exists (p, Al); split; [exact Hc | cbn beta iota].
      apply mem_selectorAtoms; exact Hy.
  Qed.

  Lemma mem_realGuard : forall G y,
      T.PkgSet.In y (realGuard G) <->
      exists p a x, Conf.In (p, (a, x)) G /\
        (y = (Name.Guard p a x, Version.Zero) \/
         y = (Name.Guard p a x, Version.One)).
  Proof.
    intros G y; unfold realGuard; rewrite SOgp.mem_unionMap.
    split.
    - intros [[p [a x]] [He Hy]]; cbn beta iota in Hy.
      rewrite SOgp.add_in, SOgp.singleton_in in Hy.
      exists p, a, x; split; [exact He | exact Hy].
    - intros [p [a [x [He Hy]]]].
      exists (p, (a, x)); split; [exact He | cbn beta iota].
      rewrite SOgp.add_in, SOgp.singleton_in; exact Hy.
  Qed.

  Lemma versions_orig_spec : forall R D Pi G n w,
      T.VSet.In w (versions R D Pi G (Name.Orig n)) <->
      exists v, PkgSet.In (n, v) R /\ w = Version.Orig v.
  Proof.
    intros R D Pi G n w; cbn [versions].
    unfold embedVS; rewrite SOvw.mem_map.
    split; intros [v [Hv Hw]]; exists v;
      (split; [apply Ver.realVersions_spec; exact Hv | exact Hw]).
  Qed.

  Lemma versions_disjunct_spec : forall R D Pi G A w,
      T.VSet.In w (versions R D Pi G (Name.Disjunct A)) <->
      hasClauseb D A = true /\ (2 <=? AtomSet.cardinal A) = true /\
      T.VSet.In w (versionsDisj A).
  Proof.
    intros R D Pi G A w; cbn [versions].
    destruct (hasClauseb D A) eqn:H1; cbn [andb].
    - destruct (2 <=? AtomSet.cardinal A) eqn:H2.
      + split.
        * intro H; split; [reflexivity | split; [reflexivity | exact H]].
        * intros (_ & _ & H); exact H.
      + split; [intro H; exfalso; exact (SOvw.empty_in _ H) |
                intros (_ & H & _); discriminate H].
    - split; [intro H; exfalso; exact (SOvw.empty_in _ H) |
              intros (H & _); discriminate H].
  Qed.

  Lemma versions_selector_spec : forall R D Pi G a w,
      T.VSet.In w (versions R D Pi G (Name.Selector a)) <->
      occursAtomb D a = true /\ provb Pi a = true /\
      T.VSet.In w (us R Pi a).
  Proof.
    intros R D Pi G a w; cbn [versions].
    destruct (occursAtomb D a) eqn:H1; cbn [andb].
    - destruct (provb Pi a) eqn:H2.
      + split.
        * intro H; split; [reflexivity | split; [reflexivity | exact H]].
        * intros (_ & _ & H); exact H.
      + split; [intro H; exfalso; exact (SOvw.empty_in _ H) |
                intros (_ & H & _); discriminate H].
    - split; [intro H; exfalso; exact (SOvw.empty_in _ H) |
              intros (H & _); discriminate H].
  Qed.

  Lemma versions_guard_spec : forall R D Pi G p a x w,
      T.VSet.In w (versions R D Pi G (Name.Guard p a x)) <->
      Conf.In (p, (a, x)) G /\ (w = Version.Zero \/ w = Version.One).
  Proof.
    intros R D Pi G p a x w; cbn [versions].
    destruct (Conf.mem (p, (a, x)) G) eqn:Hm.
    - apply Conf.mem_spec in Hm.
      split.
      + intro H; apply mem_zeroOne in H; split; assumption.
      + intros [_ H]; apply mem_zeroOne; exact H.
    - split; [intro H; exfalso; exact (SOvw.empty_in _ H) |
              intros [H _]; apply Conf.mem_spec in H; congruence].
  Qed.

  Lemma mem_reduceReal : forall R D Pi G (n' : Name.t) (w : Version.t),
      T.PkgSet.In (n', w) (reduceReal R D Pi G) <->
      T.VSet.In w (versions R D Pi G n').
  Proof.
    intros R D Pi G n' w; unfold reduceReal.
    rewrite !T.PkgSet.union_spec.
    rewrite mem_realOrig, mem_realDisjunct, mem_realSelector, mem_realGuard.
    destruct n' as [n | A | a | p a x].
    - rewrite versions_orig_spec; split.
      + intros [[n0 [v0 [HqR Hy]]] | [H2 | [H3 | H4]]].
        * injection Hy as -> ->.
          exists v0; split; [exact HqR | reflexivity].
        * destruct H2 as [p0 [Al [_ [_ [a0 [_ Hy]]]]]]; discriminate Hy.
        * destruct H3 as [p0 [Al [_ [a0 [_ [_ [w0 [_ Hy]]]]]]]];
            discriminate Hy.
        * destruct H4 as [p0 [a0 [x0 [_ [Hy | Hy]]]]]; discriminate Hy.
      + intros [v [Hv ->]].
        left; exists n, v; split; [exact Hv | reflexivity].
    - rewrite versions_disjunct_spec; split.
      + intros [[n0 [v0 [_ Hy]]] | [H2 | [H3 | H4]]].
        * discriminate Hy.
        * destruct H2 as [p0 [Al [Hc [Hcard [a0 [Ha0 Hy]]]]]].
          injection Hy as -> ->.
          split; [apply hasClauseb_iff; exists p0; exact Hc |].
          split; [exact Hcard |].
          unfold versionsDisj; apply SOaw.mem_map;
            exists a0; split; [exact Ha0 | reflexivity].
        * destruct H3 as [p0 [Al [_ [a0 [_ [_ [w0 [_ Hy]]]]]]]];
            discriminate Hy.
        * destruct H4 as [p0 [a0 [x0 [_ [Hy | Hy]]]]]; discriminate Hy.
      + intros (Hhc & Hcard & H).
        unfold versionsDisj in H; apply SOaw.mem_map in H;
          destruct H as [a0 [Ha0 ->]].
        apply hasClauseb_iff in Hhc; destruct Hhc as [p0 Hc].
        right; left; exists p0, A; split; [exact Hc |].
        split; [exact Hcard |].
        exists a0; split; [exact Ha0 | reflexivity].
    - rewrite versions_selector_spec; split.
      + intros [[n0 [v0 [_ Hy]]] | [H2 | [H3 | H4]]].
        * discriminate Hy.
        * destruct H2 as [p0 [Al [_ [_ [a0 [_ Hy]]]]]]; discriminate Hy.
        * destruct H3 as [p0 [Al [Hc [a0 [Ha0 [Hp [w0 [Hw0 Hy]]]]]]]].
          injection Hy as -> ->.
          split; [apply occursAtomb_iff; exists p0, Al; split; assumption |].
          split; [exact Hp | exact Hw0].
        * destruct H4 as [p0 [a0 [x0 [_ [Hy | Hy]]]]]; discriminate Hy.
      + intros (Hocc & Hp & H).
        apply occursAtomb_iff in Hocc; destruct Hocc as [p0 [Al [Hc Ha0]]].
        right; right; left; exists p0, Al; split; [exact Hc |].
        exists a; split; [exact Ha0 |].
        split; [exact Hp |].
        exists w; split; [exact H | reflexivity].
    - rewrite versions_guard_spec; split.
      + intros [[n0 [v0 [_ Hy]]] | [H2 | [H3 | H4]]].
        * discriminate Hy.
        * destruct H2 as [p0 [Al [_ [_ [a0 [_ Hy]]]]]]; discriminate Hy.
        * destruct H3 as [p0 [Al [_ [a0 [_ [_ [w0 [_ Hy]]]]]]]];
            discriminate Hy.
        * destruct H4 as [p0 [a0 [x0 [He [Hy | Hy]]]]];
            injection Hy as -> -> -> ->.
          { split; [exact He | left; reflexivity]. }
          { split; [exact He | right; reflexivity]. }
      + intros [He Hw].
        right; right; right; exists p, a, x; split; [exact He |].
        destruct Hw as [-> | ->]; [left | right]; reflexivity.
  Qed.

  Lemma mem_reduceDeps : forall R D Pi G (s : T.Pkg.t) (h : T.Dependees.t),
      T.DepRel.In (s, h) (reduceDeps R D Pi G) <->
      T.PkgSet.In s (reduceReal R D Pi G) /\
      T.DependeesSet.In h (dependees R D Pi G s).
  Proof.
    intros R D Pi G s [n vs]; unfold reduceDeps;
      rewrite SOse.mem_unionMap.
    split.
    - intros [s0 [Hs0 Hy]]; cbn beta iota in Hy.
      unfold depEdges in Hy; apply SOee.mem_map in Hy.
      destruct Hy as [e [He Hy]].
      injection Hy as -> He2.
      rewrite <- He2 in He.
      split; assumption.
    - intros [Hs He].
      exists s; split; [exact Hs | cbn beta iota].
      unfold depEdges; apply SOee.mem_map.
      exists (n, vs); split; [exact He | reflexivity].
  Qed.

  Definition tryInvPkg (s : T.Pkg.t) : option Pkg.t :=
    match s with
    | (Name.Orig n, Version.Orig v) => Some (n, v)
    | _ => None
    end.

  Lemma tryInvPkg_embed : forall p, tryInvPkg (embedPkg p) = Some p.
  Proof. intros [n v]; reflexivity. Qed.

  Lemma tryInvPkg_some : forall (s : T.Pkg.t) (p : Pkg.t),
      tryInvPkg s = Some p -> embedPkg p = s.
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

  Lemma dependees_orig_spec : forall R D Pi G (n : N.t) (v : V.t) y,
      T.DependeesSet.In y (dependees R D Pi G (Name.Orig n, Version.Orig v)) <->
      (exists A, Deps.In ((n, v), A) D /\
         (((AtomSet.cardinal A =? 1) = true /\
           exists a, AtomSet.min_elt A = Some a /\ y = tgt R Pi a) \/
          ((AtomSet.cardinal A =? 1) = false /\
           y = (Name.Disjunct A, versionsDisj A)))) \/
      (exists a x, Conf.In ((n, v), (a, x)) G /\
         y = (Name.Guard (n, v) a x, T.VSet.singleton Version.One)) \/
      (exists m u a x, Conf.In ((m, u), (a, x)) G /\
         matchb Pi (n, v) a = true /\
         (m, u) <> (n, v) /\ (x = true -> NG.groupEq n m = false) /\
         y = (Name.Guard (m, u) a x, T.VSet.singleton Version.Zero)).
  Proof.
    intros R D Pi G n v y; cbn [dependees].
    rewrite !T.DependeesSet.union_spec, SOde.mem_filterMap,
      !SOge.mem_filterMap.
    split.
    - intros [[[cp cA] [Hc Hy]] |
              [[[ep [ea ex]] [He Hy]] | [[[em eu] [ea ex]] [He Hy]]]];
        cbn [fst snd] in Hy.
      + destruct (Pkg.eq_dec cp (n, v)) as [-> | NE]; [| discriminate].
        destruct (AtomSet.cardinal cA =? 1) eqn:Hcard.
        * destruct (AtomSet.min_elt cA) as [a0 |] eqn:Hmin; [| discriminate].
          injection Hy as <-.
          left; exists cA; split; [exact Hc |].
          left; split; [exact Hcard |].
          exists a0; split; [exact Hmin | reflexivity].
        * injection Hy as <-.
          left; exists cA; split; [exact Hc |].
          right; split; [exact Hcard | reflexivity].
      + destruct (Pkg.eq_dec ep (n, v)) as [-> | NE]; [| discriminate].
        injection Hy as <-.
        right; left; exists ea, ex; split; [exact He | reflexivity].
      + destruct (andb (matchb Pi (n, v) ea)
                    (andb
                       (negb (if Pkg.eq_dec (em, eu) (n, v)
                              then true else false))
                       (negb (exemptb ex n em))))
          eqn:Hg; [| discriminate].
        apply andb_prop in Hg; destruct Hg as [Hm Hg].
        apply andb_prop in Hg; destruct Hg as [Hneg Hex].
        destruct (Pkg.eq_dec (em, eu) (n, v)) as [E | NE];
          [discriminate Hneg |].
        injection Hy as <-.
        right; right; exists em, eu, ea, ex.
        split; [exact He |].
        split; [exact Hm |].
        split; [exact NE |].
        split; [| reflexivity].
        exact (proj1 (exemptb_iff ex n em)
                 (proj1 (Bool.negb_true_iff _) Hex)).
    - intros [[A [HA Hcase]] |
              [[a0 [x0 [Ha0 ->]]] |
               [m0 [u0 [a0 [x0 [Hg0 [Hm [Hne [Hex ->]]]]]]]]]].
      + left; exists ((n, v), A); split; [exact HA |].
        cbn [fst snd].
        destruct (Pkg.eq_dec (n, v) (n, v)) as [_ | NE];
          [| contradiction NE; reflexivity].
        destruct Hcase as [[Hcard [a0 [Hmin ->]]] | [Hcard ->]].
        * rewrite Hcard, Hmin; reflexivity.
        * rewrite Hcard; reflexivity.
      + right; left; exists ((n, v), (a0, x0)); split; [exact Ha0 |].
        cbn [fst snd].
        destruct (Pkg.eq_dec (n, v) (n, v)) as [_ | NE];
          [| contradiction NE; reflexivity].
        reflexivity.
      + right; right; exists ((m0, u0), (a0, x0)); split; [exact Hg0 |].
        cbn [fst snd].
        rewrite Hm.
        destruct (Pkg.eq_dec (m0, u0) (n, v)) as [E | _];
          [contradiction (Hne E) |].
        assert (Hx : negb (exemptb x0 n m0) = true).
        { apply Bool.negb_true_iff, exemptb_iff; exact Hex. }
        rewrite Hx; reflexivity.
  Qed.

  Lemma dependees_disjunct_spec : forall R D Pi G A a y,
      T.DependeesSet.In y
        (dependees R D Pi G (Name.Disjunct A, Version.Atom a)) <->
      hasClauseb D A = true /\ (2 <=? AtomSet.cardinal A) = true /\
      AtomSet.mem a A = true /\ y = tgt R Pi a.
  Proof.
    intros R D Pi G A a y; cbn [dependees].
    destruct (hasClauseb D A) eqn:H1; cbn [andb].
    - destruct (2 <=? AtomSet.cardinal A) eqn:H2; cbn [andb].
      + destruct (AtomSet.mem a A) eqn:H3; cbn [andb].
        * rewrite SOde.singleton_in.
          split.
          { intro H; split; [reflexivity |].
            split; [reflexivity |].
            split; [reflexivity | exact H]. }
          { intros (_ & _ & _ & H); exact H. }
        * split; [intro H; exfalso; exact (SOde.empty_in _ H) |
                  intros (_ & _ & H & _); discriminate H].
      + split; [intro H; exfalso; exact (SOde.empty_in _ H) |
                intros (_ & H & _); discriminate H].
    - split; [intro H; exfalso; exact (SOde.empty_in _ H) |
              intros (H & _); discriminate H].
  Qed.

  Lemma dependees_selector_spec : forall R D Pi G a (m : N.t) (w : V.t) y,
      T.DependeesSet.In y
        (dependees R D Pi G (Name.Selector a, Version.Ref m w)) <->
      occursAtomb D a = true /\ provb Pi a = true /\
      T.VSet.mem (Version.Ref m w) (us R Pi a) = true /\
      y = (Name.Orig m, T.VSet.singleton (Version.Orig w)).
  Proof.
    intros R D Pi G a m w y; cbn [dependees].
    destruct (occursAtomb D a) eqn:H1; cbn [andb].
    - destruct (provb Pi a) eqn:H2; cbn [andb].
      + destruct (T.VSet.mem (Version.Ref m w) (us R Pi a)) eqn:H3; cbn [andb].
        * rewrite SOde.singleton_in.
          split.
          { intro H; split; [reflexivity |].
            split; [reflexivity |].
            split; [reflexivity | exact H]. }
          { intros (_ & _ & _ & H); exact H. }
        * split; [intro H; exfalso; exact (SOde.empty_in _ H) |
                  intros (_ & _ & H & _); discriminate H].
      + split; [intro H; exfalso; exact (SOde.empty_in _ H) |
                intros (_ & H & _); discriminate H].
    - split; [intro H; exfalso; exact (SOde.empty_in _ H) |
              intros (H & _); discriminate H].
  Qed.

  Lemma dependees_selector_real_spec : forall R D Pi G a (w : V.t) y,
      T.DependeesSet.In y
        (dependees R D Pi G (Name.Selector a, Version.RefReal w)) <->
      occursAtomb D a = true /\ provb Pi a = true /\
      T.VSet.mem (Version.RefReal w) (us R Pi a) = true /\
      y = (Name.Orig (aname a), T.VSet.singleton (Version.Orig w)).
  Proof.
    intros R D Pi G a w y; cbn [dependees].
    destruct (occursAtomb D a) eqn:H1; cbn [andb].
    - destruct (provb Pi a) eqn:H2; cbn [andb].
      + destruct (T.VSet.mem (Version.RefReal w) (us R Pi a)) eqn:H3;
          cbn [andb].
        * rewrite SOde.singleton_in.
          split.
          { intro H; split; [reflexivity |].
            split; [reflexivity |].
            split; [reflexivity | exact H]. }
          { intros (_ & _ & _ & H); exact H. }
        * split; [intro H; exfalso; exact (SOde.empty_in _ H) |
                  intros (_ & _ & H & _); discriminate H].
      + split; [intro H; exfalso; exact (SOde.empty_in _ H) |
                intros (_ & H & _); discriminate H].
    - split; [intro H; exfalso; exact (SOde.empty_in _ H) |
              intros (H & _); discriminate H].
  Qed.

  Module SOpv := SetOps Pkg V PkgSet VSet.
  Lemma eval_vfHolds : forall f Vn u,
      VSet.In u (Ver.eval f Vn) <-> VSet.In u Vn /\ vfHolds f u = true.
  Proof.
    intros f Vn u;
      induction f as [ | | f1 IH1 f2 IH2 | f1 IH1 f2 IH2 | op c];
      cbn [Ver.eval vfHolds].
    - split; [intro H; split; [exact H | reflexivity] | intros [H _]; exact H].
    - split; [intro H; exfalso; exact (SOpv.empty_in _ H) |
              intros [_ H]; discriminate H].
    - rewrite VSet.inter_spec, IH1, IH2, Bool.andb_true_iff; tauto.
    - rewrite VSet.union_spec, IH1, IH2, Bool.orb_true_iff; tauto.
    - rewrite VSet.filter_spec'.
      tauto.
  Qed.

  Lemma cardinal_in : forall A (a : Atom.t),
      AtomSet.In a A -> 1 <= AtomSet.cardinal A.
  Proof.
    intros A a Ha.
    rewrite AtomSet.cardinal_spec.
    apply SOap.elements_in in Ha.
    destruct (AtomSet.elements A); [destruct Ha | cbn; lia].
  Qed.

  Theorem debian_soundness :
    forall R D Pi G (r : Pkg.t) (S : T.PkgSet.t),
      T.IsResolution (reduceReal R D Pi G) (reduceDeps R D Pi G)
        (embedPkg r) S ->
      IsResolution R D Pi G r (debianResolution S).
  Proof.
    intros R D Pi G r S [Hsub Hroot Hdep Huniq].
    assert (Htgt : forall (s : T.Pkg.t) (a : Atom.t),
        T.PkgSet.In s S ->
        T.DependeesSet.In (tgt R Pi a) (dependees R D Pi G s) ->
        occursAtomb D a = true ->
        exists q, PkgSet.In q (debianResolution S) /\ Match Pi q a).
    { intros s [an af] HsS Hedge Hocc.
      assert (HsReal := Hsub _ HsS).
      unfold tgt in Hedge.
      destruct (provb Pi (an, af)) eqn:Hpb; rewrite ?Hpb in Hedge.
      - assert (Hd : T.DepRel.In
            (s, (Name.Selector (an, af), us R Pi (an, af)))
            (reduceDeps R D Pi G))
          by (apply mem_reduceDeps; split; [exact HsReal | exact Hedge]).
        destruct (Hdep _ HsS _ _ Hd) as [dv [Hdv HdvS]].
        apply mem_us in Hdv.
        destruct Hdv as [[u [Hu ->]] | [m0 [u0 [vt [Hin [Hvt ->]]]]]].
        + assert
            (Hmem : T.VSet.mem (Version.RefReal u) (us R Pi (an, af)) = true).
          { apply T.VSet.mem_spec; apply mem_us; left.
            exists u; split; [exact Hu | reflexivity]. }
          assert (Hedge2 : T.DependeesSet.In
              (Name.Orig an, T.VSet.singleton (Version.Orig u))
              (dependees R D Pi G
                 (Name.Selector (an, af), Version.RefReal u))).
          { apply dependees_selector_real_spec.
            split; [exact Hocc |].
            split; [exact Hpb |].
            split; [exact Hmem | reflexivity]. }
          assert (Hd2 : T.DepRel.In
              ((Name.Selector (an, af), Version.RefReal u),
               (Name.Orig an, T.VSet.singleton (Version.Orig u)))
              (reduceDeps R D Pi G))
            by (apply mem_reduceDeps; split;
                [apply Hsub; exact HdvS | exact Hedge2]).
          destruct (Hdep _ HdvS _ _ Hd2) as [dv2 [Hdv2 Hdv2S]].
          apply T.VSet.singleton_spec in Hdv2; rewrite Hdv2 in Hdv2S.
          exists (an, u); split.
          { apply mem_debianResolution; exact Hdv2S. }
          { left; cbn [aname aform fst snd]; split; [reflexivity |].
            unfold evalAt in Hu; apply eval_vfHolds in Hu.
            destruct Hu as [_ Hh]; exact Hh. }
        + assert (Hmem : T.VSet.mem (Version.Ref m0 u0)
                           (us R Pi (an, af)) = true).
          { apply T.VSet.mem_spec; apply mem_us; right.
            exists m0, u0, vt.
            split; [exact Hin | split; [exact Hvt | reflexivity]]. }
          assert (Hedge2 : T.DependeesSet.In
              (Name.Orig m0, T.VSet.singleton (Version.Orig u0))
              (dependees R D Pi G (Name.Selector (an, af), Version.Ref m0 u0))).
          { apply dependees_selector_spec.
            split; [exact Hocc |].
            split; [exact Hpb |].
            split; [exact Hmem | reflexivity]. }
          assert (Hd2 : T.DepRel.In
              ((Name.Selector (an, af), Version.Ref m0 u0),
               (Name.Orig m0, T.VSet.singleton (Version.Orig u0)))
              (reduceDeps R D Pi G))
            by (apply mem_reduceDeps; split;
                [apply Hsub; exact HdvS | exact Hedge2]).
          destruct (Hdep _ HdvS _ _ Hd2) as [dv2 [Hdv2 Hdv2S]].
          apply T.VSet.singleton_spec in Hdv2; rewrite Hdv2 in Hdv2S.
          exists (m0, u0); split.
          { apply mem_debianResolution; exact Hdv2S. }
          { right; exists vt; split; [exact Hin | exact Hvt]. }
      - assert (Hd : T.DepRel.In
            (s, (Name.Orig an, embedVS (evalAt R (an, af))))
            (reduceDeps R D Pi G))
          by (apply mem_reduceDeps; split; [exact HsReal | exact Hedge]).
        destruct (Hdep _ HsS _ _ Hd) as [dv [Hdv HdvS]].
        unfold embedVS in Hdv; apply SOvw.mem_map in Hdv;
          destruct Hdv as [u [Hu ->]].
        exists (an, u); split.
        { apply mem_debianResolution; exact HdvS. }
        { left; cbn [aname aform fst snd]; split; [reflexivity |].
          unfold evalAt in Hu; apply eval_vfHolds in Hu.
          destruct Hu as [_ Hh]; exact Hh. } }
    constructor.
    - intros p Hp.
      apply mem_debianResolution in Hp.
      apply Hsub in Hp.
      rewrite (surjective_pairing p).
      assert (Hv := proj1 (mem_reduceReal R D Pi G
                             (Name.Orig (fst p)) (Version.Orig (snd p))) Hp).
      apply versions_orig_spec in Hv.
      destruct Hv as [v [HvR Hv]]; injection Hv as Hv; subst v.
      exact HvR.
    - apply mem_debianResolution; exact Hroot.
    - intros p Hp A HA.
      apply mem_debianResolution in Hp.
      destruct (AtomSet.cardinal A =? 1) eqn:Hcard.
      + destruct (AtomSet.min_elt A) as [a |] eqn:Hmin.
        * assert (HaA : AtomSet.In a A)
            by (apply AtomSet.min_elt_spec1; exact Hmin).
          assert (Hocc : occursAtomb D a = true)
            by (apply occursAtomb_iff; exists p, A; split;
                [exact HA | exact HaA]).
          assert (Hedge : T.DependeesSet.In (tgt R Pi a)
                            (dependees R D Pi G (embedPkg p))).
          { apply (dependees_orig_spec R D Pi G (fst p) (snd p)).
            left; exists A; split.
            - rewrite <- (surjective_pairing p); exact HA.
            - left; split; [exact Hcard |].
              exists a; split; [exact Hmin | reflexivity]. }
          destruct (Htgt (embedPkg p) a Hp Hedge Hocc) as [q [HqS HqM]].
          exists a; split; [exact HaA |].
          exists q; split; assumption.
        * exfalso.
          apply AtomSet.min_elt_spec3 in Hmin.
          apply Nat.eqb_eq in Hcard.
          rewrite AtomSet.cardinal_spec in Hcard.
          destruct (AtomSet.elements A) as [| z l] eqn:He; [discriminate |].
          apply (Hmin z).
          apply SOap.elements_in.
          rewrite He; left; reflexivity.
      + assert (Hedge : T.DependeesSet.In (Name.Disjunct A, versionsDisj A)
                          (dependees R D Pi G (embedPkg p))).
        { apply (dependees_orig_spec R D Pi G (fst p) (snd p)).
          left; exists A; split.
          - rewrite <- (surjective_pairing p); exact HA.
          - right; split; [exact Hcard | reflexivity]. }
        assert (Hd : T.DepRel.In (embedPkg p, (Name.Disjunct A, versionsDisj A))
                       (reduceDeps R D Pi G))
          by (apply mem_reduceDeps; split;
              [apply Hsub; exact Hp | exact Hedge]).
        destruct (Hdep _ Hp _ _ Hd) as [dv [Hdv HdvS]].
        unfold versionsDisj in Hdv; apply SOaw.mem_map in Hdv;
          destruct Hdv as [a [HaA ->]].
        assert (Hocc : occursAtomb D a = true)
          by (apply occursAtomb_iff; exists p, A; split;
              [exact HA | exact HaA]).
        assert (Hcard2 : (2 <=? AtomSet.cardinal A) = true).
        { apply Nat.leb_le.
          apply Nat.eqb_neq in Hcard.
          assert (H1 := cardinal_in A a HaA).
          lia. }
        assert (Hedge2 : T.DependeesSet.In (tgt R Pi a)
                           (dependees R D Pi G
                              (Name.Disjunct A, Version.Atom a))).
        { apply dependees_disjunct_spec.
          split; [apply hasClauseb_iff; exists p; exact HA |].
          split; [exact Hcard2 |].
          split; [apply AtomSet.mem_spec; exact HaA | reflexivity]. }
        destruct (Htgt (Name.Disjunct A, Version.Atom a) a HdvS Hedge2 Hocc)
          as [q [HqS HqM]].
        exists a; split; [exact HaA |].
        exists q; split; assumption.
    - intros [pn pv] Hp a x HaG [q [HqS [Hqp [Hxq HqM]]]].
      apply mem_debianResolution in Hp.
      apply mem_debianResolution in HqS.
      assert (Hedge1 : T.DependeesSet.In
          (Name.Guard (pn, pv) a x, T.VSet.singleton Version.One)
          (dependees R D Pi G (embedPkg (pn, pv)))).
      { apply (dependees_orig_spec R D Pi G pn pv).
        right; left; exists a, x; split; [exact HaG | reflexivity]. }
      assert (Hd1 : T.DepRel.In
          (embedPkg (pn, pv),
           (Name.Guard (pn, pv) a x, T.VSet.singleton Version.One))
          (reduceDeps R D Pi G))
        by (apply mem_reduceDeps; split;
            [apply Hsub; exact Hp | exact Hedge1]).
      destruct (Hdep _ Hp _ _ Hd1) as [dv1 [Hdv1 Hdv1S]].
      apply T.VSet.singleton_spec in Hdv1; rewrite Hdv1 in Hdv1S.
      assert (Hedge0 : T.DependeesSet.In
          (Name.Guard (pn, pv) a x, T.VSet.singleton Version.Zero)
          (dependees R D Pi G (embedPkg q))).
      { apply (dependees_orig_spec R D Pi G (fst q) (snd q)).
        rewrite <- (surjective_pairing q).
        right; right; exists pn, pv, a, x.
        split; [exact HaG |].
        split; [apply matchb_iff; exact HqM |].
        split; [intro E; exact (Hqp (eq_sym E)) |].
        split; [exact Hxq | reflexivity]. }
      assert (Hd0 : T.DepRel.In
          (embedPkg q, (Name.Guard (pn, pv) a x, T.VSet.singleton Version.Zero))
          (reduceDeps R D Pi G))
        by (apply mem_reduceDeps; split;
            [apply Hsub; exact HqS | exact Hedge0]).
      destruct (Hdep _ HqS _ _ Hd0) as [dv0 [Hdv0 Hdv0S]].
      apply T.VSet.singleton_spec in Hdv0; rewrite Hdv0 in Hdv0S.
      assert (Huv := Huniq (Name.Guard (pn, pv) a x)
                       Version.One Version.Zero Hdv1S Hdv0S).
      discriminate Huv.
    - intros n v v' Hv Hv'.
      apply mem_debianResolution in Hv; apply mem_debianResolution in Hv'.
      assert (H := Huniq (Name.Orig n)
                     (Version.Orig v) (Version.Orig v') Hv Hv').
      injection H as H; exact H.
  Qed.

  Definition satAtoms (Pi : Prov.t) (S : PkgSet.t) (A : AtomSet.t) :
      AtomSet.t :=
    AtomSet.filter (fun a =>
        PkgSet.exists_ (fun q => matchb Pi q a) S)
      A.

  (* q satisfies a under its own name rather than through a Provides entry,
     which is what puts it in the real branch of us. *)
  Definition rmatchb (q : Pkg.t) (a : Atom.t) : bool :=
    andb (NEqb.eqb (fst q) (aname a)) (vfHolds (aform a) (snd q)).

  Definition chosenVersion (q : Pkg.t) (a : Atom.t) : Version.t :=
    if rmatchb q a
    then Version.RefReal (snd q)
    else Version.Ref (fst q) (snd q).

  Definition chooseSatisfier (Pi : Prov.t) (S : PkgSet.t) (a : Atom.t) :
      option Version.t :=
    match PkgSet.min_elt (PkgSet.filter (fun q => matchb Pi q a) S) with
    | Some q => Some (chosenVersion q a)
    | None => None
    end.

  Definition cwSelector (Pi : Prov.t) (S : PkgSet.t) (A : AtomSet.t) :
      T.PkgSet.t :=
    SOap.filterMap (fun a =>
        if provb Pi a
        then match chooseSatisfier Pi S a with
             | Some w => Some (Name.Selector a, w)
             | None => None
             end
        else None)
      A.

  Definition coreResolution (R : PkgSet.t) (D : Deps.t)
      (Pi : Prov.t) (G : Conf.t) (S : PkgSet.t) : T.PkgSet.t :=
    T.PkgSet.union (SOrp.map embedPkg S)
      (T.PkgSet.union
         (SOcp.filterMap (fun c =>
              if andb (PkgSet.mem (fst c) S)
                   (2 <=? AtomSet.cardinal (snd c))
              then match AtomSet.min_elt (satAtoms Pi S (snd c)) with
                   | Some a => Some (Name.Disjunct (snd c), Version.Atom a)
                   | None => None
                   end
              else None)
            D)
         (T.PkgSet.union
            (SOcp.unionMap (fun '(p, A) =>
                 if PkgSet.mem p S
                 then cwSelector Pi S A
                 else T.PkgSet.empty)
               D)
            (SOgp.filterMap (fun e =>
                 if PkgSet.mem (fst e) S
                 then Some (Name.Guard (fst e) (fst (snd e)) (snd (snd e)),
                            Version.One)
                 else if PkgSet.exists_ (fun q =>
                           andb (matchb Pi q (fst (snd e)))
                             (andb
                                (negb (if Pkg.eq_dec q (fst e)
                                       then true else false))
                                (negb (exemptb (snd (snd e)) (fst q)
                                         (fst (fst e))))))
                        S
                      then Some
                             (Name.Guard (fst e) (fst (snd e)) (snd (snd e)),
                              Version.Zero)
                      else None)
               G))).

  Lemma cardinal1_eq : forall A (a b : Atom.t),
      AtomSet.cardinal A = 1 ->
      AtomSet.In a A -> AtomSet.In b A -> a = b.
  Proof.
    intros A a b Hcard Ha Hb.
    rewrite AtomSet.cardinal_spec in Hcard.
    apply SOap.elements_in in Ha; apply SOap.elements_in in Hb.
    destruct (AtomSet.elements A) as [| c l]; [discriminate |].
    destruct l; [| discriminate].
    destruct Ha as [Ha | []]; destruct Hb as [Hb | []]; subst; reflexivity.
  Qed.

  Lemma mem_satAtoms : forall Pi S A a,
      AtomSet.In a (satAtoms Pi S A) <->
      AtomSet.In a A /\ exists q, PkgSet.In q S /\ matchb Pi q a = true.
  Proof.
    intros Pi S A a; unfold satAtoms.
    rewrite AtomSet.filter_spec'.
    rewrite PkgSet.exists_spec'.
    unfold PkgSet.Exists; reflexivity.
  Qed.

  Lemma chooseSatisfier_spec : forall Pi S a w,
      chooseSatisfier Pi S a = Some w ->
      exists n v, PkgSet.In (n, v) S /\ matchb Pi (n, v) a = true /\
        w = chosenVersion (n, v) a.
  Proof.
    intros Pi S a w H; unfold chooseSatisfier in H.
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
      exists w, chooseSatisfier Pi S a = Some w.
  Proof.
    intros Pi S a q HqS Hm; unfold chooseSatisfier.
    destruct (PkgSet.min_elt (PkgSet.filter (fun q0 => matchb Pi q0 a) S))
      as [q1 |] eqn:Hmin.
    - exists (chosenVersion q1 a); reflexivity.
    - exfalso.
      apply PkgSet.min_elt_spec3 in Hmin.
      apply (Hmin q).
      rewrite PkgSet.filter_spec'.
      split; assumption.
  Qed.

  Lemma mem_cwSelector : forall Pi S A y,
      T.PkgSet.In y (cwSelector Pi S A) <->
      exists a, AtomSet.In a A /\ provb Pi a = true /\
        exists w, chooseSatisfier Pi S a = Some w /\ y = (Name.Selector a, w).
  Proof.
    intros Pi S A y; unfold cwSelector.
    rewrite SOap.mem_filterMap.
    split.
    - intros [a [Ha Hy]]; cbn beta iota in Hy.
      destruct (provb Pi a) eqn:Hp; [| discriminate].
      destruct (chooseSatisfier Pi S a) as [w0 |] eqn:Hcs; [| discriminate].
      injection Hy as <-.
      exists a; split; [exact Ha |].
      split; [exact Hp |].
      exists w0; split; [exact Hcs | reflexivity].
    - intros [a [Ha [Hp [w0 [Hcs ->]]]]].
      exists a; split; [exact Ha | cbn beta iota].
      rewrite Hp, Hcs; reflexivity.
  Qed.

  Lemma mem_coreResolution : forall R D Pi G S y,
      T.PkgSet.In y (coreResolution R D Pi G S) <->
      (exists p, PkgSet.In p S /\ y = embedPkg p) \/
      (exists p Al, Deps.In (p, Al) D /\ PkgSet.mem p S = true /\
         (2 <=? AtomSet.cardinal Al) = true /\
         exists a, AtomSet.min_elt (satAtoms Pi S Al) = Some a /\
           y = (Name.Disjunct Al, Version.Atom a)) \/
      (exists p Al, Deps.In (p, Al) D /\ PkgSet.mem p S = true /\
         exists a, AtomSet.In a Al /\ provb Pi a = true /\
           exists w, chooseSatisfier Pi S a = Some w /\
             y = (Name.Selector a, w)) \/
      (exists m u a x, Conf.In ((m, u), (a, x)) G /\
         ((PkgSet.mem (m, u) S = true /\
           y = (Name.Guard (m, u) a x, Version.One)) \/
          (PkgSet.mem (m, u) S = false /\
           PkgSet.exists_ (fun q =>
               andb (matchb Pi q a)
                 (andb
                    (negb (if Pkg.eq_dec q (m, u) then true else false))
                    (negb (exemptb x (fst q) m)))) S
             = true /\
           y = (Name.Guard (m, u) a x, Version.Zero)))).
  Proof.
    intros R D Pi G S y; unfold coreResolution.
    rewrite !T.PkgSet.union_spec, SOrp.mem_map, SOcp.mem_filterMap,
      SOcp.mem_unionMap, SOgp.mem_filterMap.
    split.
    - intros [H1 | [H2 | [H3 | H4]]].
      + left; exact H1.
      + destruct H2 as [[cp cA] [Hc Hy]]; cbn [fst snd] in Hy.
        destruct (andb (PkgSet.mem cp S) (2 <=? AtomSet.cardinal cA))
          eqn:Hg; [| discriminate].
        destruct (AtomSet.min_elt (satAtoms Pi S cA)) as [a0 |] eqn:Hmin;
          [| discriminate].
        injection Hy as <-.
        apply andb_prop in Hg; destruct Hg as [Hm Hcard].
        right; left; exists cp, cA; split; [exact Hc |].
        split; [exact Hm |].
        split; [exact Hcard |].
        exists a0; split; [exact Hmin | reflexivity].
      + destruct H3 as [[cp cA] [Hc Hy]]; cbn beta iota in Hy.
        destruct (PkgSet.mem cp S) eqn:Hm;
          [| exfalso; exact (SOcp.empty_in _ Hy)].
        apply mem_cwSelector in Hy.
        destruct Hy as [a0 [Ha0 [Hp0 [w0 [Hcs Hy]]]]].
        right; right; left; exists cp, cA; split; [exact Hc |].
        split; [exact Hm |].
        exists a0; split; [exact Ha0 |].
        split; [exact Hp0 |].
        exists w0; split; [exact Hcs | exact Hy].
      + destruct H4 as [[[em eu] [ea ex]] [He Hy]];
          cbn [fst snd] in Hy.
        destruct (PkgSet.mem (em, eu) S) eqn:Hm.
        * injection Hy as <-.
          right; right; right; exists em, eu, ea, ex; split; [exact He |].
          left; split; [exact Hm | reflexivity].
        * destruct (PkgSet.exists_ (fun q =>
                        andb (matchb Pi q ea)
                          (andb
                             (negb (if Pkg.eq_dec q (em, eu)
                                    then true else false))
                             (negb (exemptb ex (fst q) em))))
                      S) eqn:Hex; [| discriminate].
          injection Hy as <-.
          right; right; right; exists em, eu, ea, ex; split; [exact He |].
          right; split; [exact Hm |].
          split; [exact Hex | reflexivity].
    - intros [H1 | [H2 | [H3 | H4]]].
      + left; exact H1.
      + destruct H2 as [cp [cA [Hc [Hm [Hcard [a0 [Hmin ->]]]]]]].
        right; left; exists (cp, cA); split; [exact Hc |].
        cbn [fst snd].
        rewrite Hm, Hcard, Hmin; reflexivity.
      + destruct H3 as [cp [cA [Hc [Hm [a0 [Ha0 [Hp0 [w0 [Hcs ->]]]]]]]]].
        right; right; left; exists (cp, cA); split; [exact Hc |].
        cbn beta iota.
        rewrite Hm.
        apply mem_cwSelector.
        exists a0; split; [exact Ha0 |].
        split; [exact Hp0 |].
        exists w0; split; [exact Hcs | reflexivity].
      + destruct H4 as [em [eu [ea [ex [He Hcase]]]]].
        right; right; right; exists ((em, eu), (ea, ex)); split; [exact He |].
        cbn [fst snd].
        destruct Hcase as [[Hm ->] | [Hm [Hex ->]]].
        * rewrite Hm; reflexivity.
        * rewrite Hm, Hex; reflexivity.
  Qed.

  Theorem debian_completeness :
    forall R D Pi G (r : Pkg.t) (S : PkgSet.t),
      IsResolution R D Pi G r S ->
      T.IsResolution (reduceReal R D Pi G) (reduceDeps R D Pi G)
        (embedPkg r) (coreResolution R D Pi G S).
  Proof.
    intros R D Pi G r S [Hsub Hroot Hclo Hconf Huniq].
    assert (Hus : forall (q : Pkg.t) (a : Atom.t),
        PkgSet.In q S -> Match Pi q a ->
        T.VSet.In (chosenVersion q a) (us R Pi a)).
    { intros [qn qv] [an af] HqS HM.
      unfold chosenVersion, rmatchb; cbn [aname aform fst snd].
      destruct (andb (NEqb.eqb qn an) (vfHolds af qv)) eqn:Hr; apply mem_us.
      - apply andb_prop in Hr; destruct Hr as [Hn Hh].
        apply NEqb.eqb_true_iff in Hn as ->.
        left; exists qv; split; [| reflexivity].
        unfold evalAt; cbn [aname aform fst snd]; apply eval_vfHolds.
        split; [| exact Hh].
        apply Ver.realVersions_spec.
        apply Hsub; exact HqS.
      - destruct HM as [[Hfq Hh] | [vt [Hin Hvt]]].
        + exfalso; cbn [aname aform fst snd] in Hfq, Hh.
          subst qn; rewrite NEqb.eqb_refl, Hh in Hr; discriminate Hr.
        + right; exists qn, qv, vt.
          split; [exact Hin | split; [exact Hvt | reflexivity]]. }
    assert (Hfwd : forall (a : Atom.t) (q : Pkg.t) n vs,
        PkgSet.In q S -> Match Pi q a ->
        (exists p A, Deps.In (p, A) D /\ PkgSet.In p S /\
           AtomSet.In a A) ->
        (n, vs) = tgt R Pi a ->
        exists dv, T.VSet.In dv vs /\
          T.PkgSet.In (n, dv) (coreResolution R D Pi G S)).
    { intros a q n vs HqS HM Hcl Heq.
      unfold tgt in Heq.
      destruct (provb Pi a) eqn:Hpb; cbn [andb] in Heq;
        injection Heq as -> ->.
      - assert (Hmb : matchb Pi q a = true) by (apply matchb_iff; exact HM).
        destruct (chooseSatisfier_some Pi S a q HqS Hmb) as [w0 Hcs].
        pose proof (chooseSatisfier_spec Pi S a w0 Hcs)
          as [qn0 [qv0 [Hq0S [Hq0m ->]]]].
        exists (chosenVersion (qn0, qv0) a); split.
        + apply (Hus (qn0, qv0)); [exact Hq0S | apply matchb_iff; exact Hq0m].
        + apply mem_coreResolution.
          right; right; left.
          destruct Hcl as [cp [cA [Hc [HcpS HaA]]]].
          exists cp, cA; split; [exact Hc |].
          split; [apply PkgSet.mem_spec; exact HcpS |].
          exists a; split; [exact HaA |].
          split; [exact Hpb |].
          exists (chosenVersion (qn0, qv0) a); split;
            [exact Hcs | reflexivity].
      - destruct HM as [[Hfq Hh] | [vt [Hin Hvt]]].
        2:{ exfalso.
            assert (Hpb2 : provb Pi a = true)
              by (apply provb_iff; exists q, vt; split; assumption).
            congruence. }
        destruct q as [qn qv]; cbn [fst snd] in Hfq, Hh.
        exists (Version.Orig qv); split.
        + unfold embedVS; apply SOvw.mem_map;
            exists qv; split; [| reflexivity].
          unfold evalAt; apply eval_vfHolds.
          split; [| exact Hh].
          apply Ver.realVersions_spec.
          rewrite <- Hfq.
          apply Hsub; exact HqS.
        + apply mem_coreResolution; left.
          exists (qn, qv); split; [exact HqS |].
          unfold embedPkg; cbn [fst snd].
          rewrite Hfq; reflexivity. }
    constructor.
    - intros y Hy.
      apply mem_coreResolution in Hy.
      destruct Hy as [H1 | [H2 | [H3 | H4]]].
      + destruct H1 as [p [Hp ->]].
        apply (mem_reduceReal R D Pi G
                 (Name.Orig (fst p)) (Version.Orig (snd p))).
        apply versions_orig_spec.
        exists (snd p); split; [| reflexivity].
        rewrite <- (surjective_pairing p); apply Hsub; exact Hp.
      + destruct H2 as [cp [cA [Hc [Hm [Hcard [a0 [Hmin ->]]]]]]].
        apply (mem_reduceReal R D Pi G (Name.Disjunct cA) (Version.Atom a0)).
        apply versions_disjunct_spec.
        split; [apply hasClauseb_iff; exists cp; exact Hc |].
        split; [exact Hcard |].
        unfold versionsDisj; apply SOaw.mem_map.
        apply AtomSet.min_elt_spec1 in Hmin.
        apply mem_satAtoms in Hmin; destruct Hmin as [Ha0 _].
        exists a0; split; [exact Ha0 | reflexivity].
      + destruct H3 as [cp [cA [Hc [Hm [a0 [Ha0 [Hp0 [w0 [Hcs ->]]]]]]]]].
        apply (mem_reduceReal R D Pi G (Name.Selector a0) w0).
        apply versions_selector_spec.
        split; [apply occursAtomb_iff; exists cp, cA; split;
                [exact Hc | exact Ha0] |].
        split; [exact Hp0 |].
        apply chooseSatisfier_spec in Hcs.
        destruct Hcs as [qn [qv [HqS [Hqm ->]]]].
        apply (Hus (qn, qv)); [exact HqS | apply matchb_iff; exact Hqm].
      + destruct H4 as [em [eu [ea [ex [He Hcase]]]]].
        destruct Hcase as [[Hm ->] | [Hm [Hex ->]]].
        * apply (mem_reduceReal R D Pi G
                   (Name.Guard (em, eu) ea ex) Version.One).
          apply versions_guard_spec.
          split; [exact He | right; reflexivity].
        * apply (mem_reduceReal R D Pi G
                   (Name.Guard (em, eu) ea ex) Version.Zero).
          apply versions_guard_spec.
          split; [exact He | left; reflexivity].
    - apply mem_coreResolution; left.
      exists r; split; [exact Hroot | reflexivity].
    - intros y Hy n vs Hd.
      apply mem_coreResolution in Hy.
      apply mem_reduceDeps in Hd; destruct Hd as [_ Hout].
      destruct Hy as [H1 | [H2 | [H3 | H4]]].
      + destruct H1 as [[pn pv] [HpS ->]].
        apply (dependees_orig_spec R D Pi G pn pv) in Hout.
        destruct Hout as [[A [HA Hcase]] |
                          [[a0 [x0 [Ha0 Heq]]] |
                           [m0 [u0 [a0 [x0 [Hg0 [Hm [Hne [Hxq Heq]]]]]]]]]].
        * assert (HpA : Deps.In ((pn, pv), A) D) by exact HA.
          destruct (Hclo (pn, pv) HpS A HpA) as [aw [HawA [q [HqS HqM]]]].
          destruct Hcase as [[Hcard [am [Hmin Heq]]] | [Hcard Heq]].
          { assert (HamA : AtomSet.In am A)
              by (apply AtomSet.min_elt_spec1; exact Hmin).
            assert (Haw : aw = am)
              by (apply Nat.eqb_eq in Hcard;
                  exact (cardinal1_eq A aw am Hcard HawA HamA)).
            subst aw.
            apply (Hfwd am q n vs HqS HqM); [| exact Heq].
            exists (pn, pv), A.
            split; [exact HpA |].
            split; [exact HpS | exact HamA]. }
          { injection Heq as -> ->.
            assert (Hsat : AtomSet.In aw (satAtoms Pi S A)).
            { apply mem_satAtoms; split; [exact HawA |].
              exists q; split; [exact HqS | apply matchb_iff; exact HqM]. }
            destruct (AtomSet.min_elt (satAtoms Pi S A)) as [am |]
              eqn:Hmin.
            2:{ exfalso; apply AtomSet.min_elt_spec3 in Hmin.
                exact (Hmin aw Hsat). }
            assert (Hmin1 := AtomSet.min_elt_spec1 Hmin).
            apply mem_satAtoms in Hmin1; destruct Hmin1 as [HamA _].
            exists (Version.Atom am); split.
            - unfold versionsDisj; apply SOaw.mem_map; exists am; split;
                [exact HamA | reflexivity].
            - apply mem_coreResolution.
              right; left.
              exists (pn, pv), A; split; [exact HpA |].
              split; [apply PkgSet.mem_spec; exact HpS |].
              split.
              { apply Nat.leb_le.
                apply Nat.eqb_neq in Hcard.
                assert (Hle := cardinal_in A aw HawA).
                lia. }
              exists am; split; [exact Hmin | reflexivity]. }
        * injection Heq as -> ->.
          exists Version.One; split.
          { apply T.VSet.singleton_spec; reflexivity. }
          { apply mem_coreResolution.
            right; right; right.
            exists pn, pv, a0, x0; split; [exact Ha0 |].
            left.
            split; [| reflexivity].
            apply PkgSet.mem_spec; exact HpS. }
        * injection Heq as -> ->.
          exists Version.Zero; split.
          { apply T.VSet.singleton_spec; reflexivity. }
          { apply mem_coreResolution.
            right; right; right.
            exists m0, u0, a0, x0; split; [exact Hg0 |].
            right.
            assert (Hp0 : PkgSet.mem (m0, u0) S = false).
            { destruct (PkgSet.mem (m0, u0) S) eqn:Hmem; [| reflexivity].
              exfalso.
              apply PkgSet.mem_spec in Hmem.
              apply (Hconf (m0, u0) Hmem a0 x0 Hg0).
              exists (pn, pv); split; [exact HpS |].
              split; [intro E; apply Hne; rewrite <- E; reflexivity |].
              split; [exact Hxq | apply matchb_iff; exact Hm]. }
            split; [exact Hp0 |].
            split; [| reflexivity].
            rewrite PkgSet.exists_spec'.
            exists (pn, pv); split; [exact HpS |].
            cbn [fst].
            rewrite Hm.
            destruct (Pkg.eq_dec (pn, pv) (m0, u0)) as [E | NE2].
            { exfalso; apply Hne; rewrite <- E; reflexivity. }
            assert (Hx : negb (exemptb x0 pn m0) = true).
            { apply Bool.negb_true_iff, exemptb_iff; exact Hxq. }
            rewrite Hx; reflexivity. }
      + destruct H2 as [cp [cA [Hc [Hmem [Hcard [a0 [Hmin ->]]]]]]].
        apply dependees_disjunct_spec in Hout.
        destruct Hout as (Hhc & Hc2 & Hmm & Heq).
        assert (Hmin1 := AtomSet.min_elt_spec1 Hmin).
        apply mem_satAtoms in Hmin1; destruct Hmin1 as [Ha0A [q [HqS Hqm]]].
        apply (Hfwd a0 q n vs HqS);
          [apply matchb_iff; exact Hqm | | exact Heq].
        exists cp, cA; split; [exact Hc |].
        split; [apply PkgSet.mem_spec; exact Hmem | exact Ha0A].
      + destruct H3 as [cp [cA [Hc [Hmem [a0 [Ha0 [Hpv [w0 [Hcs ->]]]]]]]]].
        pose proof (chooseSatisfier_spec Pi S a0 w0 Hcs)
          as [qn0 [qv0 [Hq0S [Hq0m Ew]]]].
        subst w0.
        unfold chosenVersion, rmatchb in Hout; cbn [fst snd] in Hout.
        destruct (andb (NEqb.eqb qn0 (aname a0)) (vfHolds (aform a0) qv0))
          eqn:Hr.
        * apply dependees_selector_real_spec in Hout.
          destruct Hout as (_ & _ & _ & Heq).
          injection Heq as -> ->.
          apply andb_prop in Hr; destruct Hr as [Hn _].
          apply NEqb.eqb_true_iff in Hn.
          exists (Version.Orig qv0); split.
          { apply T.VSet.singleton_spec; reflexivity. }
          { apply mem_coreResolution; left.
            exists (qn0, qv0); split; [exact Hq0S |].
            unfold embedPkg; cbn [fst snd]; rewrite Hn; reflexivity. }
        * apply dependees_selector_spec in Hout.
          destruct Hout as (_ & _ & _ & Heq).
          injection Heq as -> ->.
          exists (Version.Orig qv0); split.
          { apply T.VSet.singleton_spec; reflexivity. }
          { apply mem_coreResolution; left.
            exists (qn0, qv0); split; [exact Hq0S | reflexivity]. }
      + destruct H4 as [em [eu [ea [ex [He Hcase]]]]];
          destruct Hcase as [[Hg ->] | [Hg [Hex ->]]];
          cbn [dependees] in Hout; exfalso; exact (SOde.empty_in _ Hout).
    - intros nm cv1 cv2 H1 H2.
      apply mem_coreResolution in H1.
      apply mem_coreResolution in H2.
      destruct H1 as [[[n1 v1] [Hp1 E1]] |
                      [[cp1 [cA1 [Hc1 [Hg1 [Hd1 [a1 [Hmin1 E1]]]]]]] |
                       [[cp1 [cA1 [Hc1 [Hg1
                           [a1 [Ha1 [Hpv1 [w1 [Hcs1 E1]]]]]]]]] |
                        [em1 [eu1 [ea1 [ex1
                          [He1 [[Hg1 E1] | [Hg1 [Hex1 E1]]]]]]]]]]];
        cbn [fst snd] in E1; injection E1 as -> ->.
      + destruct H2 as [[[n2 v2] [Hp2 E2]] |
                        [[cp2 [cA2 [Hc2 [Hg2 [Hd2 [a2 [Hmin2 E2]]]]]]] |
                         [[cp2 [cA2 [Hc2 [Hg2
                             [a2 [Ha2 [Hpv2 [w2 [Hcs2 E2]]]]]]]]] |
                          [em2 [eu2 [ea2 [ex2
                            [He2 [[Hg2 E2] | [Hg2 [Hex2 E2]]]]]]]]]]];
          cbn [fst snd] in E2; try discriminate E2.
        injection E2 as <- ->.
        rewrite (Huniq n1 v1 v2 Hp1 Hp2); reflexivity.
      + destruct H2 as [[[n2 v2] [Hp2 E2]] |
                        [[cp2 [cA2 [Hc2 [Hg2 [Hd2 [a2 [Hmin2 E2]]]]]]] |
                         [[cp2 [cA2 [Hc2 [Hg2
                             [a2 [Ha2 [Hpv2 [w2 [Hcs2 E2]]]]]]]]] |
                          [em2 [eu2 [ea2 [ex2
                            [He2 [[Hg2 E2] | [Hg2 [Hex2 E2]]]]]]]]]]];
          cbn [fst snd] in E2; try discriminate E2.
        injection E2 as <- ->.
        congruence.
      + destruct H2 as [[[n2 v2] [Hp2 E2]] |
                        [[cp2 [cA2 [Hc2 [Hg2 [Hd2 [a2 [Hmin2 E2]]]]]]] |
                         [[cp2 [cA2 [Hc2 [Hg2
                             [a2 [Ha2 [Hpv2 [w2 [Hcs2 E2]]]]]]]]] |
                          [em2 [eu2 [ea2 [ex2
                            [He2 [[Hg2 E2] | [Hg2 [Hex2 E2]]]]]]]]]]];
          cbn [fst snd] in E2; try discriminate E2.
        injection E2 as <- ->.
        congruence.
      + destruct H2 as [[[n2 v2] [Hp2 E2]] |
                        [[cp2 [cA2 [Hc2 [Hg2 [Hd2 [a2 [Hmin2 E2]]]]]]] |
                         [[cp2 [cA2 [Hc2 [Hg2
                             [a2 [Ha2 [Hpv2 [w2 [Hcs2 E2]]]]]]]]] |
                          [em2 [eu2 [ea2 [ex2
                            [He2 [[Hg2 E2] | [Hg2 [Hex2 E2]]]]]]]]]]];
          cbn [fst snd] in E2; try discriminate E2.
        * injection E2 as <- <- <- <- ->.
          reflexivity.
        * injection E2 as <- <- <- <- ->.
          congruence.
      + destruct H2 as [[[n2 v2] [Hp2 E2]] |
                        [[cp2 [cA2 [Hc2 [Hg2 [Hd2 [a2 [Hmin2 E2]]]]]]] |
                         [[cp2 [cA2 [Hc2 [Hg2
                             [a2 [Ha2 [Hpv2 [w2 [Hcs2 E2]]]]]]]]] |
                          [em2 [eu2 [ea2 [ex2
                            [He2 [[Hg2 E2] | [Hg2 [Hex2 E2]]]]]]]]]]];
          cbn [fst snd] in E2; try discriminate E2.
        * injection E2 as <- <- <- <- ->.
          congruence.
        * injection E2 as <- <- <- <- ->.
          reflexivity.
  Qed.

  (* The completeness witness puts S in the Orig block and every synthetic
     package it adds carries a Disjunct/Selector/Guard name, so the decoder
     -- which inverts embedPkg exactly on Orig names -- recovers S. *)
  Corollary debianResolution_coreResolution : forall R D Pi G S,
      debianResolution (coreResolution R D Pi G S) = S.
  Proof.
    intros R D Pi G S; apply PkgSet.ext; intros [n v].
    rewrite mem_debianResolution, mem_coreResolution.
    unfold embedPkg; cbn [fst snd].
    split.
    - intros [[q [HqS Hq]] |
              [[cp [cA [_ [_ [_ [a [_ Hy]]]]]]] |
               [[cp [cA [_ [_ [a [_ [_ [w [_ Hy]]]]]]]]] |
                [em [eu [ea [ex [_ [[_ Hy] | [_ [_ Hy]]]]]]]]]]];
        try discriminate Hy.
      destruct q as [qn qv]; unfold embedPkg in Hq; cbn [fst snd] in Hq.
      injection Hq as -> ->; exact HqS.
    - intro H; left; exists (n, v); split; [exact H | reflexivity].
  Qed.

  Module Lookup.

    Definition conflictsAgainst (Pi : Prov.t) (G : Conf.t) (p : Pkg.t) :
        Conf.t :=
      Conf.filter (fun '(q, (a, x)) =>
          andb (matchb Pi p a) (negb (exemptb x (fst p) (fst q))))
        G.

    Definition clausesWith (D : Deps.t) (a : Atom.t) : Deps.t :=
      Deps.filter (fun c => AtomSet.mem a (snd c)) D.

    Module NSet := FSetUOT N.
    Module SOan := SetOps Atom N AtomSet NSet.
    Definition clauseNames (A : AtomSet.t) : NSet.t :=
      SOan.map (fun '(n, _) => n) A.

    Module SOcn := SetOps ClauseElt N Deps NSet.
    Definition atomNames (D : Deps.t) (p : Pkg.t) : NSet.t :=
      SOcn.unionMap (fun '(q, A) =>
          if Pkg.eq_dec q p then clauseNames A else NSet.empty)
        D.

    Module PkgFibred := FibredRel N V Pkg PkgSet.
    Lemma realVersions_tailFibre : forall R n,
        Ver.realVersions (PkgFibred.tailFibre R n) n = Ver.realVersions R n.
    Proof.
      intros R n; apply VSet.ext; intro v.
      rewrite !Ver.realVersions_spec.
      split; [exact (PkgFibred.tailFibre_subset R n (n, v)) |].
      intro H; apply PkgFibred.mem_tailFibre; split; [exact H | reflexivity].
    Qed.

    Lemma evalAt_tailFibre : forall R (n : N.t) (f : Ver.Formula),
        evalAt (PkgFibred.tailFibre R n) (n, f) = evalAt R (n, f).
    Proof.
      intros R n f; unfold evalAt.
      rewrite realVersions_tailFibre; reflexivity.
    Qed.

    Module ProvFibred := FibredLabelledRel Pkg N DTOT ProvElt Prov.
    Lemma provb_nodeFibre : forall Pi (n : N.t) (f : Ver.Formula),
        provb (ProvFibred.nodeFibre Pi n) (n, f) = provb Pi (n, f).
    Proof.
      intros Pi n f; unfold provb.
      apply Prov.exists_restrict; [apply ProvFibred.nodeFibre_subset |].
      intros [q [m vt]] Hin Hb; cbn [aname aform fst snd] in Hb.
      apply andb_prop in Hb; destruct Hb as [Hn _].
      apply ProvFibred.mem_nodeFibre; split;
        [exact Hin | apply NEqb.eqb_true_iff; exact Hn].
    Qed.

    Lemma us_filter : forall R Pi (n : N.t) (f : Ver.Formula),
        us (PkgFibred.tailFibre R n) (ProvFibred.nodeFibre Pi n) (n, f) =
        us R Pi (n, f).
    Proof.
      intros R Pi n f; apply T.VSet.ext; intro y; unfold us.
      rewrite !T.VSet.union_spec, evalAt_tailFibre.
      apply or_iff_compat_l.
      apply SOew.filterMap_restrict; [apply ProvFibred.nodeFibre_subset |].
      intros [q [m vt]] Hin Hf; cbn [fst snd aname aform] in Hf.
      destruct (NEqb.eqb m n) eqn:Hn; [| discriminate Hf].
      apply ProvFibred.mem_nodeFibre; split;
        [exact Hin | apply NEqb.eqb_true_iff; exact Hn].
    Qed.

    Lemma occursAtomb_clausesWith : forall D a,
        occursAtomb (clausesWith D a) a = occursAtomb D a.
    Proof.
      intros D a; unfold occursAtomb, clausesWith.
      apply Deps.exists_restrict;
        [intros c Hc; rewrite Deps.filter_spec' in Hc; exact (proj1 Hc) |].
      intros [p Al] Hc Hb; cbn beta iota in Hb.
      rewrite Deps.filter_spec'; split; [exact Hc | exact Hb].
    Qed.

    (* stated for every candidate shape at once: the real and the provided
       branch of us read the same slice, and the rest are empty *)
    Theorem dependees_lookupSelector :
      forall R D Pi G (n : N.t) (f : Ver.Formula) (y : Version.t),
        occursAtomb D (n, f) = true ->
        dependees R D Pi G (Name.Selector (n, f), y) =
        dependees (PkgFibred.tailFibre R n) (clausesWith D (n, f))
          (ProvFibred.nodeFibre Pi n) Conf.empty
          (Name.Selector (n, f), y).
    Proof.
      intros R D Pi G n f y Hocc; destruct y; cbn [dependees]; try reflexivity;
        rewrite occursAtomb_clausesWith, provb_nodeFibre, us_filter;
        reflexivity.
    Qed.

    Theorem versions_lookupSelector :
      forall R D Pi G (n : N.t) (f : Ver.Formula),
        occursAtomb D (n, f) = true ->
        versions R D Pi G (Name.Selector (n, f)) =
        versions (PkgFibred.tailFibre R n) (clausesWith D (n, f))
          (ProvFibred.nodeFibre Pi n) Conf.empty
          (Name.Selector (n, f)).
    Proof.
      intros R D Pi G n f Hocc; cbn [versions].
      rewrite occursAtomb_clausesWith, provb_nodeFibre, us_filter.
      reflexivity.
    Qed.

    Lemma mem_clauseNames : forall A (n : N.t),
        NSet.In n (clauseNames A) <-> exists f, AtomSet.In (n, f) A.
    Proof.
      intros A n; unfold clauseNames; rewrite SOan.mem_map.
      split.
      - intros [[m f] [Ha Hn]].
        cbn beta iota in Hn; subst m; exists f; exact Ha.
      - intros [f Ha].
        exists (n, f); split; [exact Ha | reflexivity].
    Qed.

    Lemma mem_atomNames : forall D (p : Pkg.t) (n : N.t),
        NSet.In n (atomNames D p) <->
        exists A, Deps.In (p, A) D /\ exists f, AtomSet.In (n, f) A.
    Proof.
      intros D p n; unfold atomNames; rewrite SOcn.mem_unionMap.
      split.
      - intros [[q A] [Hc Hn]]; cbn beta iota in Hn.
        destruct (Pkg.eq_dec q p) as [-> | NE];
          [| exfalso; exact (SOcn.empty_in _ Hn)].
        apply mem_clauseNames in Hn.
        exists A; split; assumption.
      - intros [A [Hc Hf]].
        exists (p, A); split; [exact Hc | cbn beta iota].
        destruct (Pkg.eq_dec p p) as [_ | NE];
          [| contradiction NE; reflexivity].
        apply mem_clauseNames; exact Hf.
    Qed.

    Module PkgPreimage := PreimageOfKeys N Pkg NSet PkgSet.
    Definition realPreimage (R : PkgSet.t) (ns : NSet.t) : PkgSet.t :=
      PkgPreimage.ofKeys fst ns R.

    Module ProvPreimage := PreimageOfKeys N ProvElt NSet Prov.
    Definition provPreimage (Pi : Prov.t) (ns : NSet.t) : Prov.t :=
      ProvPreimage.ofKeys ProvFibred.node ns Pi.

    Lemma realVersions_realPreimage : forall R ns m,
        NSet.In m ns ->
        Ver.realVersions (realPreimage R ns) m = Ver.realVersions R m.
    Proof.
      intros R ns m Hm; apply VSet.ext; intro v.
      rewrite !Ver.realVersions_spec; unfold realPreimage.
      rewrite PkgPreimage.mem_ofKeys.
      split.
      - intros [H _]; exact H.
      - intro H; split; [exact H | exact Hm].
    Qed.

    Lemma evalAt_realPreimage : forall R ns (n : N.t) (f : Ver.Formula),
        NSet.In n ns ->
        evalAt (realPreimage R ns) (n, f) = evalAt R (n, f).
    Proof.
      intros R ns n f Hm; unfold evalAt.
      rewrite realVersions_realPreimage by exact Hm; reflexivity.
    Qed.

    (* The three restriction lemmas below all read the same slice of Pi. *)
    Lemma provSlice_sub : forall Pi ns (p : Pkg.t),
        Prov.Subset
          (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p)) Pi.
    Proof.
      intros Pi ns p e He; apply Prov.union_spec in He.
      destruct He as [He | He];
        [exact (ProvPreimage.ofKeys_subset _ _ _ _ He)
        | exact (ProvFibred.tailFibre_subset _ _ _ He)].
    Qed.

    Lemma provb_union_restrict :
      forall Pi ns (p : Pkg.t) (n : N.t) (f : Ver.Formula),
        NSet.In n ns ->
        provb (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p))
          (n, f)
        = provb Pi (n, f).
    Proof.
      intros Pi ns p n f Hm; unfold provb.
      apply Prov.exists_restrict; [apply provSlice_sub |].
      intros [q [m vt]] Hin Hb; cbn [aname aform fst snd] in Hb.
      apply andb_prop in Hb; destruct Hb as [Hn _].
      apply NEqb.eqb_true_iff in Hn as ->.
      apply Prov.union_spec; left; unfold provPreimage.
      apply ProvPreimage.mem_ofKeys; split; [exact Hin | exact Hm].
    Qed.

    Lemma us_union_restrict :
      forall R Pi ns (p : Pkg.t) (n : N.t) (f : Ver.Formula),
        NSet.In n ns ->
        us (realPreimage R ns)
          (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p))
          (n, f)
        = us R Pi (n, f).
    Proof.
      intros R Pi ns p n f Hm; apply T.VSet.ext; intro y; unfold us.
      rewrite !T.VSet.union_spec, evalAt_realPreimage by exact Hm.
      apply or_iff_compat_l.
      apply SOew.filterMap_restrict; [apply provSlice_sub |].
      intros [q [m vt]] Hin Hf; cbn [fst snd aname aform] in Hf.
      destruct (NEqb.eqb m n) eqn:Hn; [| discriminate Hf].
      apply NEqb.eqb_true_iff in Hn as ->.
      apply Prov.union_spec; left; unfold provPreimage.
      apply ProvPreimage.mem_ofKeys; split; [exact Hin | exact Hm].
    Qed.

    Lemma tgt_union_restrict :
      forall R Pi ns (p : Pkg.t) (n : N.t) (f : Ver.Formula),
        NSet.In n ns ->
        tgt (realPreimage R ns)
          (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p))
          (n, f)
        = tgt R Pi (n, f).
    Proof.
      intros R Pi ns p n f Hm; unfold tgt.
      rewrite provb_union_restrict, us_union_restrict, evalAt_realPreimage
        by exact Hm.
      reflexivity.
    Qed.

    (* At package p itself, matchb only reads Pi entries whose package
       component is p, and those survive intact in the ProvFibred.tailFibre
       component of the union. *)
    Lemma matchb_union_restrict : forall Pi ns (p : Pkg.t) a,
        matchb (Prov.union (provPreimage Pi ns) (ProvFibred.tailFibre Pi p))
          p a
        = matchb Pi p a.
    Proof.
      intros Pi ns p a; unfold matchb; f_equal.
      apply Prov.exists_restrict; [apply provSlice_sub |].
      intros [q [m vt]] Hin Hb; cbn [fst snd aname aform] in Hb.
      apply andb_prop in Hb; destruct Hb as [Hq _].
      apply PkgEqb.eqb_true_iff in Hq as ->.
      apply Prov.union_spec; right.
      apply ProvFibred.mem_tailFibre; split; [exact Hin | reflexivity].
    Qed.

    Module DepsFibred := FibredRel Pkg AtomSet.AsUOT ClauseElt Deps.
    Module ConfFibred := FibredRel Pkg Conflictees ConfElt Conf.
    Theorem dependees_lookupOrig : forall R D Pi G n v,
        dependees R D Pi G (Name.Orig n, Version.Orig v) =
        dependees (realPreimage R (atomNames D (n, v)))
          (DepsFibred.tailFibre D (n, v))
          (Prov.union (provPreimage Pi (atomNames D (n, v)))
             (ProvFibred.tailFibre Pi (n, v)))
          (Conf.union (ConfFibred.tailFibre G (n, v))
             (conflictsAgainst Pi G (n, v)))
          (Name.Orig n, Version.Orig v).
    Proof.
      intros R D Pi G n v; apply T.DependeesSet.ext; intro y.
      rewrite !dependees_orig_spec.
      split.
      - intros [[A [HA Hcase]] |
                [[a [x [Ha Hy]]] |
                 [m0 [u0 [a [x [Hg [Hmb [Hne [Hex Hy]]]]]]]]]].
        + left; exists A; split.
          * unfold DepsFibred.tailFibre.
            rewrite Deps.filter_spec'.
            split; [exact HA | cbn [DepsFibred.tail fst]].
            destruct (Pkg.eq_dec (n, v) (n, v)) as [_ | NE];
              [reflexivity | contradiction NE; reflexivity].
          * destruct Hcase as [[Hcard [a0 [Hmin Hy]]] | [Hcard Hy]].
            { destruct a0 as [an af].
              assert (Hin : NSet.In an (atomNames D (n, v))).
              { apply mem_atomNames; exists A; split; [exact HA |].
                exists af; exact (AtomSet.min_elt_spec1 Hmin). }
              left; split; [exact Hcard |].
              exists (an, af); split; [exact Hmin |].
              rewrite tgt_union_restrict by exact Hin.
              exact Hy. }
            { right; split; [exact Hcard | exact Hy]. }
        + right; left; exists a, x; split; [| exact Hy].
          apply Conf.union_spec; left.
          unfold ConfFibred.tailFibre.
          rewrite Conf.filter_spec'.
          split; [exact Ha | cbn [ConfFibred.tail fst]].
          destruct (Pkg.eq_dec (n, v) (n, v)) as [_ | NE];
            [reflexivity | contradiction NE; reflexivity].
        + right; right; exists m0, u0, a, x.
          split.
          * apply Conf.union_spec; right.
            unfold conflictsAgainst.
            rewrite Conf.filter_spec'.
            split; [exact Hg | cbn [fst snd]].
            rewrite Hmb; cbn [andb].
            apply Bool.negb_true_iff, exemptb_iff; exact Hex.
          * split; [rewrite matchb_union_restrict; exact Hmb |].
            split; [exact Hne |].
            split; [exact Hex | exact Hy].
      - intros [[A [HA Hcase]] |
                [[a [x [Ha Hy]]] |
                 [m0 [u0 [a [x [Hg [Hmb [Hne [Hex Hy]]]]]]]]]].
        + unfold DepsFibred.tailFibre in HA.
          rewrite Deps.filter_spec' in HA.
          destruct HA as [HA _].
          left; exists A; split; [exact HA |].
          destruct Hcase as [[Hcard [a0 [Hmin Hy]]] | [Hcard Hy]].
          * destruct a0 as [an af].
            assert (Hin : NSet.In an (atomNames D (n, v))).
            { apply mem_atomNames; exists A; split; [exact HA |].
              exists af; exact (AtomSet.min_elt_spec1 Hmin). }
            left; split; [exact Hcard |].
            exists (an, af); split; [exact Hmin |].
            rewrite tgt_union_restrict in Hy by exact Hin.
            exact Hy.
          * right; split; [exact Hcard | exact Hy].
        + assert (HaG : Conf.In ((n, v), (a, x)) G).
          { apply Conf.union_spec in Ha.
            destruct Ha as [Ha | Ha];
              [unfold ConfFibred.tailFibre in Ha
              | unfold conflictsAgainst in Ha];
              rewrite Conf.filter_spec' in Ha;
              exact (proj1 Ha). }
          right; left; exists a, x; split; [exact HaG | exact Hy].
        + rewrite matchb_union_restrict in Hmb.
          assert (HgG : Conf.In ((m0, u0), (a, x)) G).
          { apply Conf.union_spec in Hg.
            destruct Hg as [Hg | Hg];
              [unfold ConfFibred.tailFibre in Hg
              | unfold conflictsAgainst in Hg];
              rewrite Conf.filter_spec' in Hg;
              exact (proj1 Hg). }
          right; right; exists m0, u0, a, x.
          split; [exact HgG |].
          split; [exact Hmb |].
          split; [exact Hne |].
          split; [exact Hex | exact Hy].
    Qed.

    Theorem versions_lookupOrig : forall R D Pi G n,
        versions R D Pi G (Name.Orig n) =
        versions (PkgFibred.tailFibre R n) Deps.empty Prov.empty Conf.empty
          (Name.Orig n).
    Proof.
      intros R D Pi G n; cbn [versions].
      rewrite realVersions_tailFibre; reflexivity.
    Qed.

    Lemma hasClauseb_headFibre : forall D A,
        hasClauseb (DepsFibred.headFibre D A) A = hasClauseb D A.
    Proof.
      intros D A; unfold hasClauseb.
      apply Deps.exists_restrict; [apply DepsFibred.headFibre_subset |].
      intros [p Al] Hc Hb; cbn beta iota in Hb.
      apply DepsFibred.mem_headFibre; split;
        [exact Hc | apply ASEqb.eqb_true_iff; exact Hb].
    Qed.

    Theorem versions_lookupDisjunct : forall R D Pi G A,
        versions R D Pi G (Name.Disjunct A) =
        versions PkgSet.empty (DepsFibred.headFibre D A) Prov.empty Conf.empty
          (Name.Disjunct A).
    Proof.
      intros R D Pi G A; cbn [versions].
      rewrite hasClauseb_headFibre; reflexivity.
    Qed.

    Theorem dependees_lookupDisjunct :
      forall R D Pi G A (n : N.t) (f : Ver.Formula),
        dependees R D Pi G (Name.Disjunct A, Version.Atom (n, f)) =
        dependees (PkgFibred.tailFibre R n) (DepsFibred.headFibre D A)
          (ProvFibred.nodeFibre Pi n) Conf.empty
          (Name.Disjunct A, Version.Atom (n, f)).
    Proof.
      intros R D Pi G A n f; cbn [dependees].
      rewrite hasClauseb_headFibre.
      unfold tgt.
      rewrite provb_nodeFibre, us_filter, evalAt_tailFibre.
      reflexivity.
    Qed.

    Lemma memb_fibre : forall G (p : Pkg.t) (a : Atom.t) (x : bool),
        Conf.mem (p, (a, x)) (ConfFibred.tailFibre G p) =
        Conf.mem (p, (a, x)) G.
    Proof.
      intros G p a x; apply Conf.mem_restrict;
        [apply ConfFibred.tailFibre_subset |].
      intro H; apply ConfFibred.mem_tailFibre; split; [exact H | reflexivity].
    Qed.

    Theorem versions_lookupGuard :
      forall R D Pi G (p : Pkg.t) (a : Atom.t) (x : bool),
        versions R D Pi G (Name.Guard p a x) =
        versions PkgSet.empty Deps.empty Prov.empty (ConfFibred.tailFibre G p)
          (Name.Guard p a x).
    Proof.
      intros R D Pi G p a x; cbn [versions].
      rewrite memb_fibre; reflexivity.
    Qed.

    Theorem dependees_lookupGuard :
      forall R D Pi G (p : Pkg.t) (a : Atom.t) (x : bool) w,
        dependees R D Pi G (Name.Guard p a x, w) = T.DependeesSet.empty.
    Proof. intros R D Pi G p a x w; destruct w; reflexivity. Qed.
  End Lookup.
End Debian.
