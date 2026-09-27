From Stdlib Require Import MSets List Bool.
From PackageCalculus Require Import Prelude Core Versions Semver Concurrent.

Create HintDb cmp_npm.
Create Rewrite HintDb cmp_npm.

Module Npm (N V : UsualOrderedType) (PM : SemverMatch V).
  (* Module application is generative, so the concurrent instance is the
     only one: every set keyed by source names goes through C. *)
  Module NKey := PairUOT N N.
  Module Conc := Concurrent NKey V V.
  Module C := Conc.C.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.

  Module KVK := TripleUOT NKey V NKey.
  Module KVN := TripleUOT NKey V N.
  Module KVKVN := TripleUOT NKey V KVN.
  Module NNN := TripleUOT N N N.
  Module NNNF := UOTCompareFacts NNN.
  Module PkgF := UOTCompareFacts Pkg.
  Module KVKF := UOTCompareFacts KVK.
  Module KVNF := UOTCompareFacts KVN.
  Module KVKVNF := UOTCompareFacts KVKVN.
  Module VF := UOTCompareFacts V.
  #[local] Hint Rewrite PkgF.compare_eq_iff KVKF.compare_eq_iff
    KVNF.compare_eq_iff KVKVNF.compare_eq_iff VF.compare_eq_iff
    NNNF.compare_eq_iff : cmp_npm.
  #[local] Hint Extern 1 => cmp_by NNNF.compare_antisym : cmp_npm.
  #[local] Hint Extern 1 => cmp_by NNNF.compare_lt_trans : cmp_npm.
  #[local] Hint Extern 1 => cmp_by PkgF.compare_antisym : cmp_npm.
  #[local] Hint Extern 1 => cmp_by KVKF.compare_antisym : cmp_npm.
  #[local] Hint Extern 1 => cmp_by KVNF.compare_antisym : cmp_npm.
  #[local] Hint Extern 1 => cmp_by KVKVNF.compare_antisym : cmp_npm.
  #[local] Hint Extern 1 => cmp_by VF.compare_antisym : cmp_npm.
  #[local] Hint Extern 1 => cmp_by PkgF.compare_lt_trans : cmp_npm.
  #[local] Hint Extern 1 => cmp_by KVKF.compare_lt_trans : cmp_npm.
  #[local] Hint Extern 1 => cmp_by KVNF.compare_lt_trans : cmp_npm.
  #[local] Hint Extern 1 => cmp_by KVKVNF.compare_lt_trans : cmp_npm.
  #[local] Hint Extern 1 => cmp_by VF.compare_lt_trans : cmp_npm.

  Module Nm.
    Inductive name : Type :=
    | Granular (k : NKey.t) (w : V.t)
    | Intermediate (k : NKey.t) (v : V.t) (m : NKey.t)
    | Sight (k : NKey.t) (v : V.t) (a : N.t)
    | Link (k : NKey.t) (v : V.t) (m : NKey.t) (u : V.t) (a : N.t)
    | Desc (a : N.t) (t : N.t) (s : N.t).
    Definition t := name.

    Definition rank (x : t) : nat :=
      match x with
      | Granular _ _ => 0 | Intermediate _ _ _ => 1
      | Sight _ _ _ => 2 | Link _ _ _ _ _ => 3 | Desc _ _ _ => 4
      end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq =>
          match x, y with
          | Granular k1 w1, Granular k2 w2 => Pkg.compare (k1, w1) (k2, w2)
          | Intermediate k1 v1 m1, Intermediate k2 v2 m2 =>
              KVK.compare (k1, (v1, m1)) (k2, (v2, m2))
          | Sight k1 v1 a1, Sight k2 v2 a2 =>
              KVN.compare (k1, (v1, a1)) (k2, (v2, a2))
          | Link k1 v1 m1 u1 a1, Link k2 v2 m2 u2 a2 =>
              KVKVN.compare (k1, (v1, (m1, (u1, a1))))
                (k2, (v2, (m2, (u2, a2))))
          | Desc a1 t1 s1, Desc a2 t2 s2 =>
              NNN.compare (a1, (t1, s1)) (a2, (t2, s2))
          | _, _ => Eq
          end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_npm. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_npm. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_npm. Qed.
  End Nm.

  Module Vs.
    Inductive version : Type :=
    | Orig (v : V.t)
    | Bot
    | Free.
    Definition t := version.

    Definition rank (x : t) : nat :=
      match x with Orig _ => 0 | Bot => 1 | Free => 2 end.

    Definition compare (x y : t) : comparison :=
      match Nat.compare (rank x) (rank y) with
      | Eq => match x, y with
              | Orig v1, Orig v2 => V.compare v1 v2
              | _, _ => Eq
              end
      | c => c
      end.

    Lemma compare_eq_iff : forall x y, compare x y = Eq <-> x = y.
    Proof. cmp_eq_iff cmp_npm. Qed.

    Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
    Proof. cmp_antisym cmp_npm. Qed.

    Lemma compare_lt_trans : forall x y z,
        compare x y = Lt -> compare y z = Lt -> compare x z = Lt.
    Proof. cmp_lt_trans cmp_npm. Qed.
  End Vs.

  Module NmOT := UOTFromCompare Nm.
  Module VsOT := UOTFromCompare Vs.
  Module T := Core NmOT VsOT.
  Module SOvcv := SetOps V VsOT VSet T.VSet.
  Module SOptp := SetOps Pkg T.Pkg PkgSet T.PkgSet.
  Module SOtpp := SetOps T.Pkg Pkg T.PkgSet PkgSet.

  Module RPkg := PairUOT N V.
  Module RepoSet := FSetUOT RPkg.
  Module KeySet := FSetUOT NKey.
  Module NSet := FSetUOT N.
  Module NmSet := FSetUOT NmOT.

  Module NEqb := UOTEqb N.
  Module VEqb := UOTEqb V.
  Module RPkgEqb := UOTEqb RPkg.
  Module KeyEqb := UOTEqb NKey.
  Module PkgEqb := UOTEqb Pkg.

  Module RSS := SetSpecs RPkg RepoSet.

  Module SOkk := SetOps NKey NKey KeySet KeySet.
  Module SOnn := SetOps N N NSet NSet.
  Module SOhh := SetOps T.Dependees T.Dependees T.DependeesSet
    T.DependeesSet.
  Module SOrv := SetOps RPkg V RepoSet VSet.
  Module SOnk := SetOps N NKey NSet KeySet.
  Module SOkp := SetOps NKey Pkg KeySet PkgSet.
  Module SOvp := SetOps V Pkg VSet PkgSet.
  Module SOpn := SetOps Pkg NmOT PkgSet NmSet.
  Module SOnm := SetOps NKey NmOT KeySet NmSet.
  Module SOam := SetOps N NmOT NSet NmSet.
  Module SOvm := SetOps V NmOT VSet NmSet.
  Module SOmt := SetOps NmOT T.Pkg NmSet T.PkgSet.
  Module SOwt := SetOps VsOT T.Pkg T.VSet T.PkgSet.
  Module SOhd := SetOps T.Dependees T.DepElt T.DependeesSet T.DepRel.
  Module SOqd := SetOps T.Pkg T.DepElt T.PkgSet T.DepRel.
  Module SOtp := SetOps T.Pkg Conc.ParentElt T.PkgSet Conc.ParentRel.
  Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
  Module SOkt := SetOps NKey T.Pkg KeySet T.PkgSet.
  Module SOvt := SetOps V T.Pkg VSet T.PkgSet.
  Module SOat := SetOps N T.Pkg NSet T.PkgSet.

  Module Sv := Semver V VSet PM.
  Include Sv.

  Record Dependency : Type := MkDep
    { d_dir : N.t
    ; d_target : N.t
    ; d_range : Range
    ; d_dev : bool
    ; d_desc : option N.t }.

  Record PeerDependency : Type := MkPeer
    { p_name : N.t
    ; p_range : Range
    ; p_optional : bool
    ; p_root : bool }.

  (* The relation fields are lists: they feed only the spec and the
     translation, and sets would demand a comparator for Range used
     nowhere. *)
  Record Inst : Type := MkInst
    { inst_repo : RepoSet.t
    ; inst_dep : list (RPkg.t * Dependency)
    ; inst_peer : list (RPkg.t * PeerDependency)
    ; inst_ovr : list (N.t * Range)
    ; inst_root : RPkg.t }.

  Definition ownedBy {A : Type} (p : RPkg.t) (l : list (RPkg.t * A))
    : list A :=
    fold_right
      (fun q acc => if RPkgEqb.eqb (fst q) p then snd q :: acc else acc)
      nil l.

  Lemma in_ownedBy : forall (A : Type) (l : list (RPkg.t * A)) p a,
      In a (ownedBy p l) <-> In (p, a) l.
  Proof.
    intros A l p a; induction l as [| [q b] l IH]; simpl.
    - split; intros [].
    - destruct (RPkgEqb.eqb q p) eqn:Hq.
      + apply RPkgEqb.eqb_true_iff in Hq; subst q; simpl.
        split.
        * intros [-> | H]; [left; reflexivity | right; apply IH; exact H].
        * intros [H | H]; [| right; apply IH; exact H].
          assert (b = a) by congruence; subst b; left; reflexivity.
      + rewrite IH; split; [intro H; right; exact H |].
        intros [H | H]; [| exact H].
        assert (q = p) by congruence; subst q.
        rewrite RPkgEqb.eqb_refl in Hq; discriminate.
  Qed.

  Lemma ownedBy_filter : forall (A : Type) (l : list (RPkg.t * A)) f p,
      (forall a, In (p, a) l -> f (p, a) = true) ->
      ownedBy p (List.filter f l) = ownedBy p l.
  Proof.
    intros A l f p; induction l as [| [q b] l IH]; simpl; [reflexivity |].
    intro H.
    assert (Htl : forall a, In (p, a) l -> f (p, a) = true)
      by (intros a Ha; apply H; right; exact Ha).
    destruct (RPkgEqb.eqb q p) eqn:Hq.
    - apply RPkgEqb.eqb_true_iff in Hq; subst q.
      rewrite (H b (or_introl eq_refl)); simpl.
      rewrite RPkgEqb.eqb_refl, (IH Htl); reflexivity.
    - destruct (f (q, b)); simpl; rewrite ?Hq; exact (IH Htl).
  Qed.

  Definition keysOfL {A : Type} (f : A -> NKey.t) (l : list A) : KeySet.t :=
    SOkk.ofList (List.map f l).

  Lemma mem_keysOfL : forall (A : Type) (f : A -> NKey.t) l k,
      KeySet.In k (keysOfL f l) <-> exists a, In a l /\ f a = k.
  Proof.
    intros A f l k; unfold keysOfL; rewrite SOkk.mem_ofList, in_map_iff.
    split; intros [a [H1 H2]]; exists a; split; assumption.
  Qed.

  Definition namesOfL {A : Type} (f : A -> N.t) (l : list A) : NSet.t :=
    SOnn.ofList (List.map f l).

  Lemma mem_namesOfL : forall (A : Type) (f : A -> N.t) l n,
      NSet.In n (namesOfL f l) <-> exists a, In a l /\ f a = n.
  Proof.
    intros A f l n; unfold namesOfL; rewrite SOnn.mem_ofList, in_map_iff.
    split; intros [a [H1 H2]]; exists a; split; assumption.
  Qed.

  Definition depsOfL {A : Type} (f : A -> T.Dependees.t) (l : list A)
    : T.DependeesSet.t :=
    SOhh.ofList (List.map f l).

  Lemma mem_depsOfL : forall (A : Type) (f : A -> T.Dependees.t) l h,
      T.DependeesSet.In h (depsOfL f l) <-> exists a, In a l /\ f a = h.
  Proof.
    intros A f l h; unfold depsOfL; rewrite SOhh.mem_ofList, in_map_iff.
    split; intros [a [H1 H2]]; exists a; split; assumption.
  Qed.

  Definition realVersions (R : RepoSet.t) (n : N.t) : VSet.t :=
    SOrv.filterMap
      (fun q => if NEqb.eqb (fst q) n then Some (snd q) else None) R.

  Lemma mem_realVersions : forall R n v,
      VSet.In v (realVersions R n) <-> RepoSet.In (n, v) R.
  Proof.
    intros R n v; unfold realVersions; rewrite SOrv.mem_filterMap_if.
    split.
    - intros [[m u] [HR [Hm ->]]]; cbn [fst snd] in *.
      apply NEqb.eqb_true_iff in Hm; subst m; exact HR.
    - intro H; exists (n, v); cbn [fst snd]; rewrite NEqb.eqb_refl; auto.
  Qed.

  Fixpoint lookupOvr (l : list (N.t * Range)) (n : N.t) : option Range :=
    match l with
    | nil => None
    | (m, rg) :: l' => if NEqb.eqb m n then Some rg else lookupOvr l' n
    end.

  Definition override (I : Inst) (n : N.t) (rg : Range) : Range :=
    match lookupOvr (inst_ovr I) n with
    | Some rg' => rg'
    | None => rg
    end.

  Definition depActive (I : Inst) (p : RPkg.t) (d : Dependency) : bool :=
    orb (negb (d_dev d)) (RPkgEqb.eqb p (inst_root I)).

  Definition dependenciesOf (I : Inst) (p : RPkg.t) : list Dependency :=
    List.filter (depActive I p) (ownedBy p (inst_dep I)).

  Fixpoint findDepL (l : list Dependency) (a : N.t) : option Dependency :=
    match l with
    | nil => None
    | d :: l' => if NEqb.eqb (d_dir d) a then Some d else findDepL l' a
    end.

  Definition slotOf (I : Inst) (p : RPkg.t) (a : N.t) : option Dependency :=
    findDepL (dependenciesOf I p) a.

  Definition dirs (I : Inst) (p : RPkg.t) : NSet.t :=
    namesOfL d_dir (dependenciesOf I p).

  Lemma findDepL_some : forall l a d,
      findDepL l a = Some d -> In d l /\ d_dir d = a.
  Proof.
    intros l a d; induction l as [| e l IH]; simpl; [discriminate |].
    destruct (NEqb.eqb (d_dir e) a) eqn:He.
    - intro H; injection H as <-.
      split; [left; reflexivity | apply NEqb.eqb_true_iff; exact He].
    - intro H; destruct (IH H) as [H1 H2]; split; [right; exact H1 | exact H2].
  Qed.

  Lemma findDepL_none : forall l a,
      findDepL l a = None -> forall d, In d l -> d_dir d <> a.
  Proof.
    intros l a; induction l as [| e l IH]; simpl; [intros _ d [] |].
    destruct (NEqb.eqb (d_dir e) a) eqn:He; [discriminate |].
    intros H d [-> | Hd].
    - intro Hc; rewrite Hc, NEqb.eqb_refl in He; discriminate.
    - exact (IH H d Hd).
  Qed.

  Definition slotKey (I : Inst) (p : RPkg.t) (a : N.t) : NKey.t :=
    match slotOf I p a with
    | Some d => (a, d_target d)
    | None => (a, a)
    end.

  Lemma slotKey_fst : forall I p a, fst (slotKey I p a) = a.
  Proof. intros I p a; unfold slotKey; destruct (slotOf I p a); reflexivity.
  Qed.

  Definition slotCands (I : Inst) (p : RPkg.t) (a : N.t)
    : VSet.t :=
    match slotOf I p a with
    | Some d => rangeEval (override I (d_target d) (d_range d))
                  (realVersions (inst_repo I) (d_target d))
    | None => VSet.empty
    end.

  Lemma slotCands_real : forall I p a v,
      VSet.In v (slotCands I p a) ->
      RepoSet.In (snd (slotKey I p a), v) (inst_repo I).
  Proof.
    intros I p a v Hv; unfold slotCands, slotKey in *.
    destruct (slotOf I p a) as [d |]; [| destruct (SOrv.empty_in _ Hv)].
    apply mem_rangeEval in Hv; destruct Hv as [Hv _]; simpl.
    apply mem_realVersions; exact Hv.
  Qed.

  Definition peerDependenciesAt (I : Inst) (p : RPkg.t) : list PeerDependency :=
    ownedBy p (inst_peer I).

  Definition peerNames (I : Inst) (p : RPkg.t) : NSet.t :=
    namesOfL p_name (peerDependenciesAt I p).

  Lemma mem_peerNames : forall I p a,
      NSet.In a (peerNames I p) <->
      exists r, In (p, r) (inst_peer I) /\ p_name r = a.
  Proof.
    intros I p a; unfold peerNames, peerDependenciesAt; rewrite mem_namesOfL.
    split; intros [r [Hr He]]; exists r; split; try exact He;
      apply in_ownedBy; exact Hr.
  Qed.

  Definition peerKeyAt (I : Inst) (p : RPkg.t) (r : PeerDependency) : NKey.t :=
    slotKey I p (p_name r).

  Definition peerCandsAt (I : Inst) (p : RPkg.t)
      (r : PeerDependency) : VSet.t :=
    rangeEval (override I (snd (peerKeyAt I p r)) (p_range r))
      (realVersions (inst_repo I) (snd (peerKeyAt I p r))).

  Definition peerActive (I : Inst) (p : RPkg.t) (r : PeerDependency) : bool :=
    orb (negb (p_optional r)) (NSet.mem (p_name r) (dirs I p)).

  Definition activePeers (I : Inst) (p : RPkg.t) (q : RPkg.t)
    : list PeerDependency :=
    List.filter (peerActive I p) (peerDependenciesAt I q).

  Definition base (q : Pkg.t) : RPkg.t := (snd (fst q), snd q).

  Definition rootKey (I : Inst) : NKey.t :=
    (fst (inst_root I), fst (inst_root I)).

  Definition rootPkg (I : Inst) : Pkg.t :=
    (rootKey I, snd (inst_root I)).

  Lemma base_rootPkg : forall I, base (rootPkg I) = inst_root I.
  Proof.
    intro I; unfold base, rootPkg, rootKey; destruct (inst_root I);
      reflexivity.
  Qed.

  Definition peerDirs (I : Inst) : NSet.t :=
    namesOfL (fun q => p_name (snd q)) (inst_peer I).

  Lemma peerDirs_peer : forall I q r,
      In (q, r) (inst_peer I) -> NSet.In (p_name r) (peerDirs I).
  Proof.
    intros I q r Hr; unfold peerDirs; apply mem_namesOfL.
    exists (q, r); split; [exact Hr | reflexivity].
  Qed.

  Definition rootPeerDirs (I : Inst) : NSet.t :=
    namesOfL (fun q => p_name (snd q))
      (List.filter (fun q => p_root (snd q)) (inst_peer I)).

  Lemma mem_rootPeerDirs : forall I a,
      NSet.In a (rootPeerDirs I) <->
      exists q r, In (q, r) (inst_peer I) /\ p_root r = true /\ p_name r = a.
  Proof.
    intros I a; unfold rootPeerDirs; rewrite mem_namesOfL; split.
    - intros [[q r] [Hin E]]; apply List.filter_In in Hin.
      exists q, r; split; [exact (proj1 Hin) | split; [exact (proj2 Hin) | exact E]].
    - intros [q [r [Hin [Hr E]]]]; exists (q, r); split; [| exact E].
      apply List.filter_In; split; assumption.
  Qed.

  Lemma rootPeerDirs_peerDirs : forall I a,
      NSet.In a (rootPeerDirs I) -> NSet.In a (peerDirs I).
  Proof.
    intros I a H; apply mem_rootPeerDirs in H; destruct H as [q [r [Hin [_ <-]]]].
    exact (peerDirs_peer I q r Hin).
  Qed.

  Definition childDirs (I : Inst) (q : Pkg.t) : NSet.t :=
    if PkgEqb.eqb q (rootPkg I)
    then NSet.union (dirs I (base q)) (peerDirs I)
    else dirs I (base q).

  Definition childKeys (I : Inst) (q : Pkg.t) : KeySet.t :=
    SOnk.map (slotKey I (base q)) (childDirs I q).

  Definition holds (I : Inst) (q : Pkg.t) (a : N.t) : bool :=
    orb (PkgEqb.eqb q (rootPkg I)) (NSet.mem a (dirs I (base q))).

  Definition chains (I : Inst) (q : Pkg.t) (a : N.t) : bool :=
    andb (negb (PkgEqb.eqb q (rootPkg I))) (NSet.mem a (peerNames I (base q))).

  Definition dp (I : Inst) (q : Pkg.t) (a : N.t) : bool :=
    andb (chains I q a) (NSet.mem a (dirs I (base q))).

  Definition loose (I : Inst) (q : Pkg.t) (a : N.t) : bool :=
    orb (andb (PkgEqb.eqb q (rootPkg I)) (negb (NSet.mem a (dirs I (base q)))))
      (dp I q a).

  Definition selfb (q : Pkg.t) (a : N.t) : bool :=
    andb (NEqb.eqb (fst (fst q)) a) (NEqb.eqb (snd (fst q)) a).

  Definition childCands (I : Inst) (q : Pkg.t)
      (m : NKey.t) : VSet.t :=
    if KeyEqb.eqb m (slotKey I (base q) (fst m))
    then if NSet.mem (fst m) (dirs I (base q))
         then slotCands I (base q) (fst m)
         else if chains I q (fst m) then VSet.empty
         else if andb (PkgEqb.eqb q (rootPkg I)) (NSet.mem (fst m) (rootPeerDirs I))
              then realVersions (inst_repo I) (snd m)
              else VSet.empty
    else VSet.empty.

  Definition keysOf (I : Inst) : KeySet.t :=
    KeySet.add (rootKey I)
      (KeySet.union
         (keysOfL (fun q => (d_dir (snd q), d_target (snd q)))
            (inst_dep I))
         (keysOfL (fun q => (p_name (snd q), p_name (snd q)))
            (inst_peer I))).

  Definition Available (I : Inst) (q : Pkg.t) : Prop :=
    KeySet.In (fst q) (keysOf I) /\ RepoSet.In (base q) (inst_repo I).

  Definition realPkgs (I : Inst) : PkgSet.t :=
    SOkp.unionMap (fun k =>
        SOvp.map (fun v => (k, v)) (realVersions (inst_repo I) (snd k)))
      (keysOf I).

  Lemma mem_realPkgs : forall I q,
      PkgSet.In q (realPkgs I) <-> Available I q.
  Proof.
    intros I [k v]; unfold realPkgs, Available, base; simpl.
    rewrite SOkp.mem_unionMap; split.
    - intros [k0 [Hk0 Hm]]; apply SOvp.mem_map in Hm as [u [Hu He]].
      mem_destruct; split; [exact Hk0 | apply mem_realVersions; exact Hu].
    - intros [Hk Hb]; exists k; split; [exact Hk |].
      apply SOvp.mem_map; exists v; split;
        [apply mem_realVersions; exact Hb | reflexivity].
  Qed.

  Definition Installs (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (p : Pkg.t) (m : NKey.t) (v : V.t) : Prop :=
    PkgSet.In (m, v) S /\ Conc.ParentRel.In ((m, v), p) pi.

  Definition Shows (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (sg : Pkg.t -> N.t -> option V.t) (q : Pkg.t) (a : N.t) (w : V.t)
    : Prop :=
    if chains I q a then sg q a = Some w
    else if holds I q a then Installs S pi q (slotKey I (base q) a) w
    else if selfb q a then w = snd q
    else False.

  Definition InPeerRanges (I : Inst) (q : Pkg.t) (c : RPkg.t) (a : N.t)
      (w : V.t) : Prop :=
    forall r, In (c, r) (inst_peer I) -> p_name r = a ->
      VSet.In w (peerCandsAt I (base q) r).

  Definition ReadBelow (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (c : Pkg.t) (a : N.t) : Prop :=
    exists m u, Installs S pi c m u /\ NSet.In a (peerNames I (snd m, u)).

  Definition plainCands (I : Inst) (a : N.t) (rg : Range) : VSet.t :=
    rangeEval (override I a rg) (realVersions (inst_repo I) a).

  Fixpoint sightCandsL (I : Inst) (a : N.t) (l : list PeerDependency)
    : VSet.t :=
    match l with
    | nil => VSet.empty
    | r :: l' =>
        if NEqb.eqb (p_name r) a
        then VSet.union (plainCands I a (p_range r)) (sightCandsL I a l')
        else sightCandsL I a l'
    end.

  Definition sightCands (I : Inst) (c : RPkg.t) (a : N.t) : VSet.t :=
    VSet.union (sightCandsL I a (peerDependenciesAt I c)) (slotCands I c a).

  Definition Offers (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (sg : Pkg.t -> N.t -> option V.t) (q c : Pkg.t) (a : N.t) (w : V.t)
    : Prop :=
    Shows I S pi sg q a w \/
    (dp I c a = true /\ (forall w', ~ Shows I S pi sg q a w') /\
     Installs S pi c (slotKey I (base c) a) w).

  Record IsResolution (I : Inst)
      (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (sg : Pkg.t -> N.t -> option V.t) : Prop :=
    { res_subset : forall q, PkgSet.In q S -> Available I q
    ; res_root : PkgSet.In (rootPkg I) S
    ; res_unique :
        forall p m v v', Installs S pi p m v -> Installs S pi p m v' -> v = v'
    ; res_slot :
        forall p, PkgSet.In p S ->
        forall a, NSet.In a (dirs I (base p)) -> dp I p a = false ->
        exists v, VSet.In v (slotCands I (base p) a) /\
          Installs S pi p (slotKey I (base p) a) v
    ; res_slot_range :
        forall p, PkgSet.In p S ->
        forall a, NSet.In a (dirs I (base p)) ->
        forall v, Installs S pi p (slotKey I (base p) a) v ->
          VSet.In v (slotCands I (base p) a)
    ; res_root_loose :
        forall m v, Installs S pi (rootPkg I) m v ->
          ~ NSet.In (fst m) (dirs I (inst_root I)) ->
          NSet.In (fst m) (rootPeerDirs I)
    ; res_peer_local :
        forall q, PkgSet.In q S ->
        forall a, chains I q a = true -> dp I q a = false ->
        forall w, ~ Installs S pi q (slotKey I (base q) a) w
    ; res_desc :
        forall p p' m u u' d d' s, PkgSet.In p S -> PkgSet.In p' S ->
          Installs S pi p m u -> Installs S pi p' m u' ->
          slotOf I (base p) (fst m) = Some d ->
          slotOf I (base p') (fst m) = Some d' ->
          d_target d = snd m -> d_target d' = snd m ->
          d_desc d = Some s -> d_desc d' = Some s -> u = u'
    ; res_dp :
        forall q, PkgSet.In q S ->
        forall m u, Installs S pi q m u ->
        forall a, dp I (m, u) a = true ->
          ((exists w, Shows I S pi sg q a w) ->
           forall u', ~ Installs S pi (m, u) (slotKey I (snd m, u) a) u') /\
          ((forall w, ~ Shows I S pi sg q a w) ->
           exists u', VSet.In u' (slotCands I (snd m, u) a) /\
             Installs S pi (m, u) (slotKey I (snd m, u) a) u')
    ; res_dp_own :
        forall c, PkgSet.In c S ->
        forall a u, dp I c a = true -> ReadBelow I S pi c a ->
          Installs S pi c (slotKey I (base c) a) u ->
          sg c a = Some u /\ slotKey I (base c) a = (a, a)
    ; res_sight_range :
        forall c a w, sg c a = Some w -> VSet.In w (sightCands I (base c) a)
    ; res_peer_sight :
        forall q, PkgSet.In q S ->
        forall m u, Installs S pi q m u ->
        forall a, NSet.In a (peerNames I (snd m, u)) ->
          chains I (m, u) a = true -> ReadBelow I S pi (m, u) a ->
          (forall w, sg (m, u) a = Some w <-> Offers I S pi sg q (m, u) a w) /\
          (forall w, Shows I S pi sg q a w -> slotKey I (base q) a = (a, a))
    ; res_peer_reach :
        forall q, PkgSet.In q S ->
        forall m u, Installs S pi q m u ->
        forall a w, NSet.In a (peerNames I (snd m, u)) ->
          Shows I S pi sg q a w -> InPeerRanges I q (snd m, u) a w /\
          (dp I (m, u) a = true -> VSet.In w (slotCands I (snd m, u) a))
    ; res_peer_need :
        forall q, PkgSet.In q S ->
        forall m u, Installs S pi q m u ->
        forall r, In ((snd m, u), r) (inst_peer I) -> p_optional r = false ->
          dp I (m, u) (p_name r) = false ->
        exists w, Shows I S pi sg q (p_name r) w
    ; res_root_peer :
        forall r, In (inst_root I, r) (inst_peer I) ->
          p_optional r = false ->
        exists v, VSet.In v (peerCandsAt I (inst_root I) r) /\
          Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) v
    ; res_root_peer_match :
        forall r, In (inst_root I, r) (inst_peer I) ->
          p_optional r = true ->
          NSet.In (p_name r) (dirs I (inst_root I)) ->
        forall v, Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) v ->
          VSet.In v (peerCandsAt I (inst_root I) r)
    ; res_parents :
        forall c q, Conc.ParentRel.In (c, q) pi ->
          PkgSet.In c S /\ PkgSet.In q S /\
          KeySet.In (fst c) (childKeys I q) }.

  Module Reduction.

    Definition embedPkg (q : Pkg.t) : T.Pkg.t :=
      (Nm.Granular (fst q) (snd q), Vs.Orig (snd q)).

    Definition embedVS (vs : VSet.t) : T.VSet.t := SOvcv.map Vs.Orig vs.

    Definition embedSet (S : PkgSet.t) : T.PkgSet.t := SOptp.map embedPkg S.

    Lemma mem_embedVS : forall vs x,
        T.VSet.In x (embedVS vs) <-> exists w, VSet.In w vs /\ x = Vs.Orig w.
    Proof. intros vs x; unfold embedVS; apply SOvcv.mem_map. Qed.

    Lemma orig_embedVS : forall vs w,
        T.VSet.In (Vs.Orig w) (embedVS vs) <-> VSet.In w vs.
    Proof.
      intros vs w; rewrite mem_embedVS; split.
      - intros [w' [Hw E]]; injection E as ->; exact Hw.
      - intro Hw; exists w; split; [exact Hw | reflexivity].
    Qed.

    Definition peerCands (I : Inst) (q c : Pkg.t) (r : PeerDependency)
      : VSet.t :=
      if dp I c (p_name r)
      then VSet.inter (peerCandsAt I (base q) r) (slotCands I (base c) (p_name r))
      else peerCandsAt I (base q) r.

    Definition peerOpt (I : Inst) (c : Pkg.t) (r : PeerDependency) : bool :=
      orb (p_optional r) (dp I c (p_name r)).

    Lemma peerCands_spec : forall I q c r w,
        VSet.In w (peerCands I q c r) <->
        VSet.In w (peerCandsAt I (base q) r) /\
        (dp I c (p_name r) = true -> VSet.In w (slotCands I (base c) (p_name r))).
    Proof.
      intros I q c r w; unfold peerCands.
      destruct (dp I c (p_name r)); [rewrite VSet.inter_spec |]; split.
      - intros [H1 H2]; split; [exact H1 | intros _; exact H2].
      - intros [H1 H2]; split; [exact H1 | exact (H2 eq_refl)].
      - intro H; split; [exact H | discriminate].
      - intros [H _]; exact H.
    Qed.

    Definition linkCands (I : Inst) (q c : Pkg.t) (r : PeerDependency)
      : T.VSet.t :=
      let pc := peerCands I q c r in
      let opt := peerOpt I c r in
      if chains I q (p_name r)
      then if opt
           then T.VSet.add Vs.Bot (embedVS pc)
           else embedVS pc
      else if holds I q (p_name r)
      then if andb (loose I q (p_name r)) opt
           then T.VSet.add Vs.Bot (embedVS pc)
           else embedVS pc
      else if selfb q (p_name r)
      then if VSet.mem (snd q) pc
           then T.VSet.singleton (Vs.Orig (snd q))
           else T.VSet.empty
      else if opt then T.VSet.singleton Vs.Bot else T.VSet.empty.

    Lemma mem_linkCands : forall I q c r x,
        T.VSet.In x (linkCands I q c r) <->
        (chains I q (p_name r) = true /\
           ((x = Vs.Bot /\ peerOpt I c r = true) \/
            exists w, VSet.In w (peerCands I q c r) /\ x = Vs.Orig w)) \/
        (chains I q (p_name r) = false /\ holds I q (p_name r) = true /\
           ((x = Vs.Bot /\ peerOpt I c r = true /\ loose I q (p_name r) = true) \/
            exists w, VSet.In w (peerCands I q c r) /\ x = Vs.Orig w)) \/
        (chains I q (p_name r) = false /\ holds I q (p_name r) = false /\
           selfb q (p_name r) = true /\
           VSet.In (snd q) (peerCands I q c r) /\ x = Vs.Orig (snd q)) \/
        (chains I q (p_name r) = false /\ holds I q (p_name r) = false /\
           selfb q (p_name r) = false /\ peerOpt I c r = true /\ x = Vs.Bot).
    Proof.
      intros I q c r x; unfold linkCands; cbv zeta.
      assert (He : forall y, T.VSet.In y T.VSet.empty <-> False)
        by (intro y; split; [apply SOvcv.empty_in | intros []]).
      destruct (chains I q (p_name r)) eqn:Hc.
      - destruct (peerOpt I c r) eqn:Ho;
          rewrite ?T.VSet.add_spec, mem_embedVS; split.
        + intros [E | H]; left; split; try reflexivity;
            [left; split; [exact E | reflexivity] | right; exact H].
        + intros [[_ [[E _] | H]] | [[E _] | [[E _] | [E _]]]];
            try discriminate E; [left; exact E | right; exact H].
        + intro H; left; split; [reflexivity | right; exact H].
        + intros [[_ [[_ E] | H]] | [[E _] | [[E _] | [E _]]]];
            try discriminate E; exact H.
      - destruct (holds I q (p_name r)) eqn:Hh.
        + destruct (andb (loose I q (p_name r)) (peerOpt I c r)) eqn:Hlo.
          * apply Bool.andb_true_iff in Hlo; destruct Hlo as [Hl Ho].
            rewrite T.VSet.add_spec, mem_embedVS; split.
            -- intro H; right; left; split; [reflexivity | split; [reflexivity |]].
               destruct H as [E | H]; [left; split; [exact E | split; assumption] |
                                       right; exact H].
            -- intros [[E _] | [[_ [_ H]] | [[_ [E _]] | [_ [E _]]]]];
                 try discriminate E.
               destruct H as [[E _] | H]; [left; exact E | right; exact H].
          * rewrite mem_embedVS; split.
            -- intro H; right; left.
               split; [reflexivity | split; [reflexivity | right; exact H]].
            -- intros [[E _] | [[_ [_ H]] | [[_ [E _]] | [_ [E _]]]]];
                 try discriminate E.
               destruct H as [[_ [Ho Hl]] | H]; [| exact H].
               rewrite Hl, Ho in Hlo; discriminate Hlo.
        + destruct (selfb q (p_name r)) eqn:Hs.
          * destruct (VSet.mem (snd q) (peerCands I q c r)) eqn:Hm.
            -- apply VSet.mem_spec in Hm.
               rewrite T.VSet.singleton_spec; split.
               ++ intro E; right; right; left; repeat split; assumption.
               ++ intros [[E _] | [[_ [E _]] | [[_ [_ [_ [_ E]]]] | [_ [_ [E _]]]]]];
                    try discriminate E; exact E.
            -- rewrite He; split; [intros [] |].
               intros [[E _] | [[_ [E _]] | [[_ [_ [_ [Hin _]]]] | [_ [_ [E _]]]]]];
                 try discriminate E.
               apply VSet.mem_spec in Hin; rewrite Hin in Hm; discriminate Hm.
          * destruct (peerOpt I c r) eqn:Ho.
            -- rewrite T.VSet.singleton_spec; split.
               ++ intro E; right; right; right; repeat split; assumption.
               ++ intros [[E _] | [[_ [E _]] | [[_ [_ [E _]]] | [_ [_ [_ [_ E]]]]]]];
                    try discriminate E; exact E.
            -- rewrite He; split; [intros [] |].
               intros [[E _] | [[_ [E _]] | [[_ [_ [E _]]] | [_ [_ [_ [E _]]]]]]];
                 discriminate E.
    Qed.

    Lemma linkCands_orig : forall I q c r w,
        T.VSet.In (Vs.Orig w) (linkCands I q c r) ->
        VSet.In w (peerCands I q c r).
    Proof.
      intros I q c r w H; apply mem_linkCands in H.
      destruct H as [[_ [[E _] | [w' [Hw E]]]] |
                     [[_ [_ [[E _] | [w' [Hw E]]]]] |
                      [[_ [_ [_ [Hw E]]]] | [_ [_ [_ [_ E]]]]]]];
        try discriminate E; injection E as ->; exact Hw.
    Qed.

    Lemma linkCands_bot : forall I q c r,
        T.VSet.In Vs.Bot (linkCands I q c r) -> peerOpt I c r = true.
    Proof.
      intros I q c r H; apply mem_linkCands in H.
      destruct H as [[_ [[_ Ho] | [w' [_ E]]]] |
                     [[_ [_ [[_ [Ho _]] | [w' [_ E]]]]] |
                      [[_ [_ [_ [_ E]]]] | [_ [_ [_ [Ho _]]]]]]];
        try discriminate E; exact Ho.
    Qed.

    Lemma linkCands_free : forall I q c r,
        ~ T.VSet.In Vs.Free (linkCands I q c r).
    Proof.
      intros I q c r H; apply mem_linkCands in H.
      destruct H as [[_ [[E _] | [w' [_ E]]]] |
                     [[_ [_ [[E _] | [w' [_ E]]]]] |
                      [[_ [_ [_ [_ E]]]] | [_ [_ [_ [_ E]]]]]]];
        discriminate E.
    Qed.

    Fixpoint linkVersL (I : Inst) (q c : Pkg.t) (a : N.t)
        (l : list PeerDependency) : T.VSet.t :=
      match l with
      | nil => T.VSet.empty
      | r :: l' =>
          if NEqb.eqb (p_name r) a
          then T.VSet.union (linkCands I q c r) (linkVersL I q c a l')
          else linkVersL I q c a l'
      end.

    Definition linkVers (I : Inst) (q c : Pkg.t) (a : N.t)
      : T.VSet.t :=
      linkVersL I q c a (peerDependenciesAt I (base c)).

    Lemma mem_linkVersL : forall I q c a l x,
        T.VSet.In x (linkVersL I q c a l) <->
        exists r, In r l /\ p_name r = a /\ T.VSet.In x (linkCands I q c r).
    Proof.
      intros I q c a l x; induction l as [| r l IH]; cbn [linkVersL].
      - split; [intro H; destruct (SOvcv.empty_in _ H) | intros [r [[] _]]].
      - destruct (NEqb.eqb (p_name r) a) eqn:Hn.
        + apply NEqb.eqb_true_iff in Hn.
          rewrite T.VSet.union_spec, IH; split.
          * intros [H | [r' [Hr' H]]].
            -- exists r; split; [left; reflexivity | split; [exact Hn | exact H]].
            -- exists r'; split; [right; exact Hr' | exact H].
          * intros [r' [[E | Hr'] [Hn' H]]].
            -- subst r'; left; exact H.
            -- right; exists r'; split; [exact Hr' | split; assumption].
        + rewrite IH; split.
          * intros [r' [Hr' H]]; exists r'; split; [right; exact Hr' | exact H].
          * intros [r' [[E | Hr'] [Hn' H]]].
            -- subst r'; rewrite Hn', NEqb.eqb_refl in Hn; discriminate Hn.
            -- exists r'; split; [exact Hr' | split; assumption].
    Qed.

    Lemma mem_linkVers : forall I q c a x,
        T.VSet.In x (linkVers I q c a) <->
        exists r, In (base c, r) (inst_peer I) /\ p_name r = a /\
          T.VSet.In x (linkCands I q c r).
    Proof.
      intros I q c a x; unfold linkVers, peerDependenciesAt.
      rewrite mem_linkVersL; split; intros [r [Hr H]]; exists r;
        (split; [apply in_ownedBy; exact Hr | exact H]).
    Qed.

    Definition versions (I : Inst) (n : Nm.t) : T.VSet.t :=
      match n with
      | Nm.Granular k w =>
          if PkgSet.mem (k, w) (realPkgs I)
          then T.VSet.singleton (Vs.Orig w)
          else T.VSet.empty
      | Nm.Intermediate k v m =>
          if loose I (k, v) (fst m)
          then T.VSet.add Vs.Bot (embedVS (childCands I (k, v) m))
          else embedVS (childCands I (k, v) m)
      | Nm.Sight k v a =>
          T.VSet.add Vs.Bot
            (T.VSet.add Vs.Free (embedVS (sightCands I (snd k, v) a)))
      | Nm.Link k v m u a => linkVers I (k, v) (m, u) a
      | Nm.Desc _ t _ => embedVS (realVersions (inst_repo I) t)
      end.

    Lemma versions_int : forall I k v m x,
        T.VSet.In x (versions I (Nm.Intermediate k v m)) <->
        (x = Vs.Bot /\ loose I (k, v) (fst m) = true) \/
        exists u, VSet.In u (childCands I (k, v) m) /\ x = Vs.Orig u.
    Proof.
      intros I k v m x; cbn [versions].
      destruct (loose I (k, v) (fst m)); rewrite ?T.VSet.add_spec, mem_embedVS.
      - split; [intros [E | H]; [left; split; [exact E | reflexivity] | right; exact H] |].
        intros [[E _] | H]; [left; exact E | right; exact H].
      - split; [intro H; right; exact H |].
        intros [[_ E] | H]; [discriminate E | exact H].
    Qed.

    Lemma orig_versions_int : forall I k v m u,
        T.VSet.In (Vs.Orig u) (versions I (Nm.Intermediate k v m)) <->
        VSet.In u (childCands I (k, v) m).
    Proof.
      intros I k v m u; rewrite versions_int; split.
      - intros [[E _] | [u' [Hu E]]]; [discriminate E | injection E as ->; exact Hu].
      - intro Hu; right; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma childCands_chains : forall I q m,
        chains I q (fst m) = true -> dp I q (fst m) = false ->
        childCands I q m = VSet.empty.
    Proof.
      intros I q m H Hd; unfold dp in Hd; rewrite H in Hd; cbn [andb] in Hd.
      unfold childCands; rewrite Hd, H.
      destruct (KeyEqb.eqb m (slotKey I (base q) (fst m))); reflexivity.
    Qed.

    Lemma childCands_root_loose : forall I m v,
        VSet.In v (childCands I (rootPkg I) m) ->
        ~ NSet.In (fst m) (dirs I (inst_root I)) ->
        NSet.In (fst m) (rootPeerDirs I).
    Proof.
      intros I m v Hv Hnd; unfold childCands in Hv; rewrite base_rootPkg in Hv.
      destruct (KeyEqb.eqb m (slotKey I (inst_root I) (fst m)));
        [| destruct (SOrv.empty_in _ Hv)].
      destruct (NSet.mem (fst m) (dirs I (inst_root I))) eqn:Hd;
        [apply NSet.mem_spec in Hd; contradiction |].
      destruct (chains I (rootPkg I) (fst m)); [destruct (SOrv.empty_in _ Hv) |].
      rewrite PkgEqb.eqb_refl in Hv; cbn [andb] in Hv.
      destruct (NSet.mem (fst m) (rootPeerDirs I)) eqn:Hr;
        [apply NSet.mem_spec; exact Hr | destruct (SOrv.empty_in _ Hv)].
    Qed.

    Definition slotSet (I : Inst) (q : Pkg.t) (a : N.t) : T.VSet.t :=
      if dp I q a
      then T.VSet.add Vs.Bot (embedVS (slotCands I (base q) a))
      else embedVS (slotCands I (base q) a).

    Definition entryEdges (I : Inst) (q : Pkg.t)
      : T.DependeesSet.t :=
      depsOfL (fun a =>
          (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
           slotSet I q a))
        (NSet.elements (dirs I (base q))).

    Definition rootPeerEdges (I : Inst) (q : Pkg.t)
      : T.DependeesSet.t :=
      if PkgEqb.eqb q (rootPkg I)
      then depsOfL (fun r =>
               (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
                embedVS (peerCandsAt I (base q) r)))
             (activePeers I (base q) (base q))
      else T.DependeesSet.empty.

    Definition linkEdges (I : Inst) (q : Pkg.t) (m : NKey.t) (u : V.t)
      : T.DependeesSet.t :=
      depsOfL (fun r =>
          (Nm.Link (fst q) (snd q) m u (p_name r), linkCands I q (m, u) r))
        (peerDependenciesAt I (snd m, u)).

    Definition plainKey (I : Inst) (p : RPkg.t) (a : N.t) : bool :=
      KeyEqb.eqb (slotKey I p a) (a, a).

    Definition sightSet (I : Inst) (q c : Pkg.t) (a : N.t) (x : Vs.t)
      : T.VSet.t :=
      match x with
      | Vs.Orig w =>
          if plainKey I (base q) a
          then T.VSet.add (Vs.Orig w) (T.VSet.singleton Vs.Free)
          else T.VSet.singleton Vs.Free
      | Vs.Bot =>
          if dp I c a
          then T.VSet.add Vs.Free
                 (if plainKey I (base c) a
                  then embedVS (slotCands I (base c) a) else T.VSet.empty)
          else T.VSet.add Vs.Bot (T.VSet.singleton Vs.Free)
      | Vs.Free => T.VSet.singleton Vs.Free
      end.

    Definition dpEdges (I : Inst) (c : Pkg.t) (a : N.t) (x : Vs.t)
      : T.DependeesSet.t :=
      if dp I c a
      then match x with
           | Vs.Orig _ =>
               T.DependeesSet.singleton
                 (Nm.Intermediate (fst c) (snd c) (slotKey I (base c) a),
                  T.VSet.singleton Vs.Bot)
           | Vs.Bot =>
               T.DependeesSet.singleton
                 (Nm.Intermediate (fst c) (snd c) (slotKey I (base c) a),
                  embedVS (slotCands I (base c) a))
           | Vs.Free => T.DependeesSet.empty
           end
      else T.DependeesSet.empty.

    Definition ownSight (I : Inst) (q : Pkg.t) (m : NKey.t) (u : V.t)
      : T.DependeesSet.t :=
      if andb (dp I q (fst m)) (KeyEqb.eqb m (slotKey I (base q) (fst m)))
      then T.DependeesSet.singleton
             (Nm.Sight (fst q) (snd q) (fst m),
              if plainKey I (base q) (fst m)
              then T.VSet.add (Vs.Orig u) (T.VSet.singleton Vs.Free)
              else T.VSet.singleton Vs.Free)
      else T.DependeesSet.empty.

    Definition descEdges (I : Inst) (q : Pkg.t) (m : NKey.t) (u : V.t)
      : T.DependeesSet.t :=
      match slotOf I (base q) (fst m) with
      | Some d =>
          match d_desc d with
          | Some s =>
              if NEqb.eqb (d_target d) (snd m)
              then T.DependeesSet.singleton
                     (Nm.Desc (fst m) (snd m) s, T.VSet.singleton (Vs.Orig u))
              else T.DependeesSet.empty
          | None => T.DependeesSet.empty
          end
      | None => T.DependeesSet.empty
      end.

    Definition holderEdges (I : Inst) (q : Pkg.t) (a : N.t) (x : Vs.t)
      : T.DependeesSet.t :=
      if chains I q a
      then T.DependeesSet.singleton
             (Nm.Sight (fst q) (snd q) a, T.VSet.singleton x)
      else if holds I q a
      then match x with
           | Vs.Free => T.DependeesSet.empty
           | _ =>
               T.DependeesSet.singleton
                 (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
                  T.VSet.singleton x)
           end
      else T.DependeesSet.empty.

    Definition dependees (I : Inst) (s : T.Pkg.t)
      : T.DependeesSet.t :=
      match s with
      | (Nm.Granular k w, Vs.Orig v) =>
          if VEqb.eqb w v
          then T.DependeesSet.union (entryEdges I (k, v))
                 (rootPeerEdges I (k, v))
          else T.DependeesSet.empty
      | (Nm.Intermediate k v m, Vs.Orig u) =>
          T.DependeesSet.add (Nm.Granular m u, T.VSet.singleton (Vs.Orig u))
            (T.DependeesSet.union (linkEdges I (k, v) m u)
               (T.DependeesSet.union (ownSight I (k, v) m u)
                  (descEdges I (k, v) m u)))
      | (Nm.Link k v m u a, x) =>
          T.DependeesSet.add (Nm.Sight m u a, sightSet I (k, v) (m, u) a x)
            (T.DependeesSet.union (holderEdges I (k, v) a x)
               (dpEdges I (m, u) a x))
      | _ => T.DependeesSet.empty
      end.

    Lemma mem_entryEdges : forall I q h,
        T.DependeesSet.In h (entryEdges I q) <->
        exists a, NSet.In a (dirs I (base q)) /\
          h = (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
               slotSet I q a).
    Proof.
      intros I q h; unfold entryEdges; rewrite mem_depsOfL.
      split; intros [a [Ha He]]; exists a; split;
        try (apply SOnn.elements_in; exact Ha);
        try (apply SOnn.elements_in in Ha; exact Ha);
        [symmetry; exact He | symmetry; exact He].
    Qed.

    Lemma mem_rootPeerEdges : forall I q h,
        T.DependeesSet.In h (rootPeerEdges I q) <->
        q = rootPkg I /\
        exists r, In (base q, r) (inst_peer I) /\
          peerActive I (base q) r = true /\
          h = (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
               embedVS (peerCandsAt I (base q) r)).
    Proof.
      intros I q h; unfold rootPeerEdges.
      rewrite SOhh.in_if_empty, PkgEqb.eqb_true_iff, mem_depsOfL.
      unfold activePeers, peerDependenciesAt; split.
      - intros [Hq [r [Hr He]]]; split; [exact Hq |].
        apply List.filter_In in Hr; destruct Hr as [Hr Hact]; exists r.
        split; [apply in_ownedBy; exact Hr | split; [exact Hact |]].
        symmetry; exact He.
      - intros [Hq [r [Hr [Hact He]]]]; split; [exact Hq |].
        exists r; split; [| symmetry; exact He].
        apply List.filter_In; split;
          [apply in_ownedBy; exact Hr | exact Hact].
    Qed.

    Lemma mem_linkEdges : forall I q m u h,
        T.DependeesSet.In h (linkEdges I q m u) <->
        exists r, In ((snd m, u), r) (inst_peer I) /\
          h = (Nm.Link (fst q) (snd q) m u (p_name r), linkCands I q (m, u) r).
    Proof.
      intros I q m u h; unfold linkEdges, peerDependenciesAt.
      rewrite mem_depsOfL; split; intros [r [Hr He]]; exists r;
        (split; [apply in_ownedBy; exact Hr | symmetry; exact He]).
    Qed.

    Lemma sightSet_free : forall I q c a x,
        T.VSet.In Vs.Free (sightSet I q c a x).
    Proof.
      intros I q c a [w | |]; unfold sightSet;
        [destruct (plainKey I (base q) a) | destruct (dp I c a) |];
        rewrite ?T.VSet.add_spec, ?T.VSet.singleton_spec;
        solve [left; reflexivity | right; reflexivity | reflexivity].
    Qed.

    Lemma sightSet_orig : forall I q c a w y,
        T.VSet.In y (sightSet I q c a (Vs.Orig w)) <->
        y = Vs.Free \/ (y = Vs.Orig w /\ slotKey I (base q) a = (a, a)).
    Proof.
      intros I q c a w y; unfold sightSet, plainKey.
      destruct (KeyEqb.eqb (slotKey I (base q) a) (a, a)) eqn:Hp.
      - apply KeyEqb.eqb_true_iff in Hp.
        rewrite T.VSet.add_spec, T.VSet.singleton_spec; split.
        + intros [E | E]; [right; split; [exact E | exact Hp] | left; exact E].
        + intros [E | [E _]]; [right; exact E | left; exact E].
      - rewrite T.VSet.singleton_spec; split; [intro E; left; exact E |].
        intros [E | [_ Hk]]; [exact E |].
        rewrite Hk, KeyEqb.eqb_refl in Hp; discriminate Hp.
    Qed.

    Lemma sightSet_bot : forall I q c a y,
        T.VSet.In y (sightSet I q c a Vs.Bot) <->
        y = Vs.Free \/ (dp I c a = false /\ y = Vs.Bot) \/
        (dp I c a = true /\ exists u, y = Vs.Orig u /\
           VSet.In u (slotCands I (base c) a) /\ slotKey I (base c) a = (a, a)).
    Proof.
      intros I q c a y; unfold sightSet, plainKey.
      destruct (dp I c a) eqn:Hd.
      - destruct (KeyEqb.eqb (slotKey I (base c) a) (a, a)) eqn:Hp.
        + apply KeyEqb.eqb_true_iff in Hp.
          rewrite T.VSet.add_spec, mem_embedVS; split.
          * intros [E | [u [Hu E]]]; [left; exact E |].
            right; right; split; [reflexivity |].
            exists u; split; [exact E | split; [exact Hu | exact Hp]].
          * intros [E | [[E _] | [_ [u [E [Hu _]]]]]];
              [left; exact E | discriminate E |].
            right; exists u; split; [exact Hu | exact E].
        + rewrite T.VSet.add_spec; split.
          * intros [E | H]; [left; exact E | destruct (SOvcv.empty_in _ H)].
          * intros [E | [[E _] | [_ [u [_ [_ Hk]]]]]];
              [left; exact E | discriminate E |].
            rewrite Hk, KeyEqb.eqb_refl in Hp; discriminate Hp.
      - rewrite T.VSet.add_spec, T.VSet.singleton_spec; split.
        + intros [E | E]; [right; left; split; [reflexivity | exact E] | left; exact E].
        + intros [E | [[_ E] | [E _]]]; [right; exact E | left; exact E | discriminate E].
    Qed.

    Lemma mem_dpEdges : forall I c a x h,
        T.DependeesSet.In h (dpEdges I c a x) <->
        dp I c a = true /\
        ((exists w, x = Vs.Orig w /\
            h = (Nm.Intermediate (fst c) (snd c) (slotKey I (base c) a),
                 T.VSet.singleton Vs.Bot)) \/
         (x = Vs.Bot /\
            h = (Nm.Intermediate (fst c) (snd c) (slotKey I (base c) a),
                 embedVS (slotCands I (base c) a)))).
    Proof.
      intros I c a x h; unfold dpEdges.
      destruct (dp I c a) eqn:Hd.
      - destruct x as [w | |]; rewrite ?SOhh.singleton_in; split.
        + intro E; split; [reflexivity | left; exists w; split; [reflexivity | exact E]].
        + intros [_ [[w' [_ E]] | [E _]]]; [exact E | discriminate E].
        + intro E; split; [reflexivity | right; split; [reflexivity | exact E]].
        + intros [_ [[w' [E _]] | [_ E]]]; [discriminate E | exact E].
        + intro H; destruct (SOhh.empty_in _ H).
        + intros [_ [[w' [E _]] | [E _]]]; discriminate E.
      - split; [intro H; destruct (SOhh.empty_in _ H) | intros [E _]; discriminate E].
    Qed.

    Lemma mem_ownSight : forall I q m u h,
        T.DependeesSet.In h (ownSight I q m u) <->
        dp I q (fst m) = true /\ m = slotKey I (base q) (fst m) /\
        h = (Nm.Sight (fst q) (snd q) (fst m),
             if plainKey I (base q) (fst m)
             then T.VSet.add (Vs.Orig u) (T.VSet.singleton Vs.Free)
             else T.VSet.singleton Vs.Free).
    Proof.
      intros I q m u h; unfold ownSight.
      destruct (dp I q (fst m)) eqn:Hd;
        destruct (KeyEqb.eqb m (slotKey I (base q) (fst m))) eqn:Hk;
        cbn [andb]; rewrite ?SOhh.singleton_in; split.
      - intro E; apply KeyEqb.eqb_true_iff in Hk; repeat split; assumption.
      - intros [_ [_ E]]; exact E.
      - intro H; destruct (SOhh.empty_in _ H).
      - intros [_ [E _]]; rewrite <- E, KeyEqb.eqb_refl in Hk; discriminate Hk.
      - intro H; destruct (SOhh.empty_in _ H).
      - intros [E _]; discriminate E.
      - intro H; destruct (SOhh.empty_in _ H).
      - intros [E _]; discriminate E.
    Qed.

    Lemma mem_descEdges : forall I q m u h,
        T.DependeesSet.In h (descEdges I q m u) <->
        exists d s, slotOf I (base q) (fst m) = Some d /\ d_target d = snd m /\
          d_desc d = Some s /\
          h = (Nm.Desc (fst m) (snd m) s, T.VSet.singleton (Vs.Orig u)).
    Proof.
      intros I q m u h; unfold descEdges.
      destruct (slotOf I (base q) (fst m)) as [d |] eqn:Hs.
      - destruct (d_desc d) as [s |] eqn:Hds.
        + destruct (NEqb.eqb (d_target d) (snd m)) eqn:Ht.
          * apply NEqb.eqb_true_iff in Ht; rewrite SOhh.singleton_in; split.
            -- intro E; exists d, s; repeat split; assumption.
            -- intros [d' [s' [E [_ [Es E']]]]]; injection E as <-.
               rewrite Hds in Es; injection Es as <-; exact E'.
          * split; [intro H; destruct (SOhh.empty_in _ H) |].
            intros [d' [s' [E [Et _]]]]; injection E as <-.
            rewrite Et, NEqb.eqb_refl in Ht; discriminate Ht.
        + split; [intro H; destruct (SOhh.empty_in _ H) |].
          intros [d' [s' [E [_ [Es _]]]]]; injection E as <-.
          rewrite Hds in Es; discriminate Es.
      - split; [intro H; destruct (SOhh.empty_in _ H) |
                intros [d' [s' [E _]]]; discriminate E].
    Qed.

    Lemma mem_holderEdges : forall I q a x h,
        T.DependeesSet.In h (holderEdges I q a x) <->
        (chains I q a = true /\
           h = (Nm.Sight (fst q) (snd q) a, T.VSet.singleton x)) \/
        (chains I q a = false /\ holds I q a = true /\ x <> Vs.Free /\
           h = (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
                T.VSet.singleton x)).
    Proof.
      intros I q a x h; unfold holderEdges.
      destruct (chains I q a) eqn:Hc.
      - rewrite SOhh.singleton_in; split.
        + intro E; left; split; [reflexivity | exact E].
        + intros [[_ E] | [E _]]; [exact E | discriminate E].
      - destruct (holds I q a) eqn:Hh.
        + destruct x as [w | |]; rewrite ?SOhh.singleton_in; split.
          * intro E; right; repeat split; [discriminate | exact E].
          * intros [[E _] | [_ [_ [_ E]]]]; [discriminate E | exact E].
          * intro E; right; repeat split; [discriminate | exact E].
          * intros [[E _] | [_ [_ [_ E]]]]; [discriminate E | exact E].
          * intro H; destruct (SOhh.empty_in _ H).
          * intros [[E _] | [_ [_ [E _]]]]; [discriminate E | contradiction E; reflexivity].
        + split; [intro H; destruct (SOhh.empty_in _ H) |].
          intros [[E _] | [_ [E _]]]; discriminate E.
    Qed.

    Lemma dependees_link : forall I k v m u a x h,
        T.DependeesSet.In h (dependees I (Nm.Link k v m u a, x)) <->
        h = (Nm.Sight m u a, sightSet I (k, v) (m, u) a x) \/
        T.DependeesSet.In h (holderEdges I (k, v) a x) \/
        T.DependeesSet.In h (dpEdges I (m, u) a x).
    Proof.
      intros I k v m u a x h; cbn [dependees].
      rewrite SOhh.add_in, T.DependeesSet.union_spec; reflexivity.
    Qed.

    Lemma dependees_int : forall I k v m u h,
        T.DependeesSet.In h (dependees I (Nm.Intermediate k v m, Vs.Orig u)) <->
        h = (Nm.Granular m u, T.VSet.singleton (Vs.Orig u)) \/
        T.DependeesSet.In h (linkEdges I (k, v) m u) \/
        T.DependeesSet.In h (ownSight I (k, v) m u) \/
        T.DependeesSet.In h (descEdges I (k, v) m u).
    Proof.
      intros I k v m u h; cbn [dependees].
      rewrite SOhh.add_in, !T.DependeesSet.union_spec; reflexivity.
    Qed.

    Definition descOf (d : Dependency) : list Nm.t :=
      match d_desc d with
      | Some s => Nm.Desc (d_dir d) (d_target d) s :: nil
      | None => nil
      end.

    Definition descNames (I : Inst) : NmSet.t :=
      SOpn.ofList (List.flat_map (fun e => descOf (snd e)) (inst_dep I)).

    Lemma mem_descNames : forall I n,
        NmSet.In n (descNames I) <->
        exists p d, In (p, d) (inst_dep I) /\ In n (descOf d).
    Proof.
      intros I n; unfold descNames; rewrite SOpn.mem_ofList, in_flat_map.
      split.
      - intros [[p d] [Hin E]]; exists p, d; split; assumption.
      - intros [p [d [Hin E]]]; exists (p, d); split; assumption.
    Qed.

    Lemma in_descOf : forall d a t s,
        In (Nm.Desc a t s) (descOf d) <->
        d_desc d = Some s /\ d_dir d = a /\ d_target d = t.
    Proof.
      intros d a t s; unfold descOf.
      destruct (d_desc d) as [s' |]; cbn [In]; split.
      - intros [E | []]; injection E as -> -> ->; repeat split.
      - intros [E [-> ->]]; injection E as ->; left; reflexivity.
      - intros [].
      - intros [E _]; discriminate E.
    Qed.

    Lemma descOf_desc : forall d n, In n (descOf d) -> exists a t s, n = Nm.Desc a t s.
    Proof.
      intros d n; unfold descOf; destruct (d_desc d) as [s |]; cbn [In];
        [intros [<- | []]; exists (d_dir d), (d_target d), s; reflexivity | intros []].
    Qed.

    Definition pkgNames (I : Inst) : NmSet.t :=
      NmSet.union
        (SOpn.map (fun q => Nm.Granular (fst q) (snd q)) (realPkgs I))
        (NmSet.union
           (SOpn.unionMap (fun q =>
                SOnm.map (fun m => Nm.Intermediate (fst q) (snd q) m)
                  (childKeys I q))
              (realPkgs I))
           (NmSet.union
              (SOpn.unionMap (fun q =>
                   SOam.map (fun a => Nm.Sight (fst q) (snd q) a)
                     (peerNames I (base q)))
                 (realPkgs I))
              (SOpn.unionMap (fun q =>
                   SOnm.unionMap (fun m =>
                       SOvm.unionMap (fun u =>
                           SOam.map (fun a => Nm.Link (fst q) (snd q) m u a)
                             (peerNames I (snd m, u)))
                         (realVersions (inst_repo I) (snd m)))
                     (childKeys I q))
                 (realPkgs I)))).

    Definition targetNames (I : Inst) : NmSet.t :=
      NmSet.union (descNames I) (pkgNames I).

    Definition TargetName (I : Inst) (n : Nm.t) : Prop :=
      match n with
      | Nm.Granular k w => PkgSet.In (k, w) (realPkgs I)
      | Nm.Intermediate k v m =>
          PkgSet.In (k, v) (realPkgs I) /\ KeySet.In m (childKeys I (k, v))
      | Nm.Sight k v a =>
          PkgSet.In (k, v) (realPkgs I) /\ NSet.In a (peerNames I (snd k, v))
      | Nm.Link k v m u a =>
          PkgSet.In (k, v) (realPkgs I) /\ KeySet.In m (childKeys I (k, v)) /\
          VSet.In u (realVersions (inst_repo I) (snd m)) /\
          NSet.In a (peerNames I (snd m, u))
      | Nm.Desc a t s =>
          exists p d, In (p, d) (inst_dep I) /\ In (Nm.Desc a t s) (descOf d)
      end.

    Lemma mem_pkgNames : forall I n,
        NmSet.In n (pkgNames I) <->
        TargetName I n /\ (forall a t s, n <> Nm.Desc a t s).
    Proof.
      intros I n; unfold pkgNames.
      rewrite !NmSet.union_spec, SOpn.mem_map, !SOpn.mem_unionMap.
      setoid_rewrite SOnm.mem_map; setoid_rewrite SOam.mem_map.
      setoid_rewrite SOnm.mem_unionMap; setoid_rewrite SOvm.mem_unionMap.
      setoid_rewrite SOam.mem_map.
      destruct n as [k w | k v m | k v a | k v m u a | a t s]; cbn [TargetName]; split.
      - intros [[[k' w'] [Hq E]] | [[q [_ [m [_ E]]]] |
                 [[q [_ [a [_ E]]]] | [q [_ [m [_ [u [_ [a [_ E]]]]]]]]]]];
          try discriminate E.
        cbn [fst snd] in E; injection E as -> ->.
        split; [exact Hq | intros a t s E; discriminate E].
      - intros [H _]; left; exists (k, w); split; [exact H | reflexivity].
      - intros [[q [_ E]] | [[[k' v'] [Hq [m' [Hm E]]]] |
                 [[q [_ [a [_ E]]]] | [q [_ [m' [_ [u [_ [a [_ E]]]]]]]]]]];
          try discriminate E.
        cbn [fst snd] in E; injection E as -> -> ->.
        split; [split; assumption | intros a t s E; discriminate E].
      - intros [[Hq Hm] _]; right; left; exists (k, v); split; [exact Hq |].
        exists m; split; [exact Hm | reflexivity].
      - intros [[q [_ E]] | [[q [_ [m' [_ E]]]] |
                 [[[k' v'] [Hq [a' [Ha E]]]] |
                  [q [_ [m' [_ [u [_ [a' [_ E]]]]]]]]]]];
          try discriminate E.
        cbn [fst snd] in E; injection E as -> -> ->.
        split; [split; assumption | intros a t s E; discriminate E].
      - intros [[Hq Ha] _]; right; right; left; exists (k, v); split; [exact Hq |].
        exists a; split; [exact Ha | reflexivity].
      - intros [[q [_ E]] | [[q [_ [m' [_ E]]]] |
                 [[q [_ [a' [_ E]]]] |
                  [[k' v'] [Hq [m' [Hm [u' [Hu [a' [Ha E]]]]]]]]]]];
          try discriminate E.
        cbn [fst snd] in E; injection E as -> -> -> -> ->.
        split; [repeat split; assumption | intros a t s E; discriminate E].
      - intros [[Hq [Hm [Hu Ha]]] _]; right; right; right; exists (k, v).
        split; [exact Hq |]; exists m; split; [exact Hm |].
        exists u; split; [exact Hu |]; exists a; split; [exact Ha | reflexivity].
      - intros [[q [_ E]] | [[q [_ [m' [_ E]]]] |
                 [[q [_ [a' [_ E]]]] |
                  [q [_ [m' [_ [u' [_ [a' [_ E]]]]]]]]]]]; discriminate E.
      - intros [_ H]; destruct (H a t s eq_refl).
    Qed.

    Lemma mem_targetNames : forall I n,
        NmSet.In n (targetNames I) <-> TargetName I n.
    Proof.
      intros I n; unfold targetNames.
      rewrite NmSet.union_spec, mem_descNames, mem_pkgNames.
      destruct n as [k w | k v m | k v a | k v m u a | a t s]; cbn [TargetName];
        split;
        try (intros [[p [d [_ E]]] | [H _]];
             [destruct (descOf_desc d _ E) as [? [? [? E']]]; discriminate E'
             | exact H]);
        try (intro H; right; split; [exact H | intros a' t' s' E; discriminate E]).
      - intros [H | [_ H]]; [exact H | destruct (H a t s eq_refl)].
      - intro H; left; exact H.
    Qed.

    Definition reduceReal (I : Inst) : T.PkgSet.t :=
      SOmt.unionMap
        (fun n => SOwt.map (fun x => (n, x)) (versions I n))
        (targetNames I).

    Lemma mem_reduceReal : forall I n x,
        T.PkgSet.In (n, x) (reduceReal I) <->
        NmSet.In n (targetNames I) /\ T.VSet.In x (versions I n).
    Proof.
      intros I n x; unfold reduceReal; rewrite SOmt.mem_unionMap; split.
      - intros [n0 [Hnm Hm]]; apply SOwt.mem_map in Hm; mem_destruct.
        split; assumption.
      - intros [Hnm Hx]; exists n; split; [exact Hnm |].
        apply SOwt.mem_map; exists x; split; [exact Hx | reflexivity].
    Qed.

    Definition depEdges (s : T.Pkg.t) (hs : T.DependeesSet.t) : T.DepRel.t :=
      SOhd.map (fun h => (s, h)) hs.

    Definition reduceDeps (I : Inst) : T.DepRel.t :=
      SOqd.unionMap (fun s => depEdges s (dependees I s)) (reduceReal I).

    Lemma mem_reduceDeps : forall I s h,
        T.DepRel.In (s, h) (reduceDeps I) <->
        T.PkgSet.In s (reduceReal I) /\
        T.DependeesSet.In h (dependees I s).
    Proof.
      intros I s h; unfold reduceDeps; rewrite SOqd.mem_unionMap; split.
      - intros [s0 [Hs0 Hm]]; unfold depEdges in Hm.
        apply SOhd.mem_map in Hm; mem_destruct; split; assumption.
      - intros [Hs Hh]; exists s; split; [exact Hs |].
        unfold depEdges; apply SOhd.mem_map.
        exists h; split; [exact Hh | reflexivity].
    Qed.

    Definition embedRoot (I : Inst) : T.Pkg.t := embedPkg (rootPkg I).

    Definition tryInvPkg (s : T.Pkg.t) : option Pkg.t :=
      match s with
      | (Nm.Granular k w, Vs.Orig v) =>
          if VEqb.eqb w v then Some (k, v) else None
      | _ => None
      end.

    Definition npmResolution (S : T.PkgSet.t) : PkgSet.t :=
      SOtpp.filterMap tryInvPkg S.

    Lemma mem_npmResolution : forall S q,
        PkgSet.In q (npmResolution S) <-> T.PkgSet.In (embedPkg q) S.
    Proof.
      intros S q; unfold npmResolution; apply SOtpp.mem_filterMap_inv.
      - intros [k v]; unfold tryInvPkg, embedPkg; cbn [fst snd].
        rewrite VEqb.eqb_refl; reflexivity.
      - intros [[k w | k v m | k v a | k v m u a | a t s] [x | |]] [k' v'] H;
          cbn [tryInvPkg] in H; try discriminate H.
        destruct (VEqb.eqb w x) eqn:E; [| discriminate H].
        apply VEqb.eqb_true_iff in E; subst w.
        injection H as <- <-; reflexivity.
    Qed.

    Definition npmParents (S : T.PkgSet.t) : Conc.ParentRel.t :=
      SOtp.filterMap
        (fun s => match s with
                  | (Nm.Intermediate k v m, Vs.Orig u) =>
                      if T.PkgSet.mem (embedPkg (k, v)) S
                      then Some ((m, u), (k, v))
                      else None
                  | _ => None
                  end)
        S.

    Lemma mem_npmParents : forall S c q,
        Conc.ParentRel.In (c, q) (npmParents S) <->
        T.PkgSet.In
          (Nm.Intermediate (fst q) (snd q) (fst c), Vs.Orig (snd c)) S /\
        T.PkgSet.In (embedPkg q) S.
    Proof.
      intros S [m u] [k v]; cbn [fst snd].
      unfold npmParents; rewrite SOtp.mem_filterMap; split.
      - intros [[n x] [Hs He]]; destruct n as [k' w | k' v' m' | | | ];
          destruct x as [u' | |]; try discriminate He.
        cbn beta iota in He; apply if_some_iff in He as [Hm He].
        injection He as <- <- <- <-.
        split; [exact Hs | apply T.PkgSet.mem_spec; exact Hm].
      - intros [H1 H2].
        exists (Nm.Intermediate k v m, Vs.Orig u); split; [exact H1 |].
        apply if_some_iff; split; [apply T.PkgSet.mem_spec; exact H2 |].
        reflexivity.
    Qed.

    Definition isSightOf (c : Pkg.t) (a : N.t) (s : T.Pkg.t) : bool :=
      match s with
      | (Nm.Sight k v b, Vs.Orig _) =>
          andb (KeyEqb.eqb k (fst c)) (andb (VEqb.eqb v (snd c)) (NEqb.eqb b a))
      | _ => false
      end.

    Definition npmSight (S : T.PkgSet.t) (c : Pkg.t) (a : N.t) : option V.t :=
      match List.find (isSightOf c a) (T.PkgSet.elements S) with
      | Some (_, Vs.Orig w) => Some w
      | _ => None
      end.

    Lemma isSightOf_true : forall c a s,
        isSightOf c a s = true ->
        exists w, s = (Nm.Sight (fst c) (snd c) a, Vs.Orig w).
    Proof.
      intros c a [[k w | k v m | k v b | k v m u b | b t s] [x | |]]; cbn [isSightOf];
        try discriminate.
      rewrite !Bool.andb_true_iff, KeyEqb.eqb_true_iff, VEqb.eqb_true_iff,
        NEqb.eqb_true_iff.
      intros [-> [-> ->]]; exists x; reflexivity.
    Qed.

    Lemma npmSight_some : forall S c a w,
        npmSight S c a = Some w ->
        T.PkgSet.In (Nm.Sight (fst c) (snd c) a, Vs.Orig w) S.
    Proof.
      intros S c a w; unfold npmSight.
      destruct (List.find (isSightOf c a) (T.PkgSet.elements S)) as [s |] eqn:Hf;
        [| discriminate].
      apply List.find_some in Hf; destruct Hf as [Hin Hp].
      destruct (isSightOf_true _ _ _ Hp) as [w' ->].
      intro H; injection H as ->; apply SOtp.elements_in; exact Hin.
    Qed.

    Lemma npmSight_in : forall S c a w,
        T.VersionUnique S ->
        T.PkgSet.In (Nm.Sight (fst c) (snd c) a, Vs.Orig w) S ->
        npmSight S c a = Some w.
    Proof.
      intros S c a w Hu Hin; unfold npmSight.
      destruct (List.find (isSightOf c a) (T.PkgSet.elements S)) as [s |] eqn:Hf.
      - apply List.find_some in Hf; destruct Hf as [Hs Hp].
        destruct (isSightOf_true _ _ _ Hp) as [w' ->].
        apply SOtp.elements_in in Hs.
        pose proof (Hu _ _ _ Hs Hin) as E; injection E as ->; reflexivity.
      - exfalso.
        pose proof (List.find_none _ _ Hf _ (proj2 (SOtp.elements_in _ _) Hin))
          as E.
        cbn [isSightOf] in E.
        rewrite KeyEqb.eqb_refl, VEqb.eqb_refl, NEqb.eqb_refl in E.
        discriminate E.
    Qed.

    Lemma dependees_embedPkg : forall I q,
        dependees I (embedPkg q) =
        T.DependeesSet.union (entryEdges I q) (rootPeerEdges I q).
    Proof.
      intros I [k v]; unfold embedPkg; cbn [fst snd].
      cbn [dependees]; rewrite VEqb.eqb_refl; reflexivity.
    Qed.

    Lemma dependees_gran : forall I k v,
        dependees I (Nm.Granular k v, Vs.Orig v) =
        T.DependeesSet.union (entryEdges I (k, v))
          (rootPeerEdges I (k, v)).
    Proof.
      intros I k v; cbn [dependees]; rewrite VEqb.eqb_refl; reflexivity.
    Qed.

    Lemma dep_met : forall I S s h,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In s S -> T.DependeesSet.In h (dependees I s) ->
        exists x, T.VSet.In x (snd h) /\ T.PkgSet.In (fst h, x) S.
    Proof.
      intros I S s [n vs] [Hsub _ Hdep _] Hs Hh.
      apply (Hdep s Hs n vs); apply mem_reduceDeps.
      split; [exact (Hsub _ Hs) | exact Hh].
    Qed.

    Lemma exit_selected : forall I S k v m u,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (Nm.Intermediate k v m, Vs.Orig u) S ->
        T.PkgSet.In (embedPkg (m, u)) S.
    Proof.
      intros I S k v m u Hres Hin.
      destruct (dep_met I S _ (Nm.Granular m u, T.VSet.singleton (Vs.Orig u))
                  Hres Hin) as [x [Hx HxS]].
      { cbn [dependees]; apply SOhh.add_in; left; reflexivity. }
      apply T.VSet.singleton_spec in Hx; subst x; exact HxS.
    Qed.

    Lemma mem_slotSet : forall I q a x,
        T.VSet.In x (slotSet I q a) <->
        (x = Vs.Bot /\ dp I q a = true) \/
        exists v, VSet.In v (slotCands I (base q) a) /\ x = Vs.Orig v.
    Proof.
      intros I q a x; unfold slotSet.
      destruct (dp I q a); rewrite ?T.VSet.add_spec, mem_embedVS; split.
      - intros [E | H]; [left; split; [exact E | reflexivity] | right; exact H].
      - intros [[E _] | H]; [left; exact E | right; exact H].
      - intro H; right; exact H.
      - intros [[_ E] | H]; [discriminate E | exact H].
    Qed.

    Lemma entry_selected : forall I S q a,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (embedPkg q) S ->
        NSet.In a (dirs I (base q)) ->
        exists x, T.VSet.In x (slotSet I q a) /\
          T.PkgSet.In
            (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a), x) S.
    Proof.
      intros I S q a Hres Hq Ha.
      destruct (dep_met I S _
                  (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
                   slotSet I q a) Hres Hq)
        as [x [Hx HxS]].
      { rewrite dependees_embedPkg.
        apply T.DependeesSet.union_spec; left; apply mem_entryEdges.
        exists a; split; [exact Ha | reflexivity]. }
      exists x; split; assumption.
    Qed.

    Lemma root_peer_selected : forall I S r,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        In (inst_root I, r) (inst_peer I) ->
        peerActive I (inst_root I) r = true ->
        exists v, VSet.In v (peerCandsAt I (inst_root I) r) /\
          T.PkgSet.In
            (Nm.Intermediate (fst (rootPkg I)) (snd (rootPkg I))
               (peerKeyAt I (inst_root I) r), Vs.Orig v) S.
    Proof.
      intros I S r Hres Hr Hact.
      destruct (dep_met I S _
                  (Nm.Intermediate (fst (rootPkg I)) (snd (rootPkg I))
                     (peerKeyAt I (inst_root I) r),
                   embedVS (peerCandsAt I (inst_root I) r))
                  Hres (T.res_root_mem _ _ _ _ Hres))
        as [x [Hx HxS]].
      { unfold embedRoot; rewrite dependees_embedPkg.
        apply T.DependeesSet.union_spec; right; apply mem_rootPeerEdges.
        split; [reflexivity |]; rewrite base_rootPkg.
        exists r; split; [exact Hr | split; [exact Hact | reflexivity]]. }
      apply mem_embedVS in Hx; destruct Hx as [v [Hv ->]].
      exists v; split; assumption.
    Qed.

    Lemma link_selected : forall I S q m u r,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S ->
        In ((snd m, u), r) (inst_peer I) ->
        exists x, T.VSet.In x (linkCands I q (m, u) r) /\
          T.PkgSet.In (Nm.Link (fst q) (snd q) m u (p_name r), x) S.
    Proof.
      intros I S [k v] m u r Hres Hin Hr.
      destruct (dep_met I S _
                  (Nm.Link k v m u (p_name r), linkCands I (k, v) (m, u) r) Hres Hin)
        as [x [Hx HxS]].
      { apply dependees_int; right; left.
        apply mem_linkEdges; exists r; split; [exact Hr | reflexivity]. }
      exists x; split; assumption.
    Qed.

    Lemma link_in_cands : forall I S q m u a x,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S ->
        T.PkgSet.In (Nm.Link (fst q) (snd q) m u a, x) S ->
        forall r, In ((snd m, u), r) (inst_peer I) -> p_name r = a ->
        T.VSet.In x (linkCands I q (m, u) r).
    Proof.
      intros I S q m u a x Hres Hin Hl r Hr Hn; subst a.
      destruct (link_selected I S q m u r Hres Hin Hr) as [y [Hy HyS]].
      rewrite (T.res_version_unique _ _ _ _ Hres _ _ _ Hl HyS); exact Hy.
    Qed.

    Lemma link_shows_iff : forall I S q m u a x,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (embedPkg q) S ->
        T.PkgSet.In (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S ->
        NSet.In a (peerNames I (snd m, u)) ->
        T.PkgSet.In (Nm.Link (fst q) (snd q) m u a, x) S ->
        forall w,
          Shows I (npmResolution S) (npmParents S) (npmSight S) q a w <->
          x = Vs.Orig w.
    Proof.
      intros I S [k v] m u a x Hres Hq Hi Ha Hl w.
      pose proof (T.res_version_unique _ _ _ _ Hres) as Huniq.
      apply mem_peerNames in Ha; destruct Ha as [r [Hr Hn]].
      pose proof (link_in_cands I S (k, v) m u a x Hres Hi Hl r Hr Hn) as Hx.
      subst a; apply mem_linkCands in Hx; unfold Shows.
      destruct Hx as [[Hc _] | [[Hc [Hh Hx']] |
                     [[Hc [Hh [Hs [_ E]]]] | [Hc [Hh [Hs [_ E]]]]]]];
        rewrite Hc; [| rewrite Hh | rewrite Hh, Hs | rewrite Hh, Hs].
      - destruct (dep_met I S _
                    (Nm.Sight k v (p_name r), T.VSet.singleton x) Hres Hl)
          as [y [Hy HyS]].
        { apply dependees_link; right; left; apply mem_holderEdges; left.
          split; [exact Hc | reflexivity]. }
        apply T.VSet.singleton_spec in Hy; subst y; split.
        + intro Hsg; apply npmSight_some in Hsg; cbn [fst snd] in Hsg.
          exact (Huniq _ _ _ HyS Hsg).
        + intros ->; apply npmSight_in; [exact Huniq | exact HyS].
      - assert (Hxf : x <> Vs.Free)
          by (destruct Hx' as [[E _] | [w0 [_ E]]]; subst x; discriminate).
        destruct (dep_met I S _
                    (Nm.Intermediate k v (slotKey I (base (k, v)) (p_name r)),
                     T.VSet.singleton x) Hres Hl)
          as [y [Hy HyS]].
        { apply dependees_link; right; left; apply mem_holderEdges; right.
          split; [exact Hc | split; [exact Hh | split; [exact Hxf | reflexivity]]]. }
        apply T.VSet.singleton_spec in Hy; subst y; split.
        + intros [_ Hp]; apply mem_npmParents in Hp; cbn [fst snd] in Hp.
          destruct Hp as [Hp _].
          exact (Huniq _ _ _ HyS Hp).
        + intros ->; split.
          * apply mem_npmResolution; exact (exit_selected I S k v _ w Hres HyS).
          * apply mem_npmParents; cbn [fst snd]; split; assumption.
      - subst x; cbn [snd]; split; [intros ->; reflexivity |].
        intro E; injection E as <-; reflexivity.
      - subst x; split; [intros [] | discriminate].
    Qed.

    Lemma dp_root : forall I a, dp I (rootPkg I) a = false.
    Proof. intros I a; unfold dp, chains; rewrite PkgEqb.eqb_refl; reflexivity. Qed.

    Lemma dp_chains : forall I q a, dp I q a = true -> chains I q a = true.
    Proof.
      intros I q a H; unfold dp in H; apply Bool.andb_true_iff in H; exact (proj1 H).
    Qed.

    Lemma dp_dirs : forall I q a, dp I q a = true -> NSet.In a (dirs I (base q)).
    Proof.
      intros I q a H; unfold dp in H; apply Bool.andb_true_iff in H.
      apply NSet.mem_spec; exact (proj2 H).
    Qed.

    Lemma chains_peerNames : forall I q a,
        chains I q a = true -> NSet.In a (peerNames I (base q)).
    Proof.
      intros I q a H; unfold chains in H; apply Bool.andb_true_iff in H.
      apply NSet.mem_spec; exact (proj2 H).
    Qed.

    Lemma sight_below : forall I S c m' u' a,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (Nm.Intermediate (fst c) (snd c) m', Vs.Orig u') S ->
        NSet.In a (peerNames I (snd m', u')) ->
        chains I c a = true ->
        exists y, y <> Vs.Free /\ T.PkgSet.In (Nm.Sight (fst c) (snd c) a, y) S.
    Proof.
      intros I S [k v] m' u' a Hres Hc Ha Hch.
      apply mem_peerNames in Ha; destruct Ha as [r [Hr <-]].
      destruct (link_selected I S (k, v) m' u' r Hres Hc Hr) as [y [Hy Hl]].
      destruct (dep_met I S _ (Nm.Sight k v (p_name r), T.VSet.singleton y)
                  Hres Hl) as [z [Hz HzS]].
      { apply dependees_link; right; left; apply mem_holderEdges; left.
        split; [exact Hch | reflexivity]. }
      apply T.VSet.singleton_spec in Hz; subst z.
      exists y; split; [| exact HzS].
      intro E; subst y; exact (linkCands_free _ _ _ _ Hy).
    Qed.

    Theorem npm_soundness : forall I S,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        IsResolution I (npmResolution S) (npmParents S) (npmSight S).
    Proof.
      intros I S Hres.
      assert (Hres' := Hres); destruct Hres' as [Hsub Hroot Hdep Huniq].
      assert (Hpi : forall q m v,
                 T.PkgSet.In (embedPkg q) S ->
                 T.PkgSet.In
                   (Nm.Intermediate (fst q) (snd q) m, Vs.Orig v) S ->
                 Installs (npmResolution S) (npmParents S) q m v).
      { intros [k w] m v Hq Hi; split.
        - apply mem_npmResolution; exact (exit_selected I S k w m v Hres Hi).
        - apply mem_npmParents; cbn [fst snd]; split; assumption. }
      assert (Hint : forall q m u,
                 Installs (npmResolution S) (npmParents S) q m u ->
                 T.PkgSet.In
                   (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S).
      { intros q m u [_ Hu]; apply mem_npmParents in Hu; exact (proj1 Hu). }
      assert (Hlink : forall q m u a,
                 T.PkgSet.In
                   (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S ->
                 NSet.In a (peerNames I (snd m, u)) ->
                 exists x,
                   T.PkgSet.In (Nm.Link (fst q) (snd q) m u a, x) S).
      { intros q m u a Hi Ha; apply mem_peerNames in Ha.
        destruct Ha as [r [Hr <-]].
        destruct (link_selected I S q m u r Hres Hi Hr) as [x [_ Hl]].
        exists x; exact Hl. }
      assert (Hxf : forall q m u a x,
                 T.PkgSet.In
                   (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S ->
                 NSet.In a (peerNames I (snd m, u)) ->
                 T.PkgSet.In (Nm.Link (fst q) (snd q) m u a, x) S ->
                 x <> Vs.Free).
      { intros q m u a x Hi Ha Hl E; subst x.
        apply mem_peerNames in Ha; destruct Ha as [r [Hr Hn]].
        exact (linkCands_free I q (m, u) r
                 (link_in_cands I S q m u a Vs.Free Hres Hi Hl r Hr Hn)). }
      constructor.
      - intros [k w] Hq; apply mem_npmResolution in Hq.
        pose proof (Hsub _ Hq) as Hr; apply mem_reduceReal in Hr.
        destruct Hr as [_ Hv].
        cbn [versions embedPkg fst snd] in Hv.
        apply SOvcv.in_if_empty in Hv as [Hm _].
        apply PkgSet.mem_spec in Hm; apply mem_realPkgs; exact Hm.
      - apply mem_npmResolution; exact Hroot.
      - intros p m v v' H1 H2; apply Hint in H1; apply Hint in H2.
        pose proof (Huniq _ _ _ H1 H2) as He; injection He as ->; reflexivity.
      - intros p Hp a Ha Hdp; apply mem_npmResolution in Hp.
        destruct (entry_selected I S p a Hres Hp Ha) as [x [Hx Hi]].
        apply mem_slotSet in Hx.
        destruct Hx as [[_ E] | [v [Hv ->]]]; [rewrite Hdp in E; discriminate E |].
        exists v; split; [exact Hv | exact (Hpi p _ v Hp Hi)].
      - intros p Hp a Ha v Hi; apply mem_npmResolution in Hp.
        destruct (entry_selected I S p a Hres Hp Ha) as [x [Hx HiS]].
        apply Hint in Hi; rewrite (Huniq _ _ _ HiS Hi) in Hx.
        apply mem_slotSet in Hx.
        destruct Hx as [[E _] | [v' [Hv' E]]]; [discriminate E |].
        injection E as ->; exact Hv'.
      - intros m v Hi Hnd; apply Hint in Hi.
        apply Hsub, mem_reduceReal in Hi; destruct Hi as [_ Hw].
        unfold rootPkg in Hw; cbn [fst snd] in Hw.
        apply orig_versions_int in Hw.
        exact (childCands_root_loose I m v Hw Hnd).
      - intros [k v] Hq a Hch Hdp w Hi; apply Hint in Hi.
        apply Hsub, mem_reduceReal in Hi; destruct Hi as [_ Hw].
        apply orig_versions_int in Hw.
        apply (SOrv.empty_in w).
        rewrite <- (childCands_chains I (k, v)
                      (slotKey I (base (k, v)) a));
          [exact Hw | rewrite slotKey_fst; exact Hch | rewrite slotKey_fst; exact Hdp].
      - intros [k v] [k' v'] m u u' d d' s _ _ Hi Hi' Hd Hd' Ht Ht' Hs Hs'.
        apply Hint in Hi; apply Hint in Hi'; cbn [fst snd] in Hi, Hi'.
        destruct (dep_met I S _
                    (Nm.Desc (fst m) (snd m) s, T.VSet.singleton (Vs.Orig u))
                    Hres Hi) as [z [Hz HzS]].
        { apply dependees_int; right; right; right; apply mem_descEdges.
          exists d, s; repeat split; assumption. }
        destruct (dep_met I S _
                    (Nm.Desc (fst m) (snd m) s, T.VSet.singleton (Vs.Orig u'))
                    Hres Hi') as [z' [Hz' HzS']].
        { apply dependees_int; right; right; right; apply mem_descEdges.
          exists d', s; repeat split; assumption. }
        apply T.VSet.singleton_spec in Hz; apply T.VSet.singleton_spec in Hz'.
        subst z z'.
        pose proof (Huniq _ _ _ HzS HzS') as E; injection E as ->; reflexivity.
      - intros q Hq m u HI a Hdp.
        apply mem_npmResolution in Hq; pose proof (Hint _ _ _ HI) as Hi.
        assert (Ha : NSet.In a (peerNames I (snd m, u)))
          by exact (chains_peerNames I (m, u) a (dp_chains I (m, u) a Hdp)).
        destruct (Hlink q m u a Hi Ha) as [x Hl].
        pose proof (link_shows_iff I S q m u a x Hres Hq Hi Ha Hl) as Hsh.
        pose proof (Hxf q m u a x Hi Ha Hl) as Hf.
        pose proof (exit_selected I S (fst q) (snd q) m u Hres Hi) as Hm.
        destruct x as [w | |]; [| | contradiction Hf; reflexivity].
        + destruct (dep_met I S _
                      (Nm.Intermediate m u (slotKey I (base (m, u)) a),
                       T.VSet.singleton Vs.Bot) Hres Hl) as [z [Hz HzS]].
          { apply dependees_link; right; right; apply mem_dpEdges.
            split; [exact Hdp | left; exists w; split; reflexivity]. }
          apply T.VSet.singleton_spec in Hz; subst z; split.
          * intros _ u' Hi'; apply Hint in Hi'.
            pose proof (Huniq _ _ _ HzS Hi') as E; discriminate E.
          * intro Hno; exfalso; apply (Hno w); apply Hsh; reflexivity.
        + destruct (dep_met I S _
                      (Nm.Intermediate m u (slotKey I (base (m, u)) a),
                       embedVS (slotCands I (base (m, u)) a)) Hres Hl)
            as [z [Hz HzS]].
          { apply dependees_link; right; right; apply mem_dpEdges.
            split; [exact Hdp | right; split; reflexivity]. }
          apply mem_embedVS in Hz; destruct Hz as [u' [Hu' ->]]; split.
          * intros [w Hw]; apply Hsh in Hw; discriminate Hw.
          * intros _; exists u'; split; [exact Hu' | exact (Hpi (m, u) _ u' Hm HzS)].
      - intros [k v] Hc a u Hdp [m' [u' [Hc' Ha']]] Hi.
        apply Hint in Hi; apply Hint in Hc'; cbn [fst snd] in Hi, Hc'.
        destruct (sight_below I S (k, v) m' u' a Hres Hc' Ha'
                    (dp_chains I (k, v) a Hdp)) as [y [Hyf Hy]].
        cbn [fst snd] in Hy.
        destruct (dep_met I S _
                    (Nm.Sight k v a,
                     if plainKey I (base (k, v)) a
                     then T.VSet.add (Vs.Orig u) (T.VSet.singleton Vs.Free)
                     else T.VSet.singleton Vs.Free) Hres Hi) as [z [Hz HzS]].
        { apply dependees_int; right; right; left; apply mem_ownSight.
          rewrite slotKey_fst; split; [exact Hdp | split; reflexivity]. }
        rewrite (Huniq _ _ _ HzS Hy) in Hz.
        cbn [snd] in Hz; unfold plainKey in Hz.
        destruct (KeyEqb.eqb (slotKey I (base (k, v)) a) (a, a)) eqn:Hp.
        + apply KeyEqb.eqb_true_iff in Hp; cbv iota in Hz.
          rewrite T.VSet.add_spec, T.VSet.singleton_spec in Hz.
          destruct Hz as [E | E]; [subst y | contradiction].
          split; [apply npmSight_in; [exact Huniq | exact Hy] | exact Hp].
        + cbv iota in Hz; rewrite T.VSet.singleton_spec in Hz; contradiction.
      - intros [k v] a w Hsg; apply npmSight_some in Hsg.
        apply Hsub, mem_reduceReal in Hsg; destruct Hsg as [_ Hw].
        cbn [versions fst snd] in Hw; rewrite !T.VSet.add_spec in Hw.
        destruct Hw as [E | [E | Hw]]; [discriminate E | discriminate E |].
        apply orig_embedVS in Hw; exact Hw.
      - intros [k v] Hq m u Hmu a Ha Hch [m' [u' [Hc' Ha']]].
        apply mem_npmResolution in Hq; apply Hint in Hmu; apply Hint in Hc'.
        cbn [fst snd] in Hmu, Hc'.
        destruct (Hlink (k, v) m u a Hmu Ha) as [x Hl]; cbn [fst snd] in Hl.
        destruct (sight_below I S (m, u) m' u' a Hres Hc' Ha' Hch) as [y [Hyf Hy]].
        cbn [fst snd] in Hy.
        destruct (dep_met I S _ (Nm.Sight m u a, sightSet I (k, v) (m, u) a x)
                    Hres Hl) as [z [Hz HzS]].
        { apply dependees_link; left; reflexivity. }
        rewrite (Huniq _ _ _ HzS Hy) in Hz.
        pose proof (link_shows_iff I S (k, v) m u a x Hres Hq Hmu Ha Hl) as Hsh.
        pose proof (Hxf (k, v) m u a x Hmu Ha Hl) as Hf.
        pose proof (exit_selected I S k v m u Hres Hmu) as Hm.
        destruct x as [w | |]; [| | contradiction Hf; reflexivity].
        + apply (sightSet_orig I (k, v) (m, u)) in Hz.
          destruct Hz as [E | [E Hplain]]; [contradiction | subst y].
          split.
          * intro w'; unfold Offers; split.
            -- intro Hsg; apply npmSight_some in Hsg; cbn [fst snd] in Hsg.
               pose proof (Huniq _ _ _ Hy Hsg) as E; injection E as <-.
               left; apply Hsh; reflexivity.
            -- intros [Hs | [_ [Hno _]]].
               ++ apply Hsh in Hs; injection Hs as <-.
                  apply npmSight_in; [exact Huniq | exact Hy].
               ++ exfalso; apply (Hno w); apply Hsh; reflexivity.
          * intros w' _; exact Hplain.
        + apply (sightSet_bot I (k, v) (m, u)) in Hz.
          destruct Hz as [E | [[Hd E] | [Hd [u2 [E [_ Hplain]]]]]];
            [contradiction | |].
          * subst y; split.
            -- intro w'; unfold Offers; split.
               ++ intro Hsg; apply npmSight_some in Hsg; cbn [fst snd] in Hsg.
                  pose proof (Huniq _ _ _ Hy Hsg) as E; discriminate E.
               ++ intros [Hs | [Hd' _]];
                    [apply Hsh in Hs; discriminate Hs | rewrite Hd in Hd'; discriminate Hd'].
            -- intros w' Hs; apply Hsh in Hs; discriminate Hs.
          * subst y.
            destruct (dep_met I S _
                        (Nm.Intermediate m u (slotKey I (base (m, u)) a),
                         embedVS (slotCands I (base (m, u)) a)) Hres Hl)
              as [z1 [Hz1 HzS']].
            { apply dependees_link; right; right; apply mem_dpEdges.
              split; [exact Hd | right; split; reflexivity]. }
            apply mem_embedVS in Hz1; destruct Hz1 as [u'' [_ ->]].
            destruct (dep_met I S _
                        (Nm.Sight m u a,
                         if plainKey I (base (m, u)) a
                         then T.VSet.add (Vs.Orig u'') (T.VSet.singleton Vs.Free)
                         else T.VSet.singleton Vs.Free) Hres HzS') as [z2 [Hz3 Hz2]].
            { apply dependees_int; right; right; left; apply mem_ownSight.
              rewrite slotKey_fst; split; [exact Hd | split; reflexivity]. }
            rewrite (Huniq _ _ _ Hz2 Hy) in Hz3.
            cbn [snd] in Hz3; unfold plainKey in Hz3; rewrite Hplain, KeyEqb.eqb_refl in Hz3.
            cbv iota in Hz3; rewrite T.VSet.add_spec, T.VSet.singleton_spec in Hz3.
            destruct Hz3 as [E | E]; [injection E as E; subst u'' | discriminate E].
            split.
            -- intro w'; unfold Offers; split.
               ++ intro Hsg; apply npmSight_some in Hsg; cbn [fst snd] in Hsg.
                  pose proof (Huniq _ _ _ Hy Hsg) as E; injection E as <-.
                  right; split; [exact Hd |].
                  split; [intros w0 Hs; apply Hsh in Hs; discriminate Hs |].
                  exact (Hpi (m, u) _ u2 Hm HzS').
               ++ intros [Hs | [_ [_ Hi2]]]; [apply Hsh in Hs; discriminate Hs |].
                  apply Hint in Hi2.
                  pose proof (Huniq _ _ _ HzS' Hi2) as E; injection E as <-.
                  apply npmSight_in; [exact Huniq | exact Hy].
            -- intros w' Hs; apply Hsh in Hs; discriminate Hs.
      - intros q Hq m u Hmu a w Ha Hs.
        apply mem_npmResolution in Hq; apply Hint in Hmu.
        destruct (Hlink q m u a Hmu Ha) as [x Hl].
        pose proof (proj1 (link_shows_iff I S q m u a x Hres Hq Hmu Ha Hl w) Hs)
          as E; subst x.
        assert (Hall : forall r, In ((snd m, u), r) (inst_peer I) -> p_name r = a ->
                  VSet.In w (peerCands I q (m, u) r))
          by (intros r Hr Hn;
              exact (linkCands_orig I q (m, u) r w
                       (link_in_cands I S q m u a (Vs.Orig w) Hres Hmu Hl r Hr Hn))).
        split.
        + intros r Hr Hn; exact (proj1 (proj1 (peerCands_spec I q (m, u) r w)
                                          (Hall r Hr Hn))).
        + intro Hd; apply mem_peerNames in Ha; destruct Ha as [r [Hr Hn]].
          subst a.
          exact (proj2 (proj1 (peerCands_spec I q (m, u) r w) (Hall r Hr eq_refl)) Hd).
      - intros q Hq m u Hmu r Hr Hopt Hdp.
        apply mem_npmResolution in Hq; apply Hint in Hmu.
        destruct (link_selected I S q m u r Hres Hmu Hr) as [x [Hx Hl]].
        assert (Ha : NSet.In (p_name r) (peerNames I (snd m, u)))
          by (apply mem_peerNames; exists r; split; [exact Hr | reflexivity]).
        destruct x as [w | |].
        + exists w.
          apply (link_shows_iff I S q m u _ _ Hres Hq Hmu Ha Hl w).
          reflexivity.
        + apply linkCands_bot in Hx; unfold peerOpt in Hx.
          rewrite Hopt, Hdp in Hx; discriminate Hx.
        + exfalso; exact (linkCands_free I q (m, u) r Hx).
      - intros r Hr Hopt.
        destruct (root_peer_selected I S r Hres Hr
                    (proj2 (Bool.orb_true_iff _ _)
                       (or_introl (proj2 (Bool.negb_true_iff _) Hopt))))
          as [v [Hv Hj]].
        exists v; split; [exact Hv | exact (Hpi (rootPkg I) _ v Hroot Hj)].
      - intros r Hr Hopt Hname v Hv.
        assert (Hact : peerActive I (inst_root I) r = true)
          by (unfold peerActive; apply Bool.orb_true_iff; right;
              apply NSet.mem_spec; exact Hname).
        destruct (root_peer_selected I S r Hres Hr Hact) as [v0 [Hv0 Hj]].
        apply Hint in Hv.
        pose proof (Huniq _ _ _ Hv Hj) as Heq; injection Heq as ->; exact Hv0.
      - intros [m u] [k w] Hcq; apply mem_npmParents in Hcq.
        cbn [fst snd] in Hcq; destruct Hcq as [Hi Hq].
        split; [| split].
        + apply mem_npmResolution; exact (exit_selected I S k w m u Hres Hi).
        + apply mem_npmResolution; exact Hq.
        + apply Hsub, mem_reduceReal in Hi; destruct Hi as [Hn _].
          apply mem_targetNames in Hn; exact (proj2 Hn).
    Qed.

    Corollary peer_installed : forall I S,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        forall k v m u,
          T.PkgSet.In (embedPkg (k, v)) S ->
          T.PkgSet.In (Nm.Intermediate k v m, Vs.Orig u) S ->
        forall r, In ((snd m, u), r) (inst_peer I) ->
          p_optional r = false -> chains I (k, v) (p_name r) = false ->
          selfb (k, v) (p_name r) = false -> dp I (m, u) (p_name r) = false ->
        exists w,
          PkgSet.In (peerKeyAt I (snd k, v) r, w) (npmResolution S) /\
          Conc.ParentRel.In
            ((peerKeyAt I (snd k, v) r, w), (k, v)) (npmParents S) /\
          VSet.In w (peerCandsAt I (snd k, v) r).
    Proof.
      intros I S Hres k v m u Hq Hi r Hr Hopt Hch Hself Hdp.
      pose proof (npm_soundness I S Hres) as Hsrc.
      assert (Hp : PkgSet.In (k, v) (npmResolution S))
        by (apply mem_npmResolution; exact Hq).
      assert (HI : Installs (npmResolution S) (npmParents S) (k, v) m u).
      { split.
        - apply mem_npmResolution; exact (exit_selected I S k v m u Hres Hi).
        - apply mem_npmParents; cbn [fst snd]; split; assumption. }
      assert (Ha : NSet.In (p_name r) (peerNames I (snd m, u)))
        by (apply mem_peerNames; exists r; split; [exact Hr | reflexivity]).
      destruct (res_peer_need _ _ _ _ Hsrc (k, v) Hp m u HI r Hr Hopt Hdp)
        as [w Hw].
      pose proof (res_peer_reach _ _ _ _ Hsrc (k, v) Hp m u HI _ w Ha Hw)
        as Hrg.
      unfold Shows in Hw; rewrite Hch in Hw.
      destruct (holds I (k, v) (p_name r)); [| rewrite Hself in Hw; destruct Hw].
      exists w; split; [exact (proj1 Hw) | split; [exact (proj2 Hw) |]].
      exact (proj1 Hrg r Hr eq_refl).
    Qed.

    Lemma slotKey_childKeys : forall I q a,
        NSet.In a (childDirs I q) ->
        KeySet.In (slotKey I (base q) a) (childKeys I q).
    Proof.
      intros I q a Ha; unfold childKeys; apply SOnk.mem_map.
      exists a; split; [exact Ha | reflexivity].
    Qed.

    Lemma dirs_childDirs : forall I q a,
        NSet.In a (dirs I (base q)) -> NSet.In a (childDirs I q).
    Proof.
      intros I q a Ha; unfold childDirs.
      destruct (PkgEqb.eqb q (rootPkg I)); [apply NSet.union_spec; left |];
        exact Ha.
    Qed.

    Lemma holds_childDirs : forall I q a,
        holds I q a = true -> NSet.In a (peerDirs I) ->
        NSet.In a (childDirs I q).
    Proof.
      intros I q a Hh Hp; unfold holds in Hh; unfold childDirs.
      apply Bool.orb_true_iff in Hh.
      destruct (PkgEqb.eqb q (rootPkg I)) eqn:Hq.
      - apply NSet.union_spec; right; exact Hp.
      - destruct Hh as [E | Hd]; [discriminate E | apply NSet.mem_spec; exact Hd].
    Qed.

    Lemma rootPeer_childKeys : forall I r,
        In (inst_root I, r) (inst_peer I) ->
        peerActive I (inst_root I) r = true ->
        KeySet.In (peerKeyAt I (inst_root I) r) (childKeys I (rootPkg I)).
    Proof.
      intros I r Hr _; unfold peerKeyAt; rewrite <- (base_rootPkg I).
      apply slotKey_childKeys.
      unfold childDirs; rewrite PkgEqb.eqb_refl; apply NSet.union_spec; right.
      exact (peerDirs_peer I _ r Hr).
    Qed.

    Lemma peerDirs_keysOf : forall I a,
        NSet.In a (peerDirs I) ->
        exists q r, In (q, r) (inst_peer I) /\ p_name r = a.
    Proof.
      intros I a Ha; unfold peerDirs in Ha; apply mem_namesOfL in Ha.
      destruct Ha as [[q r] [Hr Hn]]; exists q, r; split; assumption.
    Qed.

    Lemma slotKey_keysOf : forall I p a,
        NSet.In a (dirs I p) \/
        (exists q r, In (q, r) (inst_peer I) /\ p_name r = a) ->
        KeySet.In (slotKey I p a) (keysOf I).
    Proof.
      intros I p a Ha; unfold keysOf, slotKey.
      apply KeySet.add_spec; right; apply KeySet.union_spec.
      destruct (slotOf I p a) as [d |] eqn:Hd.
      - left; apply mem_keysOfL.
        destruct (findDepL_some _ _ _ Hd) as [Hin Hdir].
        unfold dependenciesOf in Hin; apply List.filter_In in Hin.
        exists (p, d); split; [apply in_ownedBy; exact (proj1 Hin) |].
        cbn [snd]; rewrite Hdir; reflexivity.
      - right; apply mem_keysOfL.
        destruct Ha as [Ha | [q [r [Hr Hn]]]].
        + exfalso; unfold dirs in Ha; apply mem_namesOfL in Ha.
          destruct Ha as [d [Hin Hdir]].
          exact (findDepL_none _ _ Hd d Hin Hdir).
        + exists (q, r); split; [exact Hr |].
          cbn [snd]; rewrite Hn; reflexivity.
    Qed.

    Lemma slotOf_dep : forall I p a d,
        slotOf I p a = Some d -> In (p, d) (inst_dep I) /\ d_dir d = a.
    Proof.
      intros I p a d Hd.
      destruct (findDepL_some _ _ _ Hd) as [Hin Hdir].
      unfold dependenciesOf in Hin; apply List.filter_In in Hin.
      split; [apply in_ownedBy; exact (proj1 Hin) | exact Hdir].
    Qed.

    Lemma childDirs_keysOf : forall I q a,
        NSet.In a (childDirs I q) ->
        NSet.In a (dirs I (base q)) \/
        (exists q' r, In (q', r) (inst_peer I) /\ p_name r = a).
    Proof.
      intros I q a Ha; unfold childDirs in Ha.
      destruct (PkgEqb.eqb q (rootPkg I)); [| left; exact Ha].
      apply NSet.union_spec in Ha; destruct Ha as [Ha | Ha]; [left; exact Ha |].
      right; exact (peerDirs_keysOf I a Ha).
    Qed.

    Lemma childKeys_keysOf : forall I q m,
        KeySet.In m (childKeys I q) -> KeySet.In m (keysOf I).
    Proof.
      intros I q m H; unfold childKeys in H; apply SOnk.mem_map in H.
      destruct H as [a [Ha ->]]; apply slotKey_keysOf.
      exact (childDirs_keysOf I q a Ha).
    Qed.

    Lemma childCands_real : forall I q m u,
        VSet.In u (childCands I q m) -> PkgSet.In (m, u) (realPkgs I).
    Proof.
      intros I q m u Hu; unfold childCands in Hu.
      apply SOrv.in_if_empty in Hu as [Hk Hu]; apply KeyEqb.eqb_true_iff in Hk.
      apply mem_realPkgs; unfold Available, base; cbn [fst snd].
      destruct (NSet.mem (fst m) (dirs I (base q))) eqn:Hd.
      - apply NSet.mem_spec in Hd.
        split; [rewrite Hk; apply slotKey_keysOf; left; exact Hd |].
        pose proof (slotCands_real I _ _ u Hu) as Hr.
        rewrite <- Hk in Hr; exact Hr.
      - destruct (chains I q (fst m)); [destruct (SOrv.empty_in _ Hu) |].
        apply SOrv.in_if_empty in Hu as [Hh Hu].
        apply Bool.andb_true_iff in Hh; destruct Hh as [_ Hp].
        apply NSet.mem_spec in Hp.
        split; [rewrite Hk; apply slotKey_keysOf; right;
                exact (peerDirs_keysOf I _ (rootPeerDirs_peerDirs I _ Hp)) |].
        apply mem_realVersions; exact Hu.
    Qed.

    Lemma installs_childCands : forall I S pi sg p m v,
        IsResolution I S pi sg -> PkgSet.In p S ->
        KeySet.In m (childKeys I p) ->
        Installs S pi p m v ->
        VSet.In v (childCands I p m).
    Proof.
      intros I S pi sg p m v Hres Hp Hm Hi.
      unfold childKeys in Hm; apply SOnk.mem_map in Hm.
      destruct Hm as [a [Ha ->]].
      unfold childCands; rewrite slotKey_fst, KeyEqb.eqb_refl.
      destruct (NSet.mem a (dirs I (base p))) eqn:Hsa.
      - apply NSet.mem_spec in Hsa.
        exact (res_slot_range _ _ _ _ Hres p Hp a Hsa v Hi).
      - destruct (chains I p a) eqn:Hch.
        { exfalso; refine (res_peer_local _ _ _ _ Hres p Hp a Hch _ v Hi).
          unfold dp; rewrite Hch, Hsa; reflexivity. }
        unfold childDirs in Ha.
        destruct (PkgEqb.eqb p (rootPkg I)) eqn:Hq.
        + apply NSet.union_spec in Ha; destruct Ha as [Ha | Ha].
          * apply NSet.mem_spec in Ha; rewrite Ha in Hsa; discriminate Hsa.
          * apply PkgEqb.eqb_true_iff in Hq; subst p.
            assert (Hr : NSet.In a (rootPeerDirs I)).
            { pose proof (res_root_loose _ _ _ _ Hres _ v Hi) as Hl.
              rewrite slotKey_fst in Hl; apply Hl.
              rewrite <- base_rootPkg; intro Hd; apply NSet.mem_spec in Hd.
              rewrite Hd in Hsa; discriminate Hsa. }
            apply NSet.mem_spec in Hr; rewrite Hr; cbn [andb].
            destruct Hi as [HinS _].
            destruct (res_subset _ _ _ _ Hres _ HinS) as [_ Hb]; unfold base in Hb.
            cbn [fst snd] in Hb; apply mem_realVersions; exact Hb.
        + apply NSet.mem_spec in Ha; rewrite Ha in Hsa; discriminate Hsa.
    Qed.

    Lemma root_peer_installs : forall I S pi sg r,
        IsResolution I S pi sg ->
        In (inst_root I, r) (inst_peer I) ->
        peerActive I (inst_root I) r = true ->
        exists w, VSet.In w (peerCandsAt I (inst_root I) r) /\
          Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) w.
    Proof.
      intros I S pi sg r Hres Hr Hact.
      destruct (p_optional r) eqn:Hopt;
        [| exact (res_root_peer _ _ _ _ Hres r Hr Hopt)].
      unfold peerActive in Hact; rewrite Hopt in Hact;
        cbn [negb orb] in Hact; apply NSet.mem_spec in Hact.
      assert (Hdir : NSet.In (p_name r) (dirs I (base (rootPkg I))))
        by (rewrite base_rootPkg; exact Hact).
      destruct (res_slot _ _ _ _ Hres (rootPkg I) (res_root _ _ _ _ Hres)
                  (p_name r) Hdir (dp_root I (p_name r))) as [w [_ Hi]].
      rewrite base_rootPkg in Hi.
      exists w; unfold peerKeyAt; split;
        [exact (res_root_peer_match _ _ _ _ Hres r Hr Hopt Hact w Hi)
        | exact Hi].
    Qed.

    Lemma holds_installed : forall I S pi sg q a,
        IsResolution I S pi sg -> PkgSet.In q S ->
        holds I q a = true -> loose I q a = false ->
        exists w, Installs S pi q (slotKey I (base q) a) w.
    Proof.
      intros I S pi sg q a Hres Hq Hh Hl.
      unfold loose in Hl; apply Bool.orb_false_iff in Hl; destruct Hl as [Hl Hdp].
      assert (Hd : NSet.In a (dirs I (base q))).
      { unfold holds in Hh.
        destruct (NSet.mem a (dirs I (base q))) eqn:Hm;
          [apply NSet.mem_spec; exact Hm |].
        rewrite Bool.orb_false_r in Hh; rewrite Hh in Hl; discriminate Hl. }
      destruct (res_slot _ _ _ _ Hres q Hq a Hd Hdp) as [w [_ Hi]].
      exists w; exact Hi.
    Qed.

    Definition installsb (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (p : Pkg.t) (m : NKey.t) (u : V.t) : bool :=
      andb (PkgSet.mem (m, u) S) (Conc.ParentRel.mem ((m, u), p) pi).

    Lemma installsb_iff : forall S pi p m u,
        installsb S pi p m u = true <-> Installs S pi p m u.
    Proof.
      intros S pi p m u; unfold installsb, Installs.
      rewrite Bool.andb_true_iff, PkgSet.mem_spec, Conc.ParentRel.mem_spec.
      reflexivity.
    Qed.

    Definition instNode (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (p : Pkg.t) (m : NKey.t) (u : V.t) : option T.Pkg.t :=
      if installsb S pi p m u
      then Some (Nm.Intermediate (fst p) (snd p) m, Vs.Orig u)
      else None.

    Definition ownAt (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (p : Pkg.t) (k : NKey.t) : option V.t :=
      List.find (installsb S pi p k)
        (VSet.elements (realVersions (inst_repo I) (snd k))).

    Lemma ownAt_some : forall I S pi p k w,
        ownAt I S pi p k = Some w -> Installs S pi p k w.
    Proof.
      intros I S pi p k w H; unfold ownAt in H.
      apply List.find_some in H; apply installsb_iff; exact (proj2 H).
    Qed.

    Lemma ownAt_installs : forall I S pi sg p k w,
        IsResolution I S pi sg ->
        Installs S pi p k w -> ownAt I S pi p k = Some w.
    Proof.
      intros I S pi sg p k w Hres Hi; unfold ownAt.
      destruct (List.find (installsb S pi p k)
                  (VSet.elements (realVersions (inst_repo I) (snd k))))
        as [w' |] eqn:Hf.
      - apply List.find_some in Hf; destruct Hf as [_ Hb].
        apply installsb_iff in Hb.
        rewrite (res_unique _ _ _ _ Hres _ _ _ _ Hb Hi); reflexivity.
      - exfalso.
        assert (Hw : List.In w (VSet.elements (realVersions (inst_repo I)
                                  (snd k)))).
        { apply SOvp.elements_in, mem_realVersions.
          destruct (res_subset _ _ _ _ Hres _ (proj1 Hi)) as [_ Hb].
          exact Hb. }
        pose proof (List.find_none _ _ Hf _ Hw) as E.
        apply installsb_iff in Hi; rewrite Hi in E; discriminate E.
    Qed.

    Definition showsAt (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (sg : Pkg.t -> N.t -> option V.t) (q : Pkg.t) (a : N.t)
      : option V.t :=
      if chains I q a then sg q a
      else if holds I q a then ownAt I S pi q (slotKey I (base q) a)
      else if selfb q a then Some (snd q)
      else None.

    Lemma showsAt_holds : forall I S pi sg q a,
        chains I q a = false -> holds I q a = true ->
        showsAt I S pi sg q a = ownAt I S pi q (slotKey I (base q) a).
    Proof.
      intros I S pi sg q a Hc Hh; unfold showsAt; rewrite Hc, Hh; reflexivity.
    Qed.

    Lemma showsAt_spec : forall I S pi sg q a w,
        IsResolution I S pi sg ->
        showsAt I S pi sg q a = Some w <-> Shows I S pi sg q a w.
    Proof.
      intros I S pi sg q a w Hres; unfold showsAt, Shows.
      destruct (chains I q a); [reflexivity |].
      destruct (holds I q a).
      - split; [apply ownAt_some | apply (ownAt_installs I S pi sg); exact Hres].
      - destruct (selfb q a); split.
        + intro E; injection E as <-; reflexivity.
        + intros ->; reflexivity.
        + discriminate.
        + intros [].
    Qed.

    Definition readb (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (c : Pkg.t) (a : N.t) : bool :=
      KeySet.exists_ (fun m =>
          VSet.exists_ (fun u =>
              andb (installsb S pi c m u) (NSet.mem a (peerNames I (snd m, u))))
            (realVersions (inst_repo I) (snd m)))
        (childKeys I c).

    Lemma readb_iff : forall I S pi sg c a,
        IsResolution I S pi sg ->
        readb I S pi c a = true <-> ReadBelow I S pi c a.
    Proof.
      intros I S pi sg c a Hres; unfold readb, ReadBelow.
      rewrite SOkp.SSA.exists_spec'; split.
      - intros [m [_ H]]; apply SOvp.SSA.exists_spec' in H.
        destruct H as [u [_ H]]; apply Bool.andb_true_iff in H.
        destruct H as [Hi Ha]; apply installsb_iff in Hi.
        apply NSet.mem_spec in Ha; exists m, u; split; assumption.
      - intros [m [u [Hi Ha]]]; exists m; split.
        + exact (proj2 (proj2 (res_parents _ _ _ _ Hres _ _ (proj2 Hi)))).
        + apply SOvp.SSA.exists_spec'; exists u; split.
          * apply mem_realVersions.
            exact (proj2 (res_subset _ _ _ _ Hres _ (proj1 Hi))).
          * apply Bool.andb_true_iff; split;
              [apply installsb_iff; exact Hi | apply NSet.mem_spec; exact Ha].
    Qed.

    Definition sightVal (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (sg : Pkg.t -> N.t -> option V.t) (c : Pkg.t) (a : N.t) : Vs.t :=
      if andb (chains I c a) (readb I S pi c a)
      then match sg c a with Some w => Vs.Orig w | None => Vs.Bot end
      else Vs.Free.

    Definition linkVal (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (sg : Pkg.t -> N.t -> option V.t) (q : Pkg.t) (a : N.t) : Vs.t :=
      match showsAt I S pi sg q a with
      | Some w => Vs.Orig w
      | None => Vs.Bot
      end.

    Lemma linkVal_cands : forall I S pi sg q m u r,
        IsResolution I S pi sg -> PkgSet.In q S -> Installs S pi q m u ->
        In ((snd m, u), r) (inst_peer I) ->
        T.VSet.In (linkVal I S pi sg q (p_name r)) (linkCands I q (m, u) r).
    Proof.
      intros I S pi sg q m u r Hres Hq Hi Hr.
      assert (Ha : NSet.In (p_name r) (peerNames I (snd m, u)))
        by (apply mem_peerNames; exists r; split; [exact Hr | reflexivity]).
      assert (Hrange : forall w, showsAt I S pi sg q (p_name r) = Some w ->
                 VSet.In w (peerCands I q (m, u) r)).
      { intros w Hs; apply (showsAt_spec I S pi sg q _ w Hres) in Hs.
        destruct (res_peer_reach _ _ _ _ Hres q Hq m u Hi _ w Ha Hs) as [Hpr Hd].
        apply peerCands_spec; split; [exact (Hpr r Hr eq_refl) | exact Hd]. }
      assert (Hneed : showsAt I S pi sg q (p_name r) = None ->
                 peerOpt I (m, u) r = true).
      { intro Hs; unfold peerOpt.
        destruct (p_optional r) eqn:Ho; [reflexivity |].
        destruct (dp I (m, u) (p_name r)) eqn:Hd; [reflexivity |].
        destruct (res_peer_need _ _ _ _ Hres q Hq m u Hi r Hr Ho Hd) as [w Hw].
        apply (showsAt_spec I S pi sg q _ w Hres) in Hw.
        rewrite Hs in Hw; discriminate Hw. }
      apply mem_linkCands; unfold linkVal.
      destruct (chains I q (p_name r)) eqn:Hc.
      - left; split; [reflexivity |].
        destruct (showsAt I S pi sg q (p_name r)) as [w |] eqn:Hs.
        + right; exists w; split; [exact (Hrange w eq_refl) | reflexivity].
        + left; split; [reflexivity | exact (Hneed eq_refl)].
      - destruct (holds I q (p_name r)) eqn:Hh.
        + right; left; split; [reflexivity | split; [reflexivity |]].
          pose proof (showsAt_holds I S pi sg q _ Hc Hh) as Hs0.
          destruct (showsAt I S pi sg q (p_name r)) as [w |] eqn:Hs.
          * right; exists w; split; [exact (Hrange w eq_refl) | reflexivity].
          * destruct (loose I q (p_name r)) eqn:Hl.
            -- left; split; [reflexivity | split; [exact (Hneed eq_refl) | reflexivity]].
            -- exfalso.
               destruct (holds_installed I S pi sg q _ Hres Hq Hh Hl) as [w Hw].
               rewrite (ownAt_installs I S pi sg _ _ _ Hres Hw) in Hs0.
               discriminate Hs0.
        + assert (Hs0 : showsAt I S pi sg q (p_name r) =
                        if selfb q (p_name r) then Some (snd q) else None)
            by (unfold showsAt; rewrite Hc, Hh; reflexivity).
          destruct (selfb q (p_name r)) eqn:Hsf.
          * right; right; left; rewrite Hs0.
            repeat split; try reflexivity.
            exact (Hrange _ Hs0).
          * right; right; right; rewrite Hs0.
            repeat split; try reflexivity; exact (Hneed Hs0).
    Qed.

    Definition looseNode (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (p : Pkg.t) (m : NKey.t) : option T.Pkg.t :=
      if andb (loose I p (fst m))
           (match ownAt I S pi p m with Some _ => false | None => true end)
      then Some (Nm.Intermediate (fst p) (snd p) m, Vs.Bot)
      else None.

    Definition descNode (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (p : Pkg.t) (m : NKey.t) (u : V.t) : option T.Pkg.t :=
      if installsb S pi p m u
      then match slotOf I (base p) (fst m) with
           | Some d =>
               match d_desc d with
               | Some s =>
                   if NEqb.eqb (d_target d) (snd m)
                   then Some (Nm.Desc (fst m) (snd m) s, Vs.Orig u)
                   else None
               | None => None
               end
           | None => None
           end
      else None.

    Lemma descNode_some : forall I S pi p m u x,
        descNode I S pi p m u = Some x <->
        Installs S pi p m u /\ exists d s, slotOf I (base p) (fst m) = Some d /\
          d_target d = snd m /\ d_desc d = Some s /\
          x = (Nm.Desc (fst m) (snd m) s, Vs.Orig u).
    Proof.
      intros I S pi p m u x; unfold descNode.
      destruct (installsb S pi p m u) eqn:Hb.
      - apply installsb_iff in Hb.
        destruct (slotOf I (base p) (fst m)) as [d |] eqn:Hd.
        + destruct (d_desc d) as [s |] eqn:Hds.
          * destruct (NEqb.eqb (d_target d) (snd m)) eqn:Ht.
            -- apply NEqb.eqb_true_iff in Ht; split.
               ++ intro E; injection E as <-; split; [exact Hb |].
                  exists d, s; repeat split; assumption.
               ++ intros [_ [d' [s' [E [_ [Es ->]]]]]]; injection E as <-.
                  rewrite Hds in Es; injection Es as <-; reflexivity.
            -- split; [discriminate |].
               intros [_ [d' [s' [E [Et _]]]]]; injection E as <-.
               rewrite Et, NEqb.eqb_refl in Ht; discriminate Ht.
          * split; [discriminate |].
            intros [_ [d' [s' [E [_ [Es _]]]]]]; injection E as <-.
            rewrite Hds in Es; discriminate Es.
        + split; [discriminate | intros [_ [d' [s' [E _]]]]; discriminate E].
      - split; [discriminate |].
        intros [Hi _]; apply installsb_iff in Hi; rewrite Hi in Hb; discriminate Hb.
    Qed.

    Definition coreResolution (I : Inst) (S : PkgSet.t)
        (pi : Conc.ParentRel.t) (sg : Pkg.t -> N.t -> option V.t)
      : T.PkgSet.t :=
      T.PkgSet.union (embedSet S)
        (T.PkgSet.union
           (SOpt.unionMap (fun p =>
                SOkt.unionMap (fun m =>
                    SOvt.filterMap (instNode S pi p m)
                      (realVersions (inst_repo I) (snd m)))
                  (childKeys I p))
              S)
           (T.PkgSet.union
              (SOpt.unionMap (fun c =>
                   SOat.map (fun a =>
                       (Nm.Sight (fst c) (snd c) a, sightVal I S pi sg c a))
                     (peerNames I (base c)))
                 S)
              (T.PkgSet.union
              (SOpt.unionMap (fun p =>
                   SOkt.unionMap (fun m =>
                       SOvt.unionMap (fun u =>
                           if installsb S pi p m u
                           then SOat.map (fun a =>
                                    (Nm.Link (fst p) (snd p) m u a,
                                     linkVal I S pi sg p a))
                                  (peerNames I (snd m, u))
                           else T.PkgSet.empty)
                         (realVersions (inst_repo I) (snd m)))
                     (childKeys I p))
                 S)
              (T.PkgSet.union
                 (SOpt.unionMap (fun p =>
                      SOkt.filterMap (looseNode I S pi p) (childKeys I p))
                    S)
                 (SOpt.unionMap (fun p =>
                      SOkt.unionMap (fun m =>
                          SOvt.filterMap (descNode I S pi p m)
                            (realVersions (inst_repo I) (snd m)))
                        (childKeys I p))
                    S))))).

    Lemma embedSet_gran : forall S s,
        T.PkgSet.In s (embedSet S) <->
        exists (k : NKey.t) (v : V.t), PkgSet.In (k, v) S /\
          s = (Nm.Granular k v, Vs.Orig v).
    Proof.
      intros S s; unfold embedSet; rewrite SOptp.mem_map; split.
      - intros [[k v] [Hp ->]]; exists k, v; split; [exact Hp | reflexivity].
      - intros [k [v [Hp ->]]]; exists (k, v); split; [exact Hp | reflexivity].
    Qed.

    Lemma mem_coreResolution : forall I S pi sg s,
        T.PkgSet.In s (coreResolution I S pi sg) <->
        (exists (k : NKey.t) (v : V.t), PkgSet.In (k, v) S /\
           s = (Nm.Granular k v, Vs.Orig v)) \/
        (exists p m u, PkgSet.In p S /\ KeySet.In m (childKeys I p) /\
           VSet.In u (realVersions (inst_repo I) (snd m)) /\
           Installs S pi p m u /\
           s = (Nm.Intermediate (fst p) (snd p) m, Vs.Orig u)) \/
        (exists c a, PkgSet.In c S /\ NSet.In a (peerNames I (base c)) /\
           s = (Nm.Sight (fst c) (snd c) a, sightVal I S pi sg c a)) \/
        (exists p m u a, PkgSet.In p S /\
           KeySet.In m (childKeys I p) /\
           VSet.In u (realVersions (inst_repo I) (snd m)) /\
           Installs S pi p m u /\ NSet.In a (peerNames I (snd m, u)) /\
           s = (Nm.Link (fst p) (snd p) m u a, linkVal I S pi sg p a)) \/
        (exists p m, PkgSet.In p S /\ KeySet.In m (childKeys I p) /\
           loose I p (fst m) = true /\ ownAt I S pi p m = None /\
           s = (Nm.Intermediate (fst p) (snd p) m, Vs.Bot)) \/
        (exists p m u d, PkgSet.In p S /\ KeySet.In m (childKeys I p) /\
           VSet.In u (realVersions (inst_repo I) (snd m)) /\
           Installs S pi p m u /\ slotOf I (base p) (fst m) = Some d /\
           d_target d = snd m /\ exists e, d_desc d = Some e /\
           s = (Nm.Desc (fst m) (snd m) e, Vs.Orig u)).
    Proof.
      intros I S pi sg s; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, embedSet_gran; split.
      - intros [H | [H | [H | [H | [H | H]]]]].
        + left; exact H.
        + apply SOpt.mem_unionMap in H; destruct H as [p [Hp H]].
          apply SOkt.mem_unionMap in H; destruct H as [m [Hm H]].
          apply SOvt.mem_filterMap in H; destruct H as [u [Hu H]].
          unfold instNode in H; apply if_some_iff in H; destruct H as [Hb <-].
          apply installsb_iff in Hb.
          right; left; exists p, m, u.
          exact (conj Hp (conj Hm (conj Hu (conj Hb eq_refl)))).
        + apply SOpt.mem_unionMap in H; destruct H as [c [Hc H]].
          apply SOat.mem_map in H; destruct H as [a [Ha ->]].
          right; right; left; exists c, a; exact (conj Hc (conj Ha eq_refl)).
        + apply SOpt.mem_unionMap in H; destruct H as [p [Hp H]].
          apply SOkt.mem_unionMap in H; destruct H as [m [Hm H]].
          apply SOvt.mem_unionMap in H; destruct H as [u [Hu H]].
          apply SOat.in_if_empty in H; destruct H as [Hb H].
          apply SOat.mem_map in H; destruct H as [a [Ha ->]].
          apply installsb_iff in Hb.
          right; right; right; left; exists p, m, u, a.
          exact (conj Hp (conj Hm (conj Hu (conj Hb (conj Ha eq_refl))))).
        + apply SOpt.mem_unionMap in H; destruct H as [p [Hp H]].
          apply SOkt.mem_filterMap in H; destruct H as [m [Hm H]].
          unfold looseNode in H; apply if_some_iff in H; destruct H as [Hb <-].
          apply Bool.andb_true_iff in Hb; destruct Hb as [Hl Ho].
          right; right; right; right; left; exists p, m.
          split; [exact Hp | split; [exact Hm | split; [exact Hl | split; [| reflexivity]]]].
          destruct (ownAt I S pi p m); [discriminate Ho | reflexivity].
        + apply SOpt.mem_unionMap in H; destruct H as [p [Hp H]].
          apply SOkt.mem_unionMap in H; destruct H as [m [Hm H]].
          apply SOvt.mem_filterMap in H; destruct H as [u [Hu H]].
          apply descNode_some in H; destruct H as [Hi [d [e [Hd [Ht [He ->]]]]]].
          right; right; right; right; right; exists p, m, u, d.
          do 6 (split; [assumption |]); exists e; split; [exact He | reflexivity].
      - intros [H | [[p [m [u [Hp [Hm [Hu [Hb ->]]]]]]] |
                 [[c [a [Hc [Ha ->]]]] |
                  [[p [m [u [a [Hp [Hm [Hu [Hb [Ha ->]]]]]]]]] |
                   [[p [m [Hp [Hm [Hl [Ho ->]]]]]] |
                    [p [m [u [d [Hp [Hm [Hu [Hi [Hd [Ht [e [He ->]]]]]]]]]]]]]]]]].
        + left; exact H.
        + right; left; apply SOpt.mem_unionMap; exists p; split; [exact Hp |].
          apply SOkt.mem_unionMap; exists m; split; [exact Hm |].
          apply SOvt.mem_filterMap; exists u; split; [exact Hu |].
          unfold instNode; apply installsb_iff in Hb; rewrite Hb; reflexivity.
        + right; right; left; apply SOpt.mem_unionMap; exists c;
            split; [exact Hc |].
          apply SOat.mem_map; exists a; split; [exact Ha | reflexivity].
        + right; right; right; left; apply SOpt.mem_unionMap; exists p;
            split; [exact Hp |].
          apply SOkt.mem_unionMap; exists m; split; [exact Hm |].
          apply SOvt.mem_unionMap; exists u; split; [exact Hu |].
          apply SOat.in_if_empty; split; [apply installsb_iff; exact Hb |].
          apply SOat.mem_map; exists a; split; [exact Ha | reflexivity].
        + right; right; right; right; left; apply SOpt.mem_unionMap; exists p;
            split; [exact Hp |].
          apply SOkt.mem_filterMap; exists m; split; [exact Hm |].
          unfold looseNode; rewrite Hl, Ho; reflexivity.
        + right; right; right; right; right; apply SOpt.mem_unionMap; exists p;
            split; [exact Hp |].
          apply SOkt.mem_unionMap; exists m; split; [exact Hm |].
          apply SOvt.mem_filterMap; exists u; split; [exact Hu |].
          apply descNode_some; split; [exact Hi |].
          exists d, e; repeat split; assumption.
    Qed.

    Lemma versions_gran_real : forall I (k : NKey.t) (w : V.t),
        PkgSet.In (k, w) (realPkgs I) ->
        T.VSet.In (Vs.Orig w) (versions I (Nm.Granular k w)).
    Proof.
      intros I k w H; cbn [versions]; apply PkgSet.mem_spec in H.
      rewrite H; apply T.VSet.singleton_spec; reflexivity.
    Qed.

    Lemma sightVal_versions : forall I S pi sg c a,
        IsResolution I S pi sg ->
        T.VSet.In (sightVal I S pi sg c a)
          (versions I (Nm.Sight (fst c) (snd c) a)).
    Proof.
      intros I S pi sg c a Hres; cbn [versions]; unfold sightVal.
      rewrite !T.VSet.add_spec.
      destruct (andb (chains I c a) (readb I S pi c a)); [| right; left; reflexivity].
      destruct (sg c a) as [w |] eqn:Hsg; [| left; reflexivity].
      right; right; apply orig_embedVS.
      exact (res_sight_range _ _ _ _ Hres c a w Hsg).
    Qed.

    Lemma sightVal_link : forall I S pi sg q m u a,
        IsResolution I S pi sg -> PkgSet.In q S -> Installs S pi q m u ->
        NSet.In a (peerNames I (snd m, u)) ->
        T.VSet.In (sightVal I S pi sg (m, u) a)
          (sightSet I q (m, u) a (linkVal I S pi sg q a)).
    Proof.
      intros I S pi sg q m u a Hres Hq Hi Ha.
      unfold sightVal.
      destruct (chains I (m, u) a) eqn:Hch; [| apply sightSet_free].
      destruct (readb I S pi (m, u) a) eqn:Hrd; [| apply sightSet_free].
      cbn [andb].
      apply (readb_iff I S pi sg (m, u) a Hres) in Hrd.
      destruct (res_peer_sight _ _ _ _ Hres q Hq m u Hi a Ha Hch Hrd)
        as [Hsg Hplain].
      pose proof (proj1 Hi) as Hc.
      unfold linkVal.
      destruct (showsAt I S pi sg q a) as [w |] eqn:E.
      - apply (showsAt_spec I S pi sg q a w Hres) in E.
        assert (Hs : sg (m, u) a = Some w) by (apply Hsg; left; exact E).
        rewrite Hs; apply sightSet_orig; right.
        split; [reflexivity | exact (Hplain w E)].
      - assert (Hno : forall w, ~ Shows I S pi sg q a w).
        { intros w Hw; apply (showsAt_spec I S pi sg q a w Hres) in Hw.
          rewrite E in Hw; discriminate Hw. }
        apply sightSet_bot.
        destruct (sg (m, u) a) as [w |] eqn:Hs.
        + pose proof (proj1 (Hsg w) eq_refl) as Ho.
          destruct Ho as [Hw | [Hd [_ Hw]]]; [destruct (Hno w Hw) |].
          right; right; split; [exact Hd |]; exists w; split; [reflexivity |].
          split.
          * exact (res_slot_range _ _ _ _ Hres (m, u) Hc a
                     (dp_dirs I (m, u) a Hd) w Hw).
          * exact (proj2 (res_dp_own _ _ _ _ Hres (m, u) Hc a w Hd Hrd Hw)).
        + right; left; split; [| reflexivity].
          destruct (dp I (m, u) a) eqn:Hd; [exfalso | reflexivity].
          destruct (proj2 (res_dp _ _ _ _ Hres q Hq m u Hi a Hd) Hno)
            as [u' [_ Hu']].
          assert (Ho : Offers I S pi sg q (m, u) a u')
            by (right; split; [exact Hd | split; [exact Hno | exact Hu']]).
          apply Hsg in Ho; discriminate Ho.
    Qed.

    Lemma sightVal_holder : forall I S pi sg q m u a,
        IsResolution I S pi sg -> Installs S pi q m u ->
        NSet.In a (peerNames I (snd m, u)) ->
        chains I q a = true ->
        sightVal I S pi sg q a = linkVal I S pi sg q a.
    Proof.
      intros I S pi sg q m u a Hres Hi Ha Hch.
      assert (Hrd : readb I S pi q a = true)
        by (apply (readb_iff I S pi sg q a Hres); exists m, u; split; assumption).
      unfold sightVal, linkVal, showsAt; rewrite Hch, Hrd; cbn [andb].
      destruct (sg q a); reflexivity.
    Qed.

    Theorem npm_completeness : forall I S pi sg,
        IsResolution I S pi sg ->
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I)
          (coreResolution I S pi sg).
    Proof.
      intros I S pi sg Hres.
      pose proof (res_subset _ _ _ _ Hres) as Hsub.
      pose proof (res_slot _ _ _ _ Hres) as Hslot.
      assert (Hreal : forall q, PkgSet.In q S -> PkgSet.In q (realPkgs I))
        by (intros q Hq; apply mem_realPkgs; exact (Hsub _ Hq)).
      assert (Hrv : forall p m u, Installs S pi p m u ->
                 VSet.In u (realVersions (inst_repo I) (snd m))).
      { intros p m u [HS _]; apply mem_realVersions; exact (proj2 (Hsub _ HS)). }
      assert (Hck : forall p m u, Installs S pi p m u ->
                 KeySet.In m (childKeys I p)).
      { intros p m u [_ Hpi].
        exact (proj2 (proj2 (res_parents _ _ _ _ Hres _ _ Hpi))). }
      assert (HcoreG : forall q, PkgSet.In q S ->
                 T.PkgSet.In (embedPkg q) (coreResolution I S pi sg)).
      { intros [k v] Hq; apply mem_coreResolution; left.
        exists k, v; split; [exact Hq | reflexivity]. }
      assert (HcoreI : forall p m u, PkgSet.In p S -> Installs S pi p m u ->
                 T.PkgSet.In (Nm.Intermediate (fst p) (snd p) m, Vs.Orig u)
                   (coreResolution I S pi sg)).
      { intros p m u Hp Hi; apply mem_coreResolution; right; left.
        exists p, m, u.
        exact (conj Hp (conj (Hck _ _ _ Hi) (conj (Hrv _ _ _ Hi)
                                              (conj Hi eq_refl)))). }
      assert (HcoreS : forall c a, PkgSet.In c S ->
                 NSet.In a (peerNames I (base c)) ->
                 T.PkgSet.In (Nm.Sight (fst c) (snd c) a, sightVal I S pi sg c a)
                   (coreResolution I S pi sg)).
      { intros c a Hc Ha; apply mem_coreResolution; right; right; left.
        exists c, a; exact (conj Hc (conj Ha eq_refl)). }
      assert (HcoreL : forall p m u a, PkgSet.In p S -> Installs S pi p m u ->
                 NSet.In a (peerNames I (snd m, u)) ->
                 T.PkgSet.In (Nm.Link (fst p) (snd p) m u a,
                              linkVal I S pi sg p a)
                   (coreResolution I S pi sg)).
      { intros p m u a Hp Hi Ha; apply mem_coreResolution; right; right; right.
        left; exists p, m, u, a.
        exact (conj Hp (conj (Hck _ _ _ Hi) (conj (Hrv _ _ _ Hi)
                                              (conj Hi (conj Ha eq_refl))))). }
      constructor.
      - intros s Hs; apply mem_coreResolution in Hs.
        destruct Hs as
          [[k [v [Hp ->]]] |
           [[[pk pv] [m [u [Hp [Hm [Hu [Hi ->]]]]]]] |
            [[[ck cv] [a [Hc [Ha ->]]]] |
             [[[pk pv] [m [u [a [Hp [Hm [Hu [Hi [Ha ->]]]]]]]]] |
              [[[pk pv] [m [Hp [Hm [Hl [Ho ->]]]]]] |
               [[pk pv] [m [u [d [Hp [Hm [Hu [Hi [Hsl [Ht [e [He ->]]]]]]]]]]]]]]]]];
          cbn [fst snd] in *; apply mem_reduceReal; split.
        + apply mem_targetNames; exact (Hreal _ Hp).
        + exact (versions_gran_real I k v (Hreal _ Hp)).
        + apply mem_targetNames; split; [exact (Hreal _ Hp) | exact Hm].
        + apply orig_versions_int.
          exact (installs_childCands I S pi sg (pk, pv) m u Hres Hp Hm Hi).
        + apply mem_targetNames; split; [exact (Hreal _ Hc) | exact Ha].
        + exact (sightVal_versions I S pi sg (ck, cv) a Hres).
        + apply mem_targetNames.
          split; [exact (Hreal _ Hp) | split; [exact Hm | split; [exact Hu | exact Ha]]].
        + cbn [versions]; apply mem_linkVers.
          apply mem_peerNames in Ha; destruct Ha as [r [Hr <-]].
          exists r; split; [exact Hr | split; [reflexivity |]].
          exact (linkVal_cands I S pi sg (pk, pv) m u r Hres Hp Hi Hr).
        + apply mem_targetNames; split; [exact (Hreal _ Hp) | exact Hm].
        + apply versions_int; left; split; [reflexivity | exact Hl].
        + apply mem_targetNames; cbn [TargetName].
          destruct (slotOf_dep I _ _ _ Hsl) as [Hin Hdir].
          exists (base (pk, pv)), d; split; [exact Hin |].
          apply in_descOf; repeat split; assumption.
        + cbn [versions]; apply orig_embedVS; exact Hu.
      - apply mem_coreResolution; left.
        exists (rootKey I), (snd (inst_root I)); split;
          [exact (res_root _ _ _ _ Hres) |].
        unfold embedRoot, rootPkg, embedPkg; reflexivity.
      - intros s Hs n vs Hd.
        apply mem_reduceDeps in Hd; destruct Hd as [_ Hd].
        apply mem_coreResolution in Hs.
        destruct Hs as
          [[k [v [Hp ->]]] |
           [[[pk pv] [m [u [Hp [Hm [Hu [Hi ->]]]]]]] |
            [[[ck cv] [a [Hc [Ha ->]]]] |
             [[[pk pv] [m [u [a [Hp [Hm [Hu [Hi [Ha ->]]]]]]]]] |
              [[[pk pv] [m [Hp [Hm [Hl [Ho ->]]]]]] |
               [[pk pv] [m [u [d [Hp [Hm [Hu [Hi [Hsl [Ht [e [He ->]]]]]]]]]]]]]]]]];
          cbn [fst snd] in Hd.
        + rewrite dependees_gran in Hd.
          apply T.DependeesSet.union_spec in Hd; destruct Hd as [Hd | Hd].
          * apply mem_entryEdges in Hd; destruct Hd as [a [Ha He]].
            injection He as -> ->.
            destruct (dp I (k, v) a) eqn:Hdp.
            -- destruct (ownAt I S pi (k, v) (slotKey I (base (k, v)) a))
                 as [w |] eqn:Ho.
               ++ pose proof (ownAt_some _ _ _ _ _ _ Ho) as Hi.
                  exists (Vs.Orig w); split.
                  ** apply mem_slotSet; right; exists w; split; [| reflexivity].
                     exact (res_slot_range _ _ _ _ Hres (k, v) Hp a Ha w Hi).
                  ** exact (HcoreI (k, v) _ w Hp Hi).
               ++ exists Vs.Bot; split.
                  ** apply mem_slotSet; left; split; [reflexivity | exact Hdp].
                  ** apply mem_coreResolution; right; right; right; right; left.
                     exists (k, v), (slotKey I (base (k, v)) a).
                     split; [exact Hp |].
                     split; [apply slotKey_childKeys, dirs_childDirs; exact Ha |].
                     split; [rewrite slotKey_fst; unfold loose;
                             apply Bool.orb_true_iff; right; exact Hdp |].
                     split; [exact Ho | reflexivity].
            -- destruct (Hslot (k, v) Hp a Ha Hdp) as [w [Hw Hi]].
               exists (Vs.Orig w); split;
                 [apply mem_slotSet; right; exists w; split; [exact Hw | reflexivity] |].
               exact (HcoreI (k, v) _ w Hp Hi).
          * apply mem_rootPeerEdges in Hd.
            destruct Hd as [Hq [r [Hr [Hact He]]]].
            injection He as -> ->.
            assert (Hbr : base (k, v) = inst_root I)
              by (rewrite Hq; apply base_rootPkg).
            rewrite Hbr in Hr, Hact |- *.
            destruct (root_peer_installs I S pi sg r Hres Hr Hact)
              as [w [Hw Hi]].
            rewrite <- Hq in Hi.
            exists (Vs.Orig w); split; [apply orig_embedVS; exact Hw |].
            exact (HcoreI (k, v) _ w Hp Hi).
        + apply dependees_int in Hd.
          destruct Hd as [He | [Hd | [Hd | Hd]]]; [injection He as -> -> | | |].
          * exists (Vs.Orig u); split;
              [apply T.VSet.singleton_spec; reflexivity |].
            exact (HcoreG (m, u) (proj1 Hi)).
          * apply mem_linkEdges in Hd; destruct Hd as [r [Hr He]].
            injection He as -> ->.
            assert (Ha : NSet.In (p_name r) (peerNames I (snd m, u)))
              by (apply mem_peerNames; exists r; split; [exact Hr | reflexivity]).
            exists (linkVal I S pi sg (pk, pv) (p_name r)); split.
            -- exact (linkVal_cands I S pi sg (pk, pv) m u r Hres Hp Hi Hr).
            -- exact (HcoreL (pk, pv) m u (p_name r) Hp Hi Ha).
          * apply mem_ownSight in Hd; destruct Hd as [Hdp [Hmk He]].
            injection He as -> ->.
            exists (sightVal I S pi sg (pk, pv) (fst m)); split.
            -- unfold sightVal.
               destruct (andb (chains I (pk, pv) (fst m)) (readb I S pi (pk, pv) (fst m)))
                 eqn:Hcr.
               ++ apply Bool.andb_true_iff in Hcr; destruct Hcr as [_ Hrd].
                  apply (readb_iff I S pi sg _ _ Hres) in Hrd.
                  rewrite Hmk in Hi.
                  destruct (res_dp_own _ _ _ _ Hres (pk, pv) Hp (fst m) u Hdp Hrd Hi)
                    as [Hs Hplain].
                  rewrite Hs; unfold plainKey.
                  match goal with |- context [KeyEqb.eqb ?x ?y] =>
                    replace (KeyEqb.eqb x y) with true
                      by (symmetry; apply KeyEqb.eqb_true_iff; exact Hplain)
                  end.
                  apply T.VSet.add_spec; left; reflexivity.
               ++ match goal with |- context [plainKey ?i ?p ?b] =>
                    destruct (plainKey i p b)
                  end;
                    [apply T.VSet.add_spec; right |];
                    apply T.VSet.singleton_spec; reflexivity.
            -- exact (HcoreS (pk, pv) (fst m) Hp
                        (chains_peerNames _ _ _ (dp_chains _ _ _ Hdp))).
          * apply mem_descEdges in Hd; destruct Hd as [d [e [Hsl [Ht [Hde He]]]]].
            injection He as -> ->.
            exists (Vs.Orig u); split; [apply T.VSet.singleton_spec; reflexivity |].
            apply mem_coreResolution; right; right; right; right; right.
            exists (pk, pv), m, u, d.
            do 6 (split; [assumption |]); exists e; split; [exact Hde | reflexivity].
        + cbn [dependees] in Hd; destruct (SOhh.empty_in _ Hd).
        + apply dependees_link in Hd; destruct Hd as [He | [Hd | Hd]].
          * injection He as -> ->.
            exists (sightVal I S pi sg (m, u) a); split.
            -- exact (sightVal_link I S pi sg (pk, pv) m u a Hres Hp Hi Ha).
            -- exact (HcoreS (m, u) a (proj1 Hi) Ha).
          * apply mem_holderEdges in Hd.
            destruct Hd as [[Hch He] | [Hch [Hh [Hxf He]]]].
            -- injection He as -> ->.
               exists (linkVal I S pi sg (pk, pv) a); split;
                 [apply T.VSet.singleton_spec; reflexivity |].
               rewrite <- (sightVal_holder I S pi sg (pk, pv) m u a Hres Hi Ha Hch).
               apply (HcoreS (pk, pv) a); [exact Hp |].
               unfold chains in Hch; apply Bool.andb_true_iff in Hch.
               apply NSet.mem_spec; exact (proj2 Hch).
            -- injection He as -> ->.
               exists (linkVal I S pi sg (pk, pv) a); split;
                 [apply T.VSet.singleton_spec; reflexivity |].
               unfold linkVal.
               rewrite (showsAt_holds I S pi sg (pk, pv) a Hch Hh).
               destruct (ownAt I S pi (pk, pv) (slotKey I (base (pk, pv)) a))
                 as [w |] eqn:Hs.
               ++ exact (HcoreI (pk, pv) _ w Hp (ownAt_some _ _ _ _ _ _ Hs)).
               ++ apply mem_coreResolution; right; right; right; right; left.
                  exists (pk, pv), (slotKey I (base (pk, pv)) a).
                  split; [exact Hp |]; split.
                  ** apply slotKey_childKeys, holds_childDirs; [exact Hh |].
                     apply mem_peerNames in Ha; destruct Ha as [r [Hr <-]].
                     exact (peerDirs_peer I _ r Hr).
                  ** split; [| split; [exact Hs | reflexivity]].
                     rewrite slotKey_fst.
                     destruct (loose I (pk, pv) a) eqn:Hl; [reflexivity |].
                     destruct (holds_installed I S pi sg (pk, pv) a Hres Hp Hh Hl)
                       as [w Hw].
                     rewrite (ownAt_installs I S pi sg _ _ _ Hres Hw) in Hs.
                     discriminate Hs.
          * apply mem_dpEdges in Hd.
            destruct Hd as [Hdp [[w [Hx He]] | [Hx He]]]; injection He as -> ->.
            -- exists Vs.Bot; split; [apply T.VSet.singleton_spec; reflexivity |].
               apply mem_coreResolution; right; right; right; right; left.
               exists (m, u), (slotKey I (base (m, u)) a).
               split; [exact (proj1 Hi) |].
               split; [apply slotKey_childKeys, dirs_childDirs, dp_dirs; exact Hdp |].
               split; [rewrite slotKey_fst; unfold loose;
                       apply Bool.orb_true_iff; right; exact Hdp |].
               split; [| reflexivity].
               destruct (ownAt I S pi (m, u) (slotKey I (base (m, u)) a))
                 as [w' |] eqn:Ho; [exfalso | reflexivity].
               assert (Hw : Shows I S pi sg (pk, pv) a w).
               { apply (showsAt_spec I S pi sg _ _ w Hres); unfold linkVal in Hx.
                 destruct (showsAt I S pi sg (pk, pv) a) as [w0 |];
                   [injection Hx as ->; reflexivity | discriminate Hx]. }
               exact (proj1 (res_dp _ _ _ _ Hres (pk, pv) Hp m u Hi a Hdp)
                        (ex_intro _ w Hw) w' (ownAt_some _ _ _ _ _ _ Ho)).
            -- assert (Hno : forall w, ~ Shows I S pi sg (pk, pv) a w).
               { intros w Hw; apply (showsAt_spec I S pi sg _ _ w Hres) in Hw.
                 unfold linkVal in Hx; rewrite Hw in Hx; discriminate Hx. }
               destruct (proj2 (res_dp _ _ _ _ Hres (pk, pv) Hp m u Hi a Hdp) Hno)
                 as [u' [Hu' Hi']].
               exists (Vs.Orig u'); split; [apply orig_embedVS; exact Hu' |].
               exact (HcoreI (m, u) _ u' (proj1 Hi) Hi').
        + cbn [dependees] in Hd; destruct (SOhh.empty_in _ Hd).
        + cbn [dependees] in Hd; destruct (SOhh.empty_in _ Hd).
      - intros n x1 x2 H1 H2.
        apply mem_coreResolution in H1; apply mem_coreResolution in H2.
        destruct H1 as
          [[k1 [v1 [Hp1 He1]]] |
           [[[pk1 pv1] [m1 [u1 [Hp1 [Hm1 [Hu1 [Hi1 He1]]]]]]] |
            [[[ck1 cv1] [a1 [Hc1 [Ha1 He1]]]] |
             [[[pk1 pv1] [m1 [u1 [a1 [Hp1 [Hm1 [Hu1 [Hi1 [Ha1 He1]]]]]]]]] |
              [[[pk1 pv1] [m1 [Hp1 [Hm1 [Hl1 [Ho1 He1]]]]]] |
               [[pk1 pv1] [m1 [u1 [d1 [Hp1 [Hm1 [Hu1 [Hi1 [Hs1 [Ht1 [e1 [Hd1 He1]]]]]]]]]]]]]]]]];
        destruct H2 as
          [[k2 [v2 [Hp2 He2]]] |
           [[[pk2 pv2] [m2 [u2 [Hp2 [Hm2 [Hu2 [Hi2 He2]]]]]]] |
            [[[ck2 cv2] [a2 [Hc2 [Ha2 He2]]]] |
             [[[pk2 pv2] [m2 [u2 [a2 [Hp2 [Hm2 [Hu2 [Hi2 [Ha2 He2]]]]]]]]] |
              [[[pk2 pv2] [m2 [Hp2 [Hm2 [Hl2 [Ho2 He2]]]]]] |
               [[pk2 pv2] [m2 [u2 [d2 [Hp2 [Hm2 [Hu2 [Hi2 [Hs2 [Ht2 [e2 [Hd2 He2]]]]]]]]]]]]]]]]];
          cbn [fst snd] in He1, He2; try congruence.
        + assert (pk1 = pk2) by congruence; assert (pv1 = pv2) by congruence;
            assert (m1 = m2) by congruence; subst.
          rewrite (res_unique _ _ _ _ Hres (pk2, pv2) m2 u1 u2 Hi1 Hi2) in He1.
          congruence.
        + assert (pk1 = pk2) by congruence; assert (pv1 = pv2) by congruence;
            assert (m1 = m2) by congruence; subst.
          rewrite (ownAt_installs I S pi sg _ _ _ Hres Hi1) in Ho2; discriminate Ho2.
        + assert (pk1 = pk2) by congruence; assert (pv1 = pv2) by congruence;
            assert (m1 = m2) by congruence; subst.
          rewrite (ownAt_installs I S pi sg _ _ _ Hres Hi2) in Ho1; discriminate Ho1.
        + injection He1 as -> ->; injection He2 as Ea Et Es ->.
          assert (m1 = m2) by (destruct m1, m2; cbn [fst snd] in *; congruence).
          subst m2 e2.
          rewrite (res_desc _ _ _ _ Hres (pk1, pv1) (pk2, pv2) m1 u1 u2 d1 d2 e1
                     Hp1 Hp2 Hi1 Hi2 Hs1 Hs2 Ht1 Ht2 Hd1 Hd2).
          reflexivity.
    Qed.

    Theorem dependees_targetNames : forall I s h,
        T.PkgSet.In s (reduceReal I) -> T.DependeesSet.In h (dependees I s) ->
        NmSet.In (fst h) (targetNames I).
    Proof.
      intros I [n x] h Hs Hh; apply mem_reduceReal in Hs.
      destruct Hs as [Hn Hx]; apply mem_targetNames in Hn; apply mem_targetNames.
      destruct n as [k w | k v m | k v a | k v m u a | a t s]; cbn [TargetName] in Hn.
      - cbn [versions] in Hx.
        apply SOvcv.in_if_empty in Hx as [_ Hx].
        apply T.VSet.singleton_spec in Hx; subst x.
        rewrite dependees_gran in Hh; apply T.DependeesSet.union_spec in Hh.
        destruct Hh as [Hh | Hh].
        + apply mem_entryEdges in Hh; destruct Hh as [a [Ha ->]].
          cbn [fst snd TargetName]; split; [exact Hn |].
          apply slotKey_childKeys, dirs_childDirs; exact Ha.
        + apply mem_rootPeerEdges in Hh; destruct Hh as [Hq [r [Hr [Hact ->]]]].
          cbn [fst snd TargetName]; split; [exact Hn |].
          change (k, w) with (fst (k, w), snd (k, w)).
          rewrite <- surjective_pairing, Hq.
          rewrite Hq, base_rootPkg in Hr, Hact.
          rewrite base_rootPkg; exact (rootPeer_childKeys I r Hr Hact).
      - destruct Hn as [Hkv Hm].
        apply versions_int in Hx.
        destruct Hx as [[-> _] | [u [Hu ->]]];
          [cbn [dependees] in Hh; destruct (SOhh.empty_in _ Hh) |].
        apply dependees_int in Hh.
        destruct Hh as [-> | [Hh | [Hh | Hh]]].
        + cbn [fst TargetName]; exact (childCands_real I (k, v) m u Hu).
        + apply mem_linkEdges in Hh; destruct Hh as [r [Hr ->]].
          cbn [fst snd TargetName].
          split; [exact Hkv | split; [exact Hm | split]].
          * pose proof (childCands_real I (k, v) m u Hu) as H.
            apply mem_realPkgs in H; destruct H as [_ H].
            apply mem_realVersions; exact H.
          * apply mem_peerNames; exists r; split; [exact Hr | reflexivity].
        + apply mem_ownSight in Hh; destruct Hh as [Hdp [_ ->]].
          cbn [fst snd TargetName]; split; [exact Hkv |].
          exact (chains_peerNames I (k, v) (fst m) (dp_chains _ _ _ Hdp)).
        + apply mem_descEdges in Hh; destruct Hh as [d [e [Hsl [Ht [Hde ->]]]]].
          cbn [fst TargetName].
          destruct (slotOf_dep I _ _ _ Hsl) as [Hin Hdir].
          exists (base (k, v)), d; split; [exact Hin |].
          apply in_descOf; repeat split; assumption.
      - cbn [dependees] in Hh; destruct (SOhh.empty_in _ Hh).
      - destruct Hn as [Hkv [Hm [Hu Ha]]].
        assert (Hmu : PkgSet.In (m, u) (realPkgs I)).
        { apply mem_realPkgs; split; [exact (childKeys_keysOf I _ m Hm) |].
          apply mem_realVersions in Hu; exact Hu. }
        apply dependees_link in Hh; destruct Hh as [-> | [Hh | Hh]].
        + cbn [fst TargetName]; split; [exact Hmu | exact Ha].
        + apply mem_holderEdges in Hh.
          destruct Hh as [[Hch ->] | [_ [Hh [_ ->]]]];
            cbn [fst snd TargetName]; split; try exact Hkv.
          * unfold chains in Hch; apply Bool.andb_true_iff in Hch.
            apply NSet.mem_spec; exact (proj2 Hch).
          * apply slotKey_childKeys, holds_childDirs; [exact Hh |].
            apply mem_peerNames in Ha; destruct Ha as [r [Hr <-]].
            exact (peerDirs_peer I _ r Hr).
        + apply mem_dpEdges in Hh.
          destruct Hh as [Hdp [[w [_ ->]] | [_ ->]]];
            cbn [fst snd TargetName]; (split; [exact Hmu |]);
            apply slotKey_childKeys, dirs_childDirs, dp_dirs; exact Hdp.
      - cbn [dependees] in Hh; destruct (SOhh.empty_in _ Hh).
    Qed.

    Inductive Reached (I : Inst) : T.Pkg.t -> Prop :=
    | reached_root : Reached I (embedRoot I)
    | reached_dependee : forall s h x,
        Reached I s -> T.DependeesSet.In h (dependees I s) ->
        T.VSet.In x (versions I (fst h)) -> Reached I (fst h, x).

    Theorem reached_reduceReal : forall I s,
        RepoSet.In (inst_root I) (inst_repo I) ->
        Reached I s -> T.PkgSet.In s (reduceReal I).
    Proof.
      intros I s Hroot H; induction H as [| s h x Hs IH Hh Hx].
      - assert (Hr : PkgSet.In (rootPkg I) (realPkgs I)).
        { apply mem_realPkgs; split; [| rewrite base_rootPkg; exact Hroot].
          unfold keysOf; apply KeySet.add_spec; left; reflexivity. }
        unfold embedRoot, embedPkg.
        apply mem_reduceReal; split; [apply mem_targetNames; exact Hr |].
        exact (versions_gran_real I (fst (rootPkg I)) (snd (rootPkg I)) Hr).
      - apply mem_reduceReal; split; [| exact Hx].
        exact (dependees_targetNames I s h IH Hh).
    Qed.

    Theorem lookup_resolution : forall I S,
        RepoSet.In (inst_root I) (inst_repo I) ->
        (forall s, T.PkgSet.In s S -> Reached I s) ->
        T.PkgSet.In (embedRoot I) S ->
        (forall s, T.PkgSet.In s S ->
         forall n vs, T.DependeesSet.In (n, vs) (dependees I s) ->
         exists v, T.VSet.In v vs /\ T.PkgSet.In (n, v) S) ->
        T.VersionUnique S ->
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S.
    Proof.
      intros I S Hroot Hreach HrS Hclo Huniq; constructor.
      - intros s Hs; exact (reached_reduceReal I s Hroot (Hreach s Hs)).
      - exact HrS.
      - intros s Hs n vs Hd; apply mem_reduceDeps in Hd.
        exact (Hclo s Hs n vs (proj2 Hd)).
      - exact Huniq.
    Qed.

    Module Lookup.

      Definition repoPreimage (I : Inst) (ns : NSet.t) : RepoSet.t :=
        RepoSet.filter (fun p => NSet.mem (fst p) ns) (inst_repo I).

      Definition subInst (I : Inst) (ns : NSet.t)
          (deps : list (RPkg.t * Dependency))
          (prs : list (RPkg.t * PeerDependency))
        : Inst :=
        {| inst_repo := repoPreimage I ns
         ; inst_dep := deps
         ; inst_peer := prs
         ; inst_ovr := inst_ovr I
         ; inst_root := inst_root I |}.

      Definition ownDependencies (I : Inst) (p : RPkg.t)
        : list (RPkg.t * Dependency) :=
        List.filter (fun q => RPkgEqb.eqb (fst q) p) (inst_dep I).

      Definition ownPeerDependencies (I : Inst) (p : RPkg.t)
        : list (RPkg.t * PeerDependency) :=
        List.filter (fun q => RPkgEqb.eqb (fst q) p) (inst_peer I).

      Definition twoPeers (I : Inst) (p c : RPkg.t)
        : list (RPkg.t * PeerDependency) :=
        List.filter
          (fun q => orb (RPkgEqb.eqb (fst q) p) (RPkgEqb.eqb (fst q) c))
          (inst_peer I).

      Definition twoDeps (I : Inst) (p c : RPkg.t)
        : list (RPkg.t * Dependency) :=
        List.filter
          (fun q => orb (RPkgEqb.eqb (fst q) p) (RPkgEqb.eqb (fst q) c))
          (inst_dep I).

      Definition peerDependenciesNamed (I : Inst) (n : N.t)
        : list (RPkg.t * PeerDependency) :=
        List.filter (fun q => NEqb.eqb (p_name (snd q)) n) (inst_peer I).

      Definition slotTargets (I : Inst) (p : RPkg.t) : NSet.t :=
        namesOfL d_target (dependenciesOf I p).

      Lemma mem_repoPreimage : forall I ns p,
          RepoSet.In p (repoPreimage I ns) <->
          RepoSet.In p (inst_repo I) /\ NSet.In (fst p) ns.
      Proof.
        intros I ns p; unfold repoPreimage; rewrite RSS.filter_spec'.
        rewrite NSet.mem_spec; reflexivity.
      Qed.

      Lemma repo_subInst : forall I ns deps prs n w,
          NSet.In n ns ->
          (RepoSet.In (n, w) (inst_repo (subInst I ns deps prs)) <->
           RepoSet.In (n, w) (inst_repo I)).
      Proof.
        intros I ns deps prs n w Hn; cbn [inst_repo subInst].
        rewrite mem_repoPreimage; cbn [fst]; split;
          [intros [H _]; exact H | intro H; split; [exact H | exact Hn]].
      Qed.

      Lemma realVersions_subInst : forall I ns deps prs n,
          NSet.In n ns ->
          realVersions (inst_repo (subInst I ns deps prs)) n =
          realVersions (inst_repo I) n.
      Proof.
        intros I ns deps prs n Hn; apply VSet.ext; intro w.
        rewrite !mem_realVersions; apply repo_subInst; exact Hn.
      Qed.

      Lemma ownDependencies_id : forall I p,
          ownedBy p (ownDependencies I p) = ownedBy p (inst_dep I).
      Proof.
        intros I p; unfold ownDependencies; apply ownedBy_filter.
        intros d _; cbn [fst]; apply RPkgEqb.eqb_refl.
      Qed.

      Lemma ownPeerDependencies_id : forall I p,
          ownedBy p (ownPeerDependencies I p) = ownedBy p (inst_peer I).
      Proof.
        intros I p; unfold ownPeerDependencies; apply ownedBy_filter.
        intros r _; cbn [fst]; apply RPkgEqb.eqb_refl.
      Qed.

      Lemma twoPeers_left : forall I p c,
          ownedBy p (twoPeers I p c) = ownedBy p (inst_peer I).
      Proof.
        intros I p c; unfold twoPeers; apply ownedBy_filter.
        intros r _; cbn [fst]; rewrite RPkgEqb.eqb_refl; reflexivity.
      Qed.

      Lemma twoPeers_right : forall I p c,
          ownedBy c (twoPeers I p c) = ownedBy c (inst_peer I).
      Proof.
        intros I p c; unfold twoPeers; apply ownedBy_filter.
        intros r _; cbn [fst]; rewrite RPkgEqb.eqb_refl, Bool.orb_true_r.
        reflexivity.
      Qed.

      Lemma twoDeps_left : forall I p c,
          ownedBy p (twoDeps I p c) = ownedBy p (inst_dep I).
      Proof.
        intros I p c; unfold twoDeps; apply ownedBy_filter.
        intros d _; cbn [fst]; rewrite RPkgEqb.eqb_refl; reflexivity.
      Qed.

      Lemma twoDeps_right : forall I p c,
          ownedBy c (twoDeps I p c) = ownedBy c (inst_dep I).
      Proof.
        intros I p c; unfold twoDeps; apply ownedBy_filter.
        intros d _; cbn [fst]; rewrite RPkgEqb.eqb_refl, Bool.orb_true_r.
        reflexivity.
      Qed.

      Lemma mem_peerNames_named : forall I ns deps n p,
          NSet.mem n
            (peerNames (subInst I ns deps (peerDependenciesNamed I n)) p) =
          NSet.mem n (peerNames I p).
      Proof.
        intros I ns deps n p; apply Bool.eq_iff_eq_true.
        rewrite !NSet.mem_spec, !mem_peerNames; cbn [inst_peer subInst].
        unfold peerDependenciesNamed.
        split; intros [r [Hr Hn]]; exists r; split; try exact Hn.
        - apply List.filter_In in Hr; exact (proj1 Hr).
        - apply List.filter_In; split;
            [exact Hr | cbn [snd]; apply NEqb.eqb_true_iff; exact Hn].
      Qed.

      Lemma mem_rootPeerDirs_named : forall I ns deps n,
          NSet.mem n
            (rootPeerDirs (subInst I ns deps (peerDependenciesNamed I n))) =
          NSet.mem n (rootPeerDirs I).
      Proof.
        intros I ns deps n; apply Bool.eq_iff_eq_true.
        rewrite !NSet.mem_spec, !mem_rootPeerDirs; cbn [inst_peer subInst].
        unfold peerDependenciesNamed.
        split; intros [q [r [Hq Hr]]]; exists q, r; split; try exact Hr.
        - apply List.filter_In in Hq; exact (proj1 Hq).
        - apply List.filter_In; split;
            [exact Hq | apply NEqb.eqb_true_iff; exact (proj2 Hr)].
      Qed.

      Lemma chains_named : forall I ns deps n q,
          chains (subInst I ns deps (peerDependenciesNamed I n)) q n =
          chains I q n.
      Proof.
        intros I ns deps n q; unfold chains.
        change (rootPkg (subInst I ns deps (peerDependenciesNamed I n)))
          with (rootPkg I).
        rewrite mem_peerNames_named; reflexivity.
      Qed.

      Lemma dependenciesOf_agree : forall I ns deps prs p,
          ownedBy p deps = ownedBy p (inst_dep I) ->
          dependenciesOf (subInst I ns deps prs) p = dependenciesOf I p.
      Proof.
        intros I ns deps prs p Hdeps; unfold dependenciesOf, depActive.
        cbn [inst_dep inst_root subInst]; rewrite Hdeps; reflexivity.
      Qed.

      Lemma slotOf_agree : forall I ns deps prs p a,
          ownedBy p deps = ownedBy p (inst_dep I) ->
          slotOf (subInst I ns deps prs) p a = slotOf I p a.
      Proof.
        intros I ns deps prs p a Hdeps; unfold slotOf.
        rewrite (dependenciesOf_agree I ns deps prs p Hdeps); reflexivity.
      Qed.

      Lemma dirs_agree : forall I ns deps prs p,
          ownedBy p deps = ownedBy p (inst_dep I) ->
          dirs (subInst I ns deps prs) p = dirs I p.
      Proof.
        intros I ns deps prs p Hdeps; unfold dirs.
        rewrite (dependenciesOf_agree I ns deps prs p Hdeps); reflexivity.
      Qed.

      Lemma slotKey_agree : forall I ns deps prs p a,
          ownedBy p deps = ownedBy p (inst_dep I) ->
          slotKey (subInst I ns deps prs) p a = slotKey I p a.
      Proof.
        intros I ns deps prs p a Hdeps; unfold slotKey.
        rewrite (slotOf_agree I ns deps prs p a Hdeps); reflexivity.
      Qed.

      Lemma peerNames_agree : forall I ns deps prs p,
          ownedBy p prs = ownedBy p (inst_peer I) ->
          peerNames (subInst I ns deps prs) p = peerNames I p.
      Proof.
        intros I ns deps prs p Hp; unfold peerNames, peerDependenciesAt.
        cbn [inst_peer subInst]; rewrite Hp; reflexivity.
      Qed.

      Lemma chains_agree : forall I ns deps prs q a,
          ownedBy (base q) prs = ownedBy (base q) (inst_peer I) ->
          chains (subInst I ns deps prs) q a = chains I q a.
      Proof.
        intros I ns deps prs q a Hp; unfold chains.
        change (rootPkg (subInst I ns deps prs)) with (rootPkg I).
        rewrite (peerNames_agree I ns deps prs (base q) Hp); reflexivity.
      Qed.

      Lemma holds_agree : forall I ns deps prs q a,
          ownedBy (base q) deps = ownedBy (base q) (inst_dep I) ->
          holds (subInst I ns deps prs) q a = holds I q a.
      Proof.
        intros I ns deps prs q a Hd; unfold holds.
        change (rootPkg (subInst I ns deps prs)) with (rootPkg I).
        rewrite (dirs_agree I ns deps prs (base q) Hd); reflexivity.
      Qed.

      Lemma dp_agree : forall I ns deps prs q a,
          ownedBy (base q) deps = ownedBy (base q) (inst_dep I) ->
          chains (subInst I ns deps prs) q a = chains I q a ->
          dp (subInst I ns deps prs) q a = dp I q a.
      Proof.
        intros I ns deps prs q a Hd Hch; unfold dp.
        rewrite Hch, (dirs_agree I ns deps prs (base q) Hd); reflexivity.
      Qed.

      Lemma loose_agree : forall I ns deps prs q a,
          ownedBy (base q) deps = ownedBy (base q) (inst_dep I) ->
          chains (subInst I ns deps prs) q a = chains I q a ->
          loose (subInst I ns deps prs) q a = loose I q a.
      Proof.
        intros I ns deps prs q a Hd Hch; unfold loose.
        change (rootPkg (subInst I ns deps prs)) with (rootPkg I).
        rewrite (dirs_agree I ns deps prs (base q) Hd),
          (dp_agree I ns deps prs q a Hd Hch); reflexivity.
      Qed.

      Lemma slotCands_agree : forall I ns deps prs p,
          ownedBy p deps = ownedBy p (inst_dep I) ->
          (forall d, In d (dependenciesOf I p) -> NSet.In (d_target d) ns) ->
          forall a,
            slotCands (subInst I ns deps prs) p a =
            slotCands I p a.
      Proof.
        intros I ns deps prs p Hdeps Htgt a; unfold slotCands.
        rewrite (slotOf_agree I ns deps prs p a Hdeps).
        destruct (slotOf I p a) as [d |] eqn:Hd; [| reflexivity].
        cbn [inst_ovr subInst].
        rewrite realVersions_subInst; [reflexivity |].
        apply Htgt; exact (proj1 (findDepL_some _ _ _ Hd)).
      Qed.

      Lemma peerCandsAt_agree : forall I ns deps prs p r,
          ownedBy p deps = ownedBy p (inst_dep I) ->
          NSet.In (snd (slotKey I p (p_name r))) ns ->
          peerCandsAt (subInst I ns deps prs) p r = peerCandsAt I p r.
      Proof.
        intros I ns deps prs p r Hd Hn; unfold peerCandsAt, peerKeyAt.
        rewrite (slotKey_agree I ns deps prs p (p_name r) Hd).
        cbn [inst_ovr subInst]; rewrite realVersions_subInst;
          [reflexivity | exact Hn].
      Qed.

      Lemma if_scrutinee : forall (b1 b2 : bool) (x y : T.VSet.t),
          b1 = b2 -> (if b1 then x else y) = (if b2 then x else y).
      Proof. intros b1 b2 x y ->; reflexivity. Qed.

      Lemma mem_eq_of_iffP : forall (s s' : PkgSet.t) x,
          (PkgSet.In x s <-> PkgSet.In x s') ->
          PkgSet.mem x s = PkgSet.mem x s'.
      Proof.
        intros s s' x H; apply Bool.eq_iff_eq_true.
        rewrite !PkgSet.mem_spec; exact H.
      Qed.

      Lemma slotTargets_spec : forall I p d,
          In d (dependenciesOf I p) -> NSet.In (d_target d) (slotTargets I p).
      Proof.
        intros I p d Hd; unfold slotTargets; apply mem_namesOfL.
        exists d; split; [exact Hd | reflexivity].
      Qed.

      Lemma childCands_agree : forall I ns deps prs (q : Pkg.t) (m : NKey.t),
          ownedBy (base q) deps = ownedBy (base q) (inst_dep I) ->
          (forall d, In d (dependenciesOf I (base q)) ->
             NSet.In (d_target d) ns) ->
          NSet.In (snd m) ns ->
          NSet.mem (fst m) (rootPeerDirs (subInst I ns deps prs)) =
            NSet.mem (fst m) (rootPeerDirs I) ->
          chains (subInst I ns deps prs) q (fst m) = chains I q (fst m) ->
          childCands (subInst I ns deps prs) q m =
          childCands I q m.
      Proof.
        intros I ns deps prs q m Hd Ht Hm Hpa Hch; unfold childCands.
        change (rootPkg (subInst I ns deps prs)) with (rootPkg I).
        rewrite (slotKey_agree I ns deps prs (base q) (fst m) Hd).
        rewrite (dirs_agree I ns deps prs (base q) Hd).
        rewrite Hpa, Hch.
        destruct (KeyEqb.eqb m (slotKey I (base q) (fst m)));
          destruct (chains I q (fst m));
          destruct (NSet.mem (fst m) (dirs I (base q)));
          destruct (andb (PkgEqb.eqb q (rootPkg I)) (NSet.mem (fst m) (rootPeerDirs I)));
          try reflexivity;
          first [apply slotCands_agree; assumption | apply realVersions_subInst; exact Hm].
      Qed.

      Lemma slotKey_in : forall I p a ns,
          NSet.In a ns ->
          (forall d, In d (dependenciesOf I p) -> NSet.In (d_target d) ns) ->
          NSet.In (snd (slotKey I p a)) ns.
      Proof.
        intros I p a ns Ha Ht; unfold slotKey.
        destruct (slotOf I p a) as [d |] eqn:Hd; cbn [snd];
          [apply Ht; exact (proj1 (findDepL_some _ _ _ Hd)) | exact Ha].
      Qed.

      Definition keyedDeps (I : Inst) (k : NKey.t)
        : list (RPkg.t * Dependency) :=
        List.filter
          (fun q => KeyEqb.eqb (d_dir (snd q), d_target (snd q)) k)
          (inst_dep I).

      Definition keyedPeers (I : Inst) (k : NKey.t)
        : list (RPkg.t * PeerDependency) :=
        List.filter
          (fun q => KeyEqb.eqb (p_name (snd q), p_name (snd q)) k)
          (inst_peer I).

      Definition granSubInst (I : Inst) (k : NKey.t) (w : V.t)
          (I' : Inst) : Prop :=
        inst_root I' = inst_root I /\
        (RepoSet.In (snd k, w) (inst_repo I') <->
         RepoSet.In (snd k, w) (inst_repo I)) /\
        incl (inst_dep I') (keyedDeps I k) /\
        (keyedDeps I k <> nil -> inst_dep I' <> nil) /\
        incl (inst_peer I') (keyedPeers I k) /\
        (keyedDeps I k = nil -> keyedPeers I k <> nil ->
         inst_peer I' <> nil).

      Lemma keysOf_granSubInst : forall I k w I',
          granSubInst I k w I' ->
          (KeySet.In k (keysOf I') <-> KeySet.In k (keysOf I)).
      Proof.
        intros I k w I' [Hroot [_ [Hd [Hdne [Hp Hpne]]]]].
        unfold keysOf, rootKey; rewrite Hroot, !KeySet.add_spec,
          !KeySet.union_spec, !mem_keysOfL.
        assert (Hkd : forall q, In q (keyedDeps I k) ->
                  In q (inst_dep I) /\
                  (d_dir (snd q), d_target (snd q)) = k).
        { intros q Hq; apply List.filter_In in Hq.
          destruct Hq as [Hq He]; apply KeyEqb.eqb_true_iff in He.
          split; assumption. }
        assert (Hkp : forall q, In q (keyedPeers I k) ->
                  In q (inst_peer I) /\
                  (p_name (snd q), p_name (snd q)) = k).
        { intros q Hq; apply List.filter_In in Hq.
          destruct Hq as [Hq He]; apply KeyEqb.eqb_true_iff in He.
          split; assumption. }
        split.
        - intros [E | [[q [Hq E]] | [q [Hq E]]]]; [left; exact E | |].
          + right; left; exists q; exact (conj (proj1 (Hkd q (Hd q Hq))) E).
          + right; right; exists q; exact (conj (proj1 (Hkp q (Hp q Hq))) E).
        - intros [E | Hk]; [left; exact E | right].
          destruct (keyedDeps I k) as [| q0 l0] eqn:Hkl.
          + destruct Hk as [[q [Hq E]] | [q [Hq E]]].
            * exfalso.
              assert (Hin : In q (keyedDeps I k))
                by (apply List.filter_In; split;
                    [exact Hq | apply KeyEqb.eqb_true_iff; exact E]).
              rewrite Hkl in Hin; destruct Hin.
            * destruct (inst_peer I') as [| q1 l1] eqn:Hpl.
              -- exfalso; refine (Hpne eq_refl _ eq_refl); intro Hn.
                 assert (Hin : In q (keyedPeers I k))
                   by (apply List.filter_In; split;
                       [exact Hq | apply KeyEqb.eqb_true_iff; exact E]).
                 rewrite Hn in Hin; destruct Hin.
              -- right; exists q1; split; [left; reflexivity |].
                 refine (proj2 (Hkp q1 (Hp q1 _))).
                 left; reflexivity.
          + destruct (inst_dep I') as [| q1 l1] eqn:Hdl.
            * exfalso; refine (Hdne _ eq_refl); discriminate.
            * left; exists q1; split; [left; reflexivity |].
              refine (proj2 (Hkd q1 (Hd q1 _))).
              left; reflexivity.
      Qed.

      Theorem versions_lookupGranular : forall I k w I',
          granSubInst I k w I' ->
          versions I' (Nm.Granular k w) = versions I (Nm.Granular k w).
      Proof.
        intros I k w I' Hsub; cbn [versions].
        pose proof (keysOf_granSubInst I k w I' Hsub) as Hk.
        destruct Hsub as [_ [Hr _]].
        apply if_scrutinee, mem_eq_of_iffP; rewrite !mem_realPkgs.
        unfold Available, base; cbn [fst snd]; rewrite Hk, Hr; reflexivity.
      Qed.

      Definition intSubInst (I : Inst) (p : RPkg.t) (m : NKey.t) : Inst :=
        subInst I (NSet.add (snd m) (slotTargets I p)) (ownDependencies I p)
          (peerDependenciesNamed I (fst m)).

      Theorem versions_lookupIntermediate : forall I k v m,
          versions (intSubInst I (snd k, v) m) (Nm.Intermediate k v m) =
          versions I (Nm.Intermediate k v m).
      Proof.
        intros I k v m; cbn [versions]; unfold intSubInst.
        rewrite (loose_agree I _ _ _ (k, v) (fst m) (ownDependencies_id I (snd k, v))
                   (chains_named I _ _ (fst m) (k, v))).
        rewrite childCands_agree; [reflexivity | ..].
        - apply ownDependencies_id.
        - intros d Hd; apply NSet.add_spec; right;
            apply slotTargets_spec; exact Hd.
        - apply NSet.add_spec; left; reflexivity.
        - apply mem_rootPeerDirs_named.
        - apply chains_named.
      Qed.

      Definition sightSubInst (I : Inst) (c : RPkg.t) (a : N.t) : Inst :=
        subInst I (NSet.add a (slotTargets I c)) (ownDependencies I c)
          (ownPeerDependencies I c).

      Lemma sightCandsL_agree : forall I ns deps prs a l,
          NSet.In a ns ->
          sightCandsL (subInst I ns deps prs) a l = sightCandsL I a l.
      Proof.
        intros I ns deps prs a l Ha; induction l as [| r l IH];
          cbn [sightCandsL]; [reflexivity |].
        unfold plainCands; cbn [inst_ovr subInst].
        rewrite realVersions_subInst, IH; [reflexivity | exact Ha].
      Qed.

      Theorem versions_lookupSight : forall I k v a,
          versions (sightSubInst I (snd k, v) a) (Nm.Sight k v a) =
          versions I (Nm.Sight k v a).
      Proof.
        intros I k v a; cbn [versions]; unfold sightSubInst, sightCands.
        rewrite sightCandsL_agree; [| apply NSet.add_spec; left; reflexivity].
        rewrite (slotCands_agree I _ _ _ (snd k, v) (ownDependencies_id I (snd k, v)));
          [| intros d Hd; apply NSet.add_spec; right; apply slotTargets_spec; exact Hd].
        unfold peerDependenciesAt; cbn [inst_peer subInst].
        rewrite ownPeerDependencies_id; reflexivity.
      Qed.

      Definition descSubInst (I : Inst) (t : N.t) : Inst :=
        subInst I (NSet.singleton t) nil nil.

      Theorem versions_lookupDesc : forall I a t s,
          versions (descSubInst I t) (Nm.Desc a t s) = versions I (Nm.Desc a t s).
      Proof.
        intros I a t s; cbn [versions]; unfold descSubInst.
        rewrite realVersions_subInst; [reflexivity | apply NSet.singleton_spec; reflexivity].
      Qed.

      Lemma linkCands_agree : forall I ns deps prs (q c : Pkg.t) r,
          ownedBy (base q) deps = ownedBy (base q) (inst_dep I) ->
          ownedBy (base q) prs = ownedBy (base q) (inst_peer I) ->
          ownedBy (base c) deps = ownedBy (base c) (inst_dep I) ->
          ownedBy (base c) prs = ownedBy (base c) (inst_peer I) ->
          NSet.In (snd (slotKey I (base q) (p_name r))) ns ->
          (forall d, In d (dependenciesOf I (base c)) -> NSet.In (d_target d) ns) ->
          linkCands (subInst I ns deps prs) q c r = linkCands I q c r.
      Proof.
        intros I ns deps prs q c r Hd Hp Hdc Hpc Hn Htc.
        unfold linkCands, peerCands, peerOpt; cbv zeta.
        rewrite (chains_agree I ns deps prs q _ Hp),
          (holds_agree I ns deps prs q _ Hd),
          (loose_agree I ns deps prs q _ Hd (chains_agree I ns deps prs q _ Hp)),
          (peerCandsAt_agree I ns deps prs (base q) r Hd Hn),
          (slotCands_agree I ns deps prs (base c) Hdc Htc (p_name r)),
          (dp_agree I ns deps prs c _ Hdc (chains_agree I ns deps prs c _ Hpc)).
        reflexivity.
      Qed.

      Definition linkSubInst (I : Inst) (p c : RPkg.t) (a : N.t) : Inst :=
        subInst I (NSet.add a (NSet.union (slotTargets I p) (slotTargets I c)))
          (twoDeps I p c) (twoPeers I p c).

      Theorem versions_lookupLink : forall I k v m u a,
          versions (linkSubInst I (snd k, v) (snd m, u) a) (Nm.Link k v m u a) =
          versions I (Nm.Link k v m u a).
      Proof.
        intros I k v m u a; cbn [versions]; unfold linkSubInst, linkVers.
        change (base (m, u)) with (snd m, u).
        unfold peerDependenciesAt at 1; cbn [inst_peer subInst].
        rewrite twoPeers_right; fold (peerDependenciesAt I (snd m, u)).
        induction (peerDependenciesAt I (snd m, u)) as [| r l IH];
          cbn [linkVersL]; [reflexivity |].
        rewrite IH; destruct (NEqb.eqb (p_name r) a) eqn:Hn; [| reflexivity].
        apply NEqb.eqb_true_iff in Hn.
        rewrite (linkCands_agree I _ _ _ (k, v) (m, u) r
                   (twoDeps_left I (snd k, v) (snd m, u))
                   (twoPeers_left I (snd k, v) (snd m, u))
                   (twoDeps_right I (snd k, v) (snd m, u))
                   (twoPeers_right I (snd k, v) (snd m, u))); [reflexivity | |].
        - apply slotKey_in; [rewrite Hn; apply NSet.add_spec; left; reflexivity |].
          intros d Hd; apply NSet.add_spec; right; apply NSet.union_spec; left.
          apply slotTargets_spec; exact Hd.
        - intros d Hd; apply NSet.add_spec; right; apply NSet.union_spec; right.
          apply slotTargets_spec; exact Hd.
      Qed.

      Definition pkgSubInst (I : Inst) (p : RPkg.t) : Inst :=
        subInst I (NSet.union (slotTargets I p) (peerNames I p))
          (ownDependencies I p) (ownPeerDependencies I p).

      Lemma slotKey_peerTargets : forall I p p' r,
          In r (peerDependenciesAt I p') ->
          NSet.In (snd (slotKey I p (p_name r)))
            (NSet.union (slotTargets I p) (peerNames I p')).
      Proof.
        intros I p p' r Hr; unfold slotKey; apply NSet.union_spec.
        destruct (slotOf I p (p_name r)) as [d |] eqn:Hd; cbn [snd].
        - left; apply slotTargets_spec; exact (proj1 (findDepL_some _ _ _ Hd)).
        - right; unfold peerNames; apply mem_namesOfL.
          exists r; split; [exact Hr | reflexivity].
      Qed.

      Lemma peerDeps_agree : forall I k v p p',
          let I' := subInst I
                      (NSet.union (slotTargets I p) (peerNames I p'))
                      (ownDependencies I p) (ownPeerDependencies I p') in
          depsOfL (fun r =>
              (Nm.Intermediate k v (peerKeyAt I' p r),
               embedVS (peerCandsAt I' p r)))
            (activePeers I' p p') =
          depsOfL (fun r =>
              (Nm.Intermediate k v (peerKeyAt I p r),
               embedVS (peerCandsAt I p r)))
            (activePeers I p p').
      Proof.
        intros I k v p p' I'.
        pose proof (ownDependencies_id I p) as Hd.
        assert (Hpr : peerDependenciesAt I' p' = peerDependenciesAt I p')
          by (unfold peerDependenciesAt; cbn [inst_peer subInst];
              apply ownPeerDependencies_id).
        unfold activePeers, peerActive; rewrite Hpr.
        unfold I'; rewrite (dirs_agree I _ _ _ p Hd).
        unfold depsOfL; f_equal; apply map_ext_in; intros r Hr.
        apply List.filter_In in Hr; destruct Hr as [Hr _].
        unfold peerCandsAt, peerKeyAt, peerKeyAt.
        rewrite (slotKey_agree I _ _ _ p (p_name r) Hd).
        rewrite realVersions_subInst;
          [reflexivity | apply slotKey_peerTargets; exact Hr].
      Qed.

      Theorem dependees_lookupGranular : forall I k v,
          dependees (pkgSubInst I (snd k, v))
            (Nm.Granular k v, Vs.Orig v) =
          dependees I (Nm.Granular k v, Vs.Orig v).
      Proof.
        intros I k v; rewrite !dependees_gran.
        pose proof (ownDependencies_id I (snd k, v)) as Hd.
        pose proof (ownPeerDependencies_id I (snd k, v)) as Hp.
        assert (Htgt : forall d, In d (dependenciesOf I (snd k, v)) ->
                   NSet.In (d_target d)
                     (NSet.union (slotTargets I (snd k, v))
                        (peerNames I (snd k, v)))).
        { intros d Hdr; apply NSet.union_spec; left;
            apply slotTargets_spec; exact Hdr. }
        unfold pkgSubInst; f_equal.
        - unfold entryEdges, slotSet.
          unfold depsOfL; f_equal.
          unfold base at 1 3; cbn [fst snd].
          rewrite (dirs_agree I _ _ _ (snd k, v) Hd).
          apply map_ext_in; intros a _.
          rewrite (dp_agree I _ _ _ (k, v) a Hd (chains_agree I _ _ _ (k, v) a Hp)).
          unfold base; cbn [fst snd].
          rewrite (slotKey_agree I _ _ _ (snd k, v) a Hd).
          rewrite (slotCands_agree I _ _ _ (snd k, v) Hd Htgt a).
          reflexivity.
        - unfold rootPeerEdges.
          change (rootPkg (subInst I _ _ _)) with (rootPkg I).
          destruct (PkgEqb.eqb _ (rootPkg I)); [| reflexivity].
          unfold base; cbn [fst snd]; apply peerDeps_agree.
      Qed.

      Definition peerSubInst (I : Inst) (p : RPkg.t) (m : NKey.t) (u : V.t)
        : Inst :=
        subInst I
          (NSet.union (slotTargets I p)
             (NSet.union (peerNames I (snd m, u)) (slotTargets I (snd m, u))))
          (twoDeps I p (snd m, u)) (twoPeers I p (snd m, u)).

      Lemma linkEdges_agree : forall I k v m u,
          linkEdges (peerSubInst I (snd k, v) m u) (k, v) m u =
          linkEdges I (k, v) m u.
      Proof.
        intros I k v m u; unfold peerSubInst.
        assert (Hpr : forall ns deps,
                   peerDependenciesAt
                     (subInst I ns deps (twoPeers I (snd k, v) (snd m, u))) (snd m, u) =
                   peerDependenciesAt I (snd m, u))
          by (intros ns deps; unfold peerDependenciesAt; cbn [inst_peer subInst];
              apply twoPeers_right).
        unfold linkEdges; rewrite Hpr.
        unfold depsOfL; f_equal; apply map_ext_in; intros r Hr.
        rewrite (linkCands_agree I _ _ _ (k, v) (m, u) r
                   (twoDeps_left I (snd k, v) (snd m, u))
                   (twoPeers_left I (snd k, v) (snd m, u))
                   (twoDeps_right I (snd k, v) (snd m, u))
                   (twoPeers_right I (snd k, v) (snd m, u))); [reflexivity | |].
        - apply slotKey_in.
          + apply NSet.union_spec; right; apply NSet.union_spec; left.
            unfold peerNames; apply mem_namesOfL.
            exists r; split; [exact Hr | reflexivity].
          + intros d Hd; apply NSet.union_spec; left; apply slotTargets_spec; exact Hd.
        - intros d Hd; apply NSet.union_spec; right; apply NSet.union_spec; right.
          apply slotTargets_spec; exact Hd.
      Qed.

      Theorem dependees_lookupIntermediate : forall I k v m u,
          dependees (peerSubInst I (snd k, v) m u)
            (Nm.Intermediate k v m, Vs.Orig u) =
          dependees I (Nm.Intermediate k v m, Vs.Orig u).
      Proof.
        intros I k v m u; cbn [dependees]; f_equal; f_equal;
          [apply linkEdges_agree | f_equal].
        - unfold peerSubInst, ownSight.
          pose proof (twoDeps_left I (snd k, v) (snd m, u)) as Hd.
          pose proof (twoPeers_left I (snd k, v) (snd m, u)) as Hp.
          rewrite (dp_agree I _ _ _ (k, v) (fst m) Hd
                     (chains_agree I _ _ _ (k, v) (fst m) Hp)).
          unfold plainKey, base; cbn [fst snd].
          rewrite (slotKey_agree I _ _ _ (snd k, v) (fst m) Hd).
          reflexivity.
        - unfold peerSubInst, descEdges, base; cbn [fst snd].
          rewrite (slotOf_agree I _ _ _ (snd k, v) (fst m)
                     (twoDeps_left I (snd k, v) (snd m, u))).
          reflexivity.
      Qed.

      Definition holderSubInst (I : Inst) (p c : RPkg.t) : Inst :=
        subInst I (slotTargets I c) (twoDeps I p c) (twoPeers I p c).

      Theorem dependees_lookupLink : forall I k v m u a x,
          dependees (holderSubInst I (snd k, v) (snd m, u)) (Nm.Link k v m u a, x) =
          dependees I (Nm.Link k v m u a, x).
      Proof.
        intros I k v m u a x; unfold holderSubInst.
        pose proof (twoDeps_left I (snd k, v) (snd m, u)) as Hd.
        pose proof (twoPeers_left I (snd k, v) (snd m, u)) as Hp.
        pose proof (twoDeps_right I (snd k, v) (snd m, u)) as Hdc.
        pose proof (twoPeers_right I (snd k, v) (snd m, u)) as Hpc.
        cbn [dependees]; unfold sightSet, holderEdges, dpEdges, plainKey.
        rewrite (chains_agree I _ _ _ (k, v) a Hp),
          (holds_agree I _ _ _ (k, v) a Hd),
          (dp_agree I _ _ _ (m, u) a Hdc (chains_agree I _ _ _ (m, u) a Hpc)).
        unfold base; cbn [fst snd].
        rewrite (slotKey_agree I _ _ _ (snd k, v) a Hd),
          (slotKey_agree I _ _ _ (snd m, u) a Hdc),
          (slotCands_agree I _ _ _ (snd m, u) Hdc
             (fun d Hdr => slotTargets_spec I (snd m, u) d Hdr) a).
        reflexivity.
      Qed.

      Theorem dependees_lookupSight : forall I k v a x,
          dependees I (Nm.Sight k v a, x) = T.DependeesSet.empty.
      Proof. intros I k v a x; reflexivity. Qed.

      Theorem dependees_lookupDesc : forall I a t s x,
          dependees I (Nm.Desc a t s, x) = T.DependeesSet.empty.
      Proof. intros I a t s x; reflexivity. Qed.

    End Lookup.

    Theorem npmResolution_coreResolution : forall I S pi sg,
        npmResolution (coreResolution I S pi sg) = S.
    Proof.
      intros I S pi sg; apply PkgSet.ext; intros [k v].
      rewrite mem_npmResolution, mem_coreResolution.
      unfold embedPkg; cbn [fst snd]; split.
      - intros [[k' [v' [Hp He]]] |
                [[p [m [u [_ [_ [_ [_ He]]]]]]] |
                 [[c [a [_ [_ He]]]] |
                  [[p [m [u [a [_ [_ [_ [_ [_ He]]]]]]]]] |
                   [[p [m [_ [_ [_ [_ He]]]]]] |
                    [p [m [u [d [_ [_ [_ [_ [_ [_ [e [_ He]]]]]]]]]]]]]]]]];
          try discriminate He.
        injection He as E1 E2 E3; subst; exact Hp.
      - intro Hp; left; exists k, v; split; [exact Hp | reflexivity].
    Qed.

    Theorem npmParents_coreResolution : forall I S pi sg,
        IsResolution I S pi sg ->
        npmParents (coreResolution I S pi sg) = pi.
    Proof.
      intros I S pi sg Hres.
      apply Conc.ParentRel.ext; intros [[m u] [k v]].
      rewrite mem_npmParents, !mem_coreResolution; cbn [fst snd]; split.
      - intros [[[k' [v' [_ He]]] |
                 [[[pk pv] [m' [u' [_ [_ [_ [Hi He]]]]]]] |
                  [[c [a [_ [_ He]]]] |
                   [[p [m' [u' [a [_ [_ [_ [_ [_ He]]]]]]]]] |
                    [[p [m' [_ [_ [_ [_ He]]]]]] |
                     [p [m' [u' [d [_ [_ [_ [_ [_ [_ [e [_ He]]]]]]]]]]]]]]]]] _];
          try discriminate He.
        cbn [fst snd] in He.
        injection He as E1 E2 E3 E4; subst; exact (proj2 Hi).
      - intro Hcq; destruct (res_parents _ _ _ _ Hres _ _ Hcq)
          as [Hc [Hq Hk]].
        split.
        + right; left; exists (k, v), m, u.
          split; [exact Hq |]; split; [exact Hk |].
          split; [apply mem_realVersions;
                  exact (proj2 (res_subset _ _ _ _ Hres _ Hc)) |].
          split; [exact (conj Hc Hcq) | reflexivity].
        + left; exists k, v; split; [exact Hq | reflexivity].
    Qed.

  End Reduction.
End Npm.
