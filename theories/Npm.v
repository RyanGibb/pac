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
  Module PkgF := UOTCompareFacts Pkg.
  Module KVKF := UOTCompareFacts KVK.
  Module KVNF := UOTCompareFacts KVN.
  Module KVKVNF := UOTCompareFacts KVKVN.
  Module VF := UOTCompareFacts V.
  #[local] Hint Rewrite PkgF.compare_eq_iff KVKF.compare_eq_iff
    KVNF.compare_eq_iff KVKVNF.compare_eq_iff VF.compare_eq_iff : cmp_npm.
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

  (* The Concurrent Reduction's names and versions, widened: a peer's
     version has to reach the copies below its declarer, which one name per
     copy and peer name (its sight) and one per holder of that copy (a link)
     carry, and Bot is a sight or link that answers for nothing. *)
  Module Nm.
    Inductive name : Type :=
    | Granular (k : NKey.t) (w : V.t)
    | Intermediate (k : NKey.t) (v : V.t) (m : NKey.t)
    | Sight (k : NKey.t) (v : V.t) (a : N.t)
    | Link (k : NKey.t) (v : V.t) (m : NKey.t) (u : V.t) (a : N.t).
    Definition t := name.

    Definition rank (x : t) : nat :=
      match x with
      | Granular _ _ => 0 | Intermediate _ _ _ => 1
      | Sight _ _ _ => 2 | Link _ _ _ _ _ => 3
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
    | Bot.
    Definition t := version.

    Definition rank (x : t) : nat :=
      match x with Orig _ => 0 | Bot => 1 end.

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
    ; d_dev : bool }.

  Record PeerDependency : Type := MkPeer
    { p_name : N.t
    ; p_range : Range
    ; p_optional : bool }.

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

  Lemma peerCandsAt_real : forall I p r w,
      VSet.In w (peerCandsAt I p r) ->
      VSet.In w (realVersions (inst_repo I) (snd (slotKey I p (p_name r)))).
  Proof.
    intros I p r w Hw; unfold peerCandsAt in Hw; apply mem_rangeEval in Hw.
    exact (proj1 Hw).
  Qed.

  Definition peerActive (I : Inst) (p : RPkg.t) (r : PeerDependency) : bool :=
    orb (negb (p_optional r)) (NSet.mem (p_name r) (dirs I p)).

  Definition activePeers (I : Inst) (p : RPkg.t) (q : RPkg.t)
    : list PeerDependency :=
    List.filter (peerActive I p) (peerDependenciesAt I q).

  Definition peerDirs (I : Inst) : NSet.t :=
    namesOfL (fun q => p_name (snd q)) (inst_peer I).

  Lemma peerDirs_peer : forall I q r,
      In (q, r) (inst_peer I) -> NSet.In (p_name r) (peerDirs I).
  Proof.
    intros I q r Hr; unfold peerDirs; apply mem_namesOfL.
    exists (q, r); split; [exact Hr | reflexivity].
  Qed.

  Definition childDirs (I : Inst) (p : RPkg.t) : NSet.t :=
    NSet.union (dirs I p) (peerDirs I).

  Definition childKeys (I : Inst) (p : RPkg.t) : KeySet.t :=
    SOnk.map (slotKey I p) (childDirs I p).

  Lemma slotKey_plain : forall I p a,
      ~ NSet.In a (dirs I p) -> slotKey I p a = (a, a).
  Proof.
    intros I p a Ha; unfold slotKey.
    destruct (slotOf I p a) as [d |] eqn:Hd; [| reflexivity].
    exfalso; apply Ha; unfold dirs; apply mem_namesOfL.
    destruct (findDepL_some _ _ _ Hd) as [Hin Hdir].
    exists d; split; assumption.
  Qed.

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

  (* arborist's PEER LOCAL (edge.js): a peer may not resolve into its own
     declarer's node_modules unless the declarer is the root, so a copy that
     peers on a holds nothing there, and what it shows at a is what its own
     peer sees *)
  Definition chains (I : Inst) (q : Pkg.t) (a : N.t) : bool :=
    andb (negb (PkgEqb.eqb q (rootPkg I))) (NSet.mem a (peerNames I (base q))).

  Definition childCands (I : Inst) (q : Pkg.t)
      (m : NKey.t) : VSet.t :=
    if KeyEqb.eqb m (slotKey I (base q) (fst m))
    then if chains I q (fst m) then VSet.empty
         else if NSet.mem (fst m) (dirs I (base q))
         then slotCands I (base q) (fst m)
         else if NSet.mem (fst m) (peerDirs I)
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

  (* The version q shows a copy it holds at a: its own copy there, or,
     where it chains, what its sight holds. *)
  Definition Shows (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (sg : Pkg.t -> N.t -> option V.t) (q : Pkg.t) (a : N.t) (w : V.t)
    : Prop :=
    if chains I q a then sg q a = Some w
    else Installs S pi q (slotKey I (base q) a) w.

  Definition InPeerRanges (I : Inst) (q : Pkg.t) (c : RPkg.t) (a : N.t)
      (w : V.t) : Prop :=
    forall r, In (c, r) (inst_peer I) -> p_name r = a ->
      VSet.In w (peerCandsAt I (base q) r).

  Record IsResolution (I : Inst)
      (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (sg : Pkg.t -> N.t -> option V.t) : Prop :=
    { res_subset : forall q, PkgSet.In q S -> Available I q
    ; res_root : PkgSet.In (rootPkg I) S
    ; res_unique :
        forall p m v v', Installs S pi p m v -> Installs S pi p m v' -> v = v'
    ; res_slot :
        forall p, PkgSet.In p S ->
        forall a, NSet.In a (dirs I (base p)) ->
        exists v, VSet.In v (slotCands I (base p) a) /\
          Installs S pi p (slotKey I (base p) a) v
    ; res_peer_local :
        forall q, PkgSet.In q S ->
        forall a, chains I q a = true ->
        forall w, ~ Installs S pi q (slotKey I (base q) a) w
    ; res_peer_sight :
        forall q, PkgSet.In q S ->
        forall m u, Installs S pi q m u ->
        forall a w, NSet.In a (peerNames I (snd m, u)) ->
          sg (m, u) a = Some w ->
          Shows I S pi sg q a w /\ slotKey I (base q) a = (a, a) /\
          InPeerRanges I q (snd m, u) a w
    ; res_peer_reach :
        forall q, PkgSet.In q S ->
        forall m u, Installs S pi q m u ->
        forall r, In ((snd m, u), r) (inst_peer I) ->
          peerActive I (base q) r = true ->
        exists w, Shows I S pi sg q (p_name r) w /\
          InPeerRanges I q (snd m, u) (p_name r) w
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
          KeySet.In (fst c) (childKeys I (base q)) }.

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

    Definition versions (I : Inst) (n : Nm.t) : T.VSet.t :=
      match n with
      | Nm.Granular k w =>
          if PkgSet.mem (k, w) (realPkgs I)
          then T.VSet.singleton (Vs.Orig w)
          else T.VSet.empty
      | Nm.Intermediate k v m => embedVS (childCands I (k, v) m)
      | Nm.Sight _ _ a =>
          T.VSet.add Vs.Bot (embedVS (realVersions (inst_repo I) a))
      | Nm.Link k v _ _ a =>
          T.VSet.add Vs.Bot
            (embedVS (realVersions (inst_repo I)
                        (snd (slotKey I (snd k, v) a))))
      end.

    Lemma childCands_chains : forall I q m,
        chains I q (fst m) = true -> childCands I q m = VSet.empty.
    Proof.
      intros I q m H; unfold childCands; rewrite H.
      destruct (KeyEqb.eqb m (slotKey I (base q) (fst m))); reflexivity.
    Qed.

    Definition entryEdges (I : Inst) (q : Pkg.t)
      : T.DependeesSet.t :=
      depsOfL (fun a =>
          (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
           embedVS (slotCands I (base q) a)))
        (NSet.elements (dirs I (base q))).

    Definition rootPeerEdges (I : Inst) (q : Pkg.t)
      : T.DependeesSet.t :=
      if PkgEqb.eqb q (rootPkg I)
      then depsOfL (fun r =>
               (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
                embedVS (peerCandsAt I (base q) r)))
             (activePeers I (base q) (base q))
      else T.DependeesSet.empty.

    (* Bot only where the peer asks nothing of what q shows, which is
       npm's legacy reading kept for an optional peer q has no directory
       for. *)
    Definition linkCands (I : Inst) (q : Pkg.t) (r : PeerDependency)
      : T.VSet.t :=
      if peerActive I (base q) r
      then embedVS (peerCandsAt I (base q) r)
      else T.VSet.add Vs.Bot (embedVS (peerCandsAt I (base q) r)).

    Definition linkEdges (I : Inst) (q : Pkg.t) (m : NKey.t) (u : V.t)
      : T.DependeesSet.t :=
      depsOfL (fun r =>
          (Nm.Link (fst q) (snd q) m u (p_name r), linkCands I q r))
        (peerDependenciesAt I (snd m, u)).

    Definition plainKey (I : Inst) (p : RPkg.t) (a : N.t) : bool :=
      KeyEqb.eqb (slotKey I p a) (a, a).

    (* A copy's sight is shared by all its holders, which may show different
       versions, so a link only fixes the sight or leaves it Bot, and a
       dependency of the copy that reads it is what forces it.  It is a
       version of a itself, so a holder's aliased copy cannot fill it. *)
    Definition sightSet (I : Inst) (q : Pkg.t) (a : N.t) (x : Vs.t)
      : T.VSet.t :=
      match x with
      | Vs.Orig w =>
          if plainKey I (base q) a
          then T.VSet.add (Vs.Orig w) (T.VSet.singleton Vs.Bot)
          else T.VSet.singleton Vs.Bot
      | Vs.Bot => T.VSet.singleton Vs.Bot
      end.

    Definition holderEdge (I : Inst) (q : Pkg.t) (a : N.t) (w : V.t)
      : T.Dependees.t :=
      (if chains I q a
       then Nm.Sight (fst q) (snd q) a
       else Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
       T.VSet.singleton (Vs.Orig w)).

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
            (linkEdges I (k, v) m u)
      | (Nm.Link k v m u a, x) =>
          T.DependeesSet.add (Nm.Sight m u a, sightSet I (k, v) a x)
            (match x with
             | Vs.Orig w => T.DependeesSet.singleton (holderEdge I (k, v) a w)
             | Vs.Bot => T.DependeesSet.empty
             end)
      | _ => T.DependeesSet.empty
      end.

    Lemma mem_entryEdges : forall I q h,
        T.DependeesSet.In h (entryEdges I q) <->
        exists a, NSet.In a (dirs I (base q)) /\
          h = (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
               embedVS (slotCands I (base q) a)).
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
          h = (Nm.Link (fst q) (snd q) m u (p_name r), linkCands I q r).
    Proof.
      intros I q m u h; unfold linkEdges, peerDependenciesAt.
      rewrite mem_depsOfL; split; intros [r [Hr He]]; exists r;
        (split; [apply in_ownedBy; exact Hr | symmetry; exact He]).
    Qed.

    Lemma mem_linkCands : forall I q r x,
        T.VSet.In x (linkCands I q r) <->
        (x = Vs.Bot /\ peerActive I (base q) r = false) \/
        exists w, VSet.In w (peerCandsAt I (base q) r) /\ x = Vs.Orig w.
    Proof.
      intros I q r x; unfold linkCands.
      destruct (peerActive I (base q) r);
        rewrite ?T.VSet.add_spec, mem_embedVS; split.
      - intro H; right; exact H.
      - intros [[_ E] | H]; [discriminate E | exact H].
      - intros [E | H]; [left; split; [exact E | reflexivity] | right; exact H].
      - intros [[E _] | H]; [left; exact E | right; exact H].
    Qed.

    Lemma mem_sightSet : forall I q a x y,
        T.VSet.In y (sightSet I q a x) <->
        y = Vs.Bot \/
        (y = x /\ x <> Vs.Bot /\ slotKey I (base q) a = (a, a)).
    Proof.
      intros I q a x y; unfold sightSet, plainKey.
      destruct x as [w |].
      - destruct (KeyEqb.eqb (slotKey I (base q) a) (a, a)) eqn:Hp.
        + apply KeyEqb.eqb_true_iff in Hp.
          rewrite T.VSet.add_spec, T.VSet.singleton_spec; split.
          * intros [E | E]; [right; split; [exact E | split; [discriminate | exact Hp]]
                            | left; exact E].
          * intros [E | [E _]]; [right; exact E | left; exact E].
        + rewrite T.VSet.singleton_spec; split; [intro E; left; exact E |].
          intros [E | [_ [_ E]]]; [exact E |].
          rewrite E, KeyEqb.eqb_refl in Hp; discriminate Hp.
      - rewrite T.VSet.singleton_spec; split; [intro E; left; exact E |].
        intros [E | [_ [E _]]]; [exact E | contradiction E; reflexivity].
    Qed.

    Lemma dependees_link : forall I k v m u a x h,
        T.DependeesSet.In h (dependees I (Nm.Link k v m u a, x)) <->
        h = (Nm.Sight m u a, sightSet I (k, v) a x) \/
        exists w, x = Vs.Orig w /\ h = holderEdge I (k, v) a w.
    Proof.
      intros I k v m u a x h; cbn [dependees].
      rewrite SOhh.add_in; destruct x as [w |].
      - rewrite SOhh.singleton_in; split.
        + intros [E | E]; [left; exact E | right; exists w; split; [reflexivity | exact E]].
        + intros [E | [w' [E1 E2]]]; [left; exact E |].
          injection E1 as <-; right; exact E2.
      - split.
        + intros [E | E]; [left; exact E | destruct (SOhh.empty_in _ E)].
        + intros [E | [w' [E _]]]; [left; exact E | discriminate E].
    Qed.

    Definition targetNames (I : Inst) : NmSet.t :=
      NmSet.union
        (SOpn.map (fun q => Nm.Granular (fst q) (snd q)) (realPkgs I))
        (NmSet.union
           (SOpn.unionMap (fun q =>
                SOnm.map (fun m => Nm.Intermediate (fst q) (snd q) m)
                  (childKeys I (base q)))
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
                     (childKeys I (base q)))
                 (realPkgs I)))).

    Definition TargetName (I : Inst) (n : Nm.t) : Prop :=
      match n with
      | Nm.Granular k w => PkgSet.In (k, w) (realPkgs I)
      | Nm.Intermediate k v m =>
          PkgSet.In (k, v) (realPkgs I) /\ KeySet.In m (childKeys I (snd k, v))
      | Nm.Sight k v a =>
          PkgSet.In (k, v) (realPkgs I) /\ NSet.In a (peerNames I (snd k, v))
      | Nm.Link k v m u a =>
          PkgSet.In (k, v) (realPkgs I) /\ KeySet.In m (childKeys I (snd k, v)) /\
          VSet.In u (realVersions (inst_repo I) (snd m)) /\
          NSet.In a (peerNames I (snd m, u))
      end.

    Lemma mem_targetNames : forall I n,
        NmSet.In n (targetNames I) <-> TargetName I n.
    Proof.
      intros I n; unfold targetNames.
      rewrite !NmSet.union_spec, SOpn.mem_map, !SOpn.mem_unionMap.
      setoid_rewrite SOnm.mem_map; setoid_rewrite SOam.mem_map.
      setoid_rewrite SOnm.mem_unionMap; setoid_rewrite SOvm.mem_unionMap.
      setoid_rewrite SOam.mem_map.
      destruct n as [k w | k v m | k v a | k v m u a]; cbn [TargetName]; split.
      - intros [[[k' w'] [Hq E]] | [[q [_ [m [_ E]]]] |
                 [[q [_ [a [_ E]]]] | [q [_ [m [_ [u [_ [a [_ E]]]]]]]]]]];
          try discriminate E.
        cbn [fst snd] in E; injection E as -> ->; exact Hq.
      - intro H; left; exists (k, w); split; [exact H | reflexivity].
      - intros [[q [_ E]] | [[[k' v'] [Hq [m' [Hm E]]]] |
                 [[q [_ [a [_ E]]]] | [q [_ [m' [_ [u [_ [a [_ E]]]]]]]]]]];
          try discriminate E.
        cbn [fst snd] in E; injection E as -> -> ->; split; assumption.
      - intros [Hq Hm]; right; left; exists (k, v); split; [exact Hq |].
        exists m; split; [exact Hm | reflexivity].
      - intros [[q [_ E]] | [[q [_ [m' [_ E]]]] |
                 [[[k' v'] [Hq [a' [Ha E]]]] |
                  [q [_ [m' [_ [u [_ [a' [_ E]]]]]]]]]]];
          try discriminate E.
        cbn [fst snd] in E; injection E as -> -> ->; split; assumption.
      - intros [Hq Ha]; right; right; left; exists (k, v); split; [exact Hq |].
        exists a; split; [exact Ha | reflexivity].
      - intros [[q [_ E]] | [[q [_ [m' [_ E]]]] |
                 [[q [_ [a' [_ E]]]] |
                  [[k' v'] [Hq [m' [Hm [u' [Hu [a' [Ha E]]]]]]]]]]];
          try discriminate E.
        cbn [fst snd] in E; injection E as -> -> -> -> ->.
        repeat split; assumption.
      - intros [Hq [Hm [Hu Ha]]]; right; right; right; exists (k, v).
        split; [exact Hq |]; exists m; split; [exact Hm |].
        exists u; split; [exact Hu |]; exists a; split; [exact Ha | reflexivity].
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
      - intros [[k w | k v m | k v a | k v m u a] [x |]] [k' v'] H;
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
      - intros [[n x] [Hs He]]; destruct n as [k' w | k' v' m' | | ];
          destruct x as [u' |]; try discriminate He.
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
      intros c a [[k w | k v m | k v b | k v m u b] [x |]]; cbn [isSightOf];
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

    Lemma entry_selected : forall I S q a,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (embedPkg q) S ->
        NSet.In a (dirs I (base q)) ->
        exists v, VSet.In v (slotCands I (base q) a) /\
          T.PkgSet.In
            (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
             Vs.Orig v) S.
    Proof.
      intros I S q a Hres Hq Ha.
      destruct (dep_met I S _
                  (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
                   embedVS (slotCands I (base q) a)) Hres Hq)
        as [x [Hx HxS]].
      { rewrite dependees_embedPkg.
        apply T.DependeesSet.union_spec; left; apply mem_entryEdges.
        exists a; split; [exact Ha | reflexivity]. }
      apply mem_embedVS in Hx; destruct Hx as [v [Hv ->]].
      exists v; split; assumption.
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
        exists x, T.VSet.In x (linkCands I q r) /\
          T.PkgSet.In (Nm.Link (fst q) (snd q) m u (p_name r), x) S.
    Proof.
      intros I S [k v] m u r Hres Hin Hr.
      destruct (dep_met I S _
                  (Nm.Link k v m u (p_name r), linkCands I (k, v) r) Hres Hin)
        as [x [Hx HxS]].
      { cbn [dependees fst snd]; apply SOhh.add_in; right.
        apply mem_linkEdges; exists r; split; [exact Hr | reflexivity]. }
      exists x; split; assumption.
    Qed.

    Lemma link_ranges : forall I S q m u a w,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S ->
        T.PkgSet.In (Nm.Link (fst q) (snd q) m u a, Vs.Orig w) S ->
        InPeerRanges I q (snd m, u) a w.
    Proof.
      intros I S q m u a w Hres Hin Hl r Hr Hn; subst a.
      destruct (link_selected I S q m u r Hres Hin Hr) as [x [Hx HxS]].
      rewrite (T.res_version_unique _ _ _ _ Hres _ _ _ HxS Hl) in Hx.
      apply mem_linkCands in Hx.
      destruct Hx as [[E _] | [w' [Hw' E]]]; [discriminate E |].
      injection E as ->; exact Hw'.
    Qed.

    Lemma link_sight : forall I S k v m u a x,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (Nm.Link k v m u a, x) S ->
        exists y, T.VSet.In y (sightSet I (k, v) a x) /\
          T.PkgSet.In (Nm.Sight m u a, y) S.
    Proof.
      intros I S k v m u a x Hres Hl.
      destruct (dep_met I S _ (Nm.Sight m u a, sightSet I (k, v) a x) Hres Hl)
        as [y [Hy HyS]].
      { apply dependees_link; left; reflexivity. }
      exists y; split; assumption.
    Qed.

    Lemma link_shows : forall I S q m u a w,
        T.IsResolution (reduceReal I) (reduceDeps I) (embedRoot I) S ->
        T.PkgSet.In (embedPkg q) S ->
        T.PkgSet.In (Nm.Link (fst q) (snd q) m u a, Vs.Orig w) S ->
        Shows I (npmResolution S) (npmParents S) (npmSight S) q a w.
    Proof.
      intros I S [k v] m u a w Hres Hq Hl; cbn [fst snd] in Hl.
      destruct (dep_met I S _ (holderEdge I (k, v) a w) Hres Hl) as [x [Hx HxS]].
      { apply dependees_link; right; exists w; split; reflexivity. }
      unfold holderEdge in Hx, HxS; cbn [fst snd] in Hx, HxS.
      apply T.VSet.singleton_spec in Hx; subst x.
      unfold Shows; destruct (chains I (k, v) a).
      - apply npmSight_in; [exact (T.res_version_unique _ _ _ _ Hres) | exact HxS].
      - split.
        + apply mem_npmResolution; exact (exit_selected I S k v _ w Hres HxS).
        + apply mem_npmParents; cbn [fst snd]; split; assumption.
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
      - intros p Hp a Ha; apply mem_npmResolution in Hp.
        destruct (entry_selected I S p a Hres Hp Ha) as [v [Hv Hi]].
        exists v; split; [exact Hv | exact (Hpi p _ v Hp Hi)].
      - intros [k v] Hq a Hch w Hi; apply Hint in Hi.
        apply Hsub, mem_reduceReal in Hi; destruct Hi as [_ Hw].
        cbn [versions fst snd] in Hw; apply orig_embedVS in Hw.
        apply (SOrv.empty_in w).
        rewrite <- (childCands_chains I (k, v)
                      (slotKey I (base (k, v)) a));
          [exact Hw | rewrite slotKey_fst; exact Hch].
      - intros q Hq m u Hmu a w Ha Hsg.
        apply mem_npmResolution in Hq; apply Hint in Hmu.
        apply mem_peerNames in Ha; destruct Ha as [r [Hr Hn]].
        apply npmSight_some in Hsg; cbn [fst snd] in Hsg.
        destruct (link_selected I S q m u r Hres Hmu Hr) as [x [_ Hl]].
        rewrite Hn in Hl.
        destruct q as [k v]; cbn [fst snd] in Hl, Hmu.
        destruct (link_sight I S k v m u a x Hres Hl) as [y [Hy HyS]].
        rewrite (Huniq _ _ _ HyS Hsg) in Hy.
        apply mem_sightSet in Hy.
        destruct Hy as [E | [E [_ Hplain]]]; [discriminate E | subst x].
        split; [exact (link_shows I S (k, v) m u a w Hres Hq Hl) |].
        split; [exact Hplain |].
        exact (link_ranges I S (k, v) m u a w Hres Hmu Hl).
      - intros q Hq m u Hmu r Hr Hact.
        apply mem_npmResolution in Hq; apply Hint in Hmu.
        destruct (link_selected I S q m u r Hres Hmu Hr) as [x [Hx Hl]].
        apply mem_linkCands in Hx.
        destruct Hx as [[_ E] | [w [_ ->]]];
          [rewrite Hact in E; discriminate E |].
        exists w; split.
        + exact (link_shows I S q m u _ w Hres Hq Hl).
        + exact (link_ranges I S q m u _ w Hres Hmu Hl).
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
        exists w,
          PkgSet.In (peerKeyAt I (snd k, v) r, w) (npmResolution S) /\
          Conc.ParentRel.In
            ((peerKeyAt I (snd k, v) r, w), (k, v)) (npmParents S) /\
          VSet.In w (peerCandsAt I (snd k, v) r).
    Proof.
      intros I S Hres k v m u Hq Hi r Hr Hopt Hch.
      pose proof (npm_soundness I S Hres) as Hsrc.
      assert (Hp : PkgSet.In (k, v) (npmResolution S))
        by (apply mem_npmResolution; exact Hq).
      assert (HI : Installs (npmResolution S) (npmParents S) (k, v) m u).
      { split.
        - apply mem_npmResolution; exact (exit_selected I S k v m u Hres Hi).
        - apply mem_npmParents; cbn [fst snd]; split; assumption. }
      assert (Hact : peerActive I (base (k, v)) r = true)
        by (unfold peerActive; rewrite Hopt; reflexivity).
      destruct (res_peer_reach _ _ _ _ Hsrc (k, v) Hp m u HI r Hr Hact)
        as [w [Hw Hrg]].
      unfold Shows in Hw; rewrite Hch in Hw.
      exists w; split; [exact (proj1 Hw) | split; [exact (proj2 Hw) |]].
      exact (Hrg r Hr eq_refl).
    Qed.

    Lemma slotKey_childKeys : forall I p a,
        NSet.In a (childDirs I p) -> KeySet.In (slotKey I p a) (childKeys I p).
    Proof.
      intros I p a Ha; unfold childKeys; apply SOnk.mem_map.
      exists a; split; [exact Ha | reflexivity].
    Qed.

    Lemma peerKeyAt_childKeys : forall I p q r,
        In (q, r) (inst_peer I) -> KeySet.In (peerKeyAt I p r) (childKeys I p).
    Proof.
      intros I p q r Hr; apply slotKey_childKeys.
      apply NSet.union_spec; right; exact (peerDirs_peer I q r Hr).
    Qed.

    Lemma slotKey_keysOf : forall I p a,
        NSet.In a (dirs I p) \/ NSet.In a (peerDirs I) ->
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
        destruct Ha as [Ha | Ha].
        + exfalso; unfold dirs in Ha; apply mem_namesOfL in Ha.
          destruct Ha as [d [Hin Hdir]].
          exact (findDepL_none _ _ Hd d Hin Hdir).
        + unfold peerDirs in Ha; apply mem_namesOfL in Ha.
          destruct Ha as [[q r] [Hr Hn]]; exists (q, r); split; [exact Hr |].
          cbn [snd] in Hn |- *; rewrite Hn; reflexivity.
    Qed.

    Lemma childKeys_keysOf : forall I p m,
        KeySet.In m (childKeys I p) -> KeySet.In m (keysOf I).
    Proof.
      intros I p m H; unfold childKeys in H; apply SOnk.mem_map in H.
      destruct H as [a [Ha ->]]; apply slotKey_keysOf.
      unfold childDirs in Ha; apply NSet.union_spec in Ha; exact Ha.
    Qed.

    Lemma childCands_real : forall I q m u,
        VSet.In u (childCands I q m) -> PkgSet.In (m, u) (realPkgs I).
    Proof.
      intros I q m u Hu; unfold childCands in Hu.
      apply SOrv.in_if_empty in Hu as [Hk Hu]; apply KeyEqb.eqb_true_iff in Hk.
      destruct (chains I q (fst m)); [destruct (SOrv.empty_in _ Hu) |].
      apply mem_realPkgs; unfold Available, base; cbn [fst snd].
      destruct (NSet.mem (fst m) (dirs I (base q))) eqn:Hd.
      - apply NSet.mem_spec in Hd.
        split; [rewrite Hk; apply slotKey_keysOf; left; exact Hd |].
        pose proof (slotCands_real I _ _ u Hu) as Hr.
        rewrite <- Hk in Hr; exact Hr.
      - apply SOrv.in_if_empty in Hu as [Hp Hu].
        apply NSet.mem_spec in Hp.
        split; [rewrite Hk; apply slotKey_keysOf; right; exact Hp |].
        apply mem_realVersions; exact Hu.
    Qed.

    Lemma installs_childCands : forall I S pi sg p m v,
        IsResolution I S pi sg -> PkgSet.In p S ->
        KeySet.In m (childKeys I (base p)) ->
        Installs S pi p m v ->
        VSet.In v (childCands I p m).
    Proof.
      intros I S pi sg p m v Hres Hp Hm Hi.
      unfold childKeys in Hm; apply SOnk.mem_map in Hm.
      destruct Hm as [a [Ha ->]].
      unfold childCands; rewrite slotKey_fst, KeyEqb.eqb_refl.
      destruct (chains I p a) eqn:Hch.
      { exfalso; exact (res_peer_local _ _ _ _ Hres p Hp a Hch v Hi). }
      destruct (NSet.mem a (dirs I (base p))) eqn:Hsa.
      - apply NSet.mem_spec in Hsa.
        destruct (res_slot _ _ _ _ Hres p Hp a Hsa) as [v' [Hv' Hi']].
        rewrite (res_unique _ _ _ _ Hres p _ v v' Hi Hi'); exact Hv'.
      - unfold childDirs in Ha; apply NSet.union_spec in Ha.
        destruct Ha as [Ha | Ha];
          [apply NSet.mem_spec in Ha; rewrite Ha in Hsa; discriminate |].
        assert (Hpa : NSet.mem a (peerDirs I) = true)
          by (apply NSet.mem_spec; exact Ha).
        rewrite Hpa; destruct Hi as [HinS _].
        destruct (res_subset _ _ _ _ Hres _ HinS) as [_ Hb]; unfold base in Hb.
        cbn [fst snd] in Hb; apply mem_realVersions; exact Hb.
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
                  (p_name r) Hdir) as [w [_ Hi]].
      rewrite base_rootPkg in Hi.
      exists w; unfold peerKeyAt; split;
        [exact (res_root_peer_match _ _ _ _ Hres r Hr Hopt Hact w Hi)
        | exact Hi].
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

    Definition showsAt (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (sg : Pkg.t -> N.t -> option V.t) (q : Pkg.t) (a : N.t)
      : option V.t :=
      if chains I q a then sg q a
      else ownAt I S pi q (slotKey I (base q) a).

    Lemma shows_showsAt : forall I S pi sg q a w,
        IsResolution I S pi sg ->
        Shows I S pi sg q a w -> showsAt I S pi sg q a = Some w.
    Proof.
      intros I S pi sg q a w Hres; unfold Shows, showsAt.
      destruct (chains I q a); [exact (fun H => H) |].
      intro Hi; unfold ownAt.
      destruct (List.find (installsb S pi q (slotKey I (base q) a))
                  (VSet.elements (realVersions (inst_repo I)
                     (snd (slotKey I (base q) a))))) as [w' |] eqn:Hf.
      - apply List.find_some in Hf; destruct Hf as [_ Hb].
        apply installsb_iff in Hb.
        rewrite (res_unique _ _ _ _ Hres _ _ _ _ Hb Hi); reflexivity.
      - exfalso.
        assert (Hw : List.In w (VSet.elements (realVersions (inst_repo I)
                                  (snd (slotKey I (base q) a))))).
        { apply SOvp.elements_in, mem_realVersions.
          destruct (res_subset _ _ _ _ Hres _ (proj1 Hi)) as [_ Hb].
          exact Hb. }
        pose proof (List.find_none _ _ Hf _ Hw) as E.
        apply installsb_iff in Hi; rewrite Hi in E; discriminate E.
    Qed.

    Definition requiredb (I : Inst) (q : Pkg.t) (c : RPkg.t) (a : N.t)
      : bool :=
      existsb (fun r => andb (NEqb.eqb (p_name r) a) (peerActive I (base q) r))
        (peerDependenciesAt I c).

    Lemma requiredb_spec : forall I q c a,
        requiredb I q c a = true <->
        exists r, In (c, r) (inst_peer I) /\ p_name r = a /\
          peerActive I (base q) r = true.
    Proof.
      intros I q c a; unfold requiredb, peerDependenciesAt.
      rewrite existsb_exists; split; intros [r [Hr H]].
      - apply Bool.andb_true_iff in H; destruct H as [Hn Ha].
        apply NEqb.eqb_true_iff in Hn.
        exists r; split; [apply in_ownedBy; exact Hr | split; assumption].
      - destruct H as [Hn Ha]; exists r; split; [apply in_ownedBy; exact Hr |].
        apply Bool.andb_true_iff; split;
          [apply NEqb.eqb_true_iff; exact Hn | exact Ha].
    Qed.

    Definition sightVal (I : Inst) (sg : Pkg.t -> N.t -> option V.t)
        (c : Pkg.t) (a : N.t) : Vs.t :=
      match sg c a with
      | Some w =>
          if VSet.mem w (realVersions (inst_repo I) a) then Vs.Orig w
          else Vs.Bot
      | None => Vs.Bot
      end.

    Lemma shows_cases : forall I S pi sg q a w,
        Shows I S pi sg q a w ->
        (chains I q a = true /\ sg q a = Some w) \/
        (chains I q a = false /\ Installs S pi q (slotKey I (base q) a) w).
    Proof.
      intros I S pi sg q a w; unfold Shows.
      destruct (chains I q a); intro H; [left | right]; split;
        solve [reflexivity | exact H].
    Qed.

    Lemma holderEdge_chain : forall I q a w,
        chains I q a = true ->
        holderEdge I q a w =
        (Nm.Sight (fst q) (snd q) a, T.VSet.singleton (Vs.Orig w)).
    Proof. intros I q a w H; unfold holderEdge; rewrite H; reflexivity. Qed.

    Lemma holderEdge_own : forall I q a w,
        chains I q a = false ->
        holderEdge I q a w =
        (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
         T.VSet.singleton (Vs.Orig w)).
    Proof. intros I q a w H; unfold holderEdge; rewrite H; reflexivity. Qed.

    Lemma sightVal_none : forall I sg c a,
        sg c a = None -> sightVal I sg c a = Vs.Bot.
    Proof. intros I sg c a H; unfold sightVal; rewrite H; reflexivity. Qed.

    Lemma sightVal_some : forall I sg c a w,
        sg c a = Some w -> VSet.In w (realVersions (inst_repo I) a) ->
        sightVal I sg c a = Vs.Orig w.
    Proof.
      intros I sg c a w H Hw; unfold sightVal; rewrite H.
      apply VSet.mem_spec in Hw; rewrite Hw; reflexivity.
    Qed.

    Definition linkVal (I : Inst) (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (sg : Pkg.t -> N.t -> option V.t) (q : Pkg.t) (m : NKey.t) (u : V.t)
        (a : N.t) : Vs.t :=
      match sg (m, u) a with
      | Some w => Vs.Orig w
      | None =>
          if requiredb I q (snd m, u) a
          then match showsAt I S pi sg q a with
               | Some w => Vs.Orig w
               | None => Vs.Bot
               end
          else Vs.Bot
      end.

    Lemma linkVal_spec : forall I S pi sg p m u a,
        IsResolution I S pi sg -> PkgSet.In p S -> Installs S pi p m u ->
        NSet.In a (peerNames I (snd m, u)) ->
        (linkVal I S pi sg p m u a = Vs.Bot /\ sg (m, u) a = None /\
         forall r, In ((snd m, u), r) (inst_peer I) -> p_name r = a ->
           peerActive I (base p) r = false) \/
        (exists w, linkVal I S pi sg p m u a = Vs.Orig w /\
           Shows I S pi sg p a w /\ InPeerRanges I p (snd m, u) a w /\
           forall w', sg (m, u) a = Some w' ->
             w' = w /\ slotKey I (base p) a = (a, a)).
    Proof.
      intros I S pi sg p m u a Hres Hp Hi Ha; unfold linkVal.
      destruct (sg (m, u) a) as [w |] eqn:Hsg.
      - destruct (res_peer_sight _ _ _ _ Hres p Hp m u Hi a w Ha Hsg)
          as [Hs [Hk Hrg]].
        right; exists w; split; [reflexivity |].
        split; [exact Hs | split; [exact Hrg |]].
        intros w' E; injection E as ->; split; [reflexivity | exact Hk].
      - destruct (requiredb I p (snd m, u) a) eqn:Hreq.
        + apply requiredb_spec in Hreq; destruct Hreq as [r [Hr [Hn Hact]]].
          destruct (res_peer_reach _ _ _ _ Hres p Hp m u Hi r Hr Hact)
            as [w [Hs Hrg]].
          rewrite Hn in Hs, Hrg.
          rewrite (shows_showsAt I S pi sg p a w Hres Hs).
          right; exists w; split; [reflexivity |].
          split; [exact Hs | split; [exact Hrg |]].
          intros w' E; discriminate E.
        + left; split; [reflexivity | split; [reflexivity |]].
          intros r Hr Hn.
          destruct (peerActive I (base p) r) eqn:Hact; [| reflexivity].
          exfalso.
          assert (requiredb I p (snd m, u) a = true) as H
            by (apply requiredb_spec; exists r; auto).
          rewrite H in Hreq; discriminate Hreq.
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
                  (childKeys I (base p)))
              S)
           (T.PkgSet.union
              (SOpt.unionMap (fun c =>
                   SOat.map (fun a =>
                       (Nm.Sight (fst c) (snd c) a, sightVal I sg c a))
                     (peerNames I (base c)))
                 S)
              (SOpt.unionMap (fun p =>
                   SOkt.unionMap (fun m =>
                       SOvt.unionMap (fun u =>
                           if installsb S pi p m u
                           then SOat.map (fun a =>
                                    (Nm.Link (fst p) (snd p) m u a,
                                     linkVal I S pi sg p m u a))
                                  (peerNames I (snd m, u))
                           else T.PkgSet.empty)
                         (realVersions (inst_repo I) (snd m)))
                     (childKeys I (base p)))
                 S))).

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
        (exists p m u, PkgSet.In p S /\ KeySet.In m (childKeys I (base p)) /\
           VSet.In u (realVersions (inst_repo I) (snd m)) /\
           Installs S pi p m u /\
           s = (Nm.Intermediate (fst p) (snd p) m, Vs.Orig u)) \/
        (exists c a, PkgSet.In c S /\ NSet.In a (peerNames I (base c)) /\
           s = (Nm.Sight (fst c) (snd c) a, sightVal I sg c a)) \/
        (exists p m u a, PkgSet.In p S /\
           KeySet.In m (childKeys I (base p)) /\
           VSet.In u (realVersions (inst_repo I) (snd m)) /\
           Installs S pi p m u /\ NSet.In a (peerNames I (snd m, u)) /\
           s = (Nm.Link (fst p) (snd p) m u a, linkVal I S pi sg p m u a)).
    Proof.
      intros I S pi sg s; unfold coreResolution.
      rewrite !T.PkgSet.union_spec, embedSet_gran; split.
      - intros [H | [H | [H | H]]].
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
          right; right; right; exists p, m, u, a.
          exact (conj Hp (conj Hm (conj Hu (conj Hb (conj Ha eq_refl))))).
      - intros [H | [[p [m [u [Hp [Hm [Hu [Hb ->]]]]]]] |
                 [[c [a [Hc [Ha ->]]]] |
                  [p [m [u [a [Hp [Hm [Hu [Hb [Ha ->]]]]]]]]]]]].
        + left; exact H.
        + right; left; apply SOpt.mem_unionMap; exists p; split; [exact Hp |].
          apply SOkt.mem_unionMap; exists m; split; [exact Hm |].
          apply SOvt.mem_filterMap; exists u; split; [exact Hu |].
          unfold instNode; apply installsb_iff in Hb; rewrite Hb; reflexivity.
        + right; right; left; apply SOpt.mem_unionMap; exists c;
            split; [exact Hc |].
          apply SOat.mem_map; exists a; split; [exact Ha | reflexivity].
        + right; right; right; apply SOpt.mem_unionMap; exists p;
            split; [exact Hp |].
          apply SOkt.mem_unionMap; exists m; split; [exact Hm |].
          apply SOvt.mem_unionMap; exists u; split; [exact Hu |].
          apply SOat.in_if_empty; split; [apply installsb_iff; exact Hb |].
          apply SOat.mem_map; exists a; split; [exact Ha | reflexivity].
    Qed.

    Lemma versions_gran_real : forall I (k : NKey.t) (w : V.t),
        PkgSet.In (k, w) (realPkgs I) ->
        T.VSet.In (Vs.Orig w) (versions I (Nm.Granular k w)).
    Proof.
      intros I k w H; cbn [versions]; apply PkgSet.mem_spec in H.
      rewrite H; apply T.VSet.singleton_spec; reflexivity.
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
                 KeySet.In m (childKeys I (base p))).
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
                 T.PkgSet.In (Nm.Sight (fst c) (snd c) a, sightVal I sg c a)
                   (coreResolution I S pi sg)).
      { intros c a Hc Ha; apply mem_coreResolution; right; right; left.
        exists c, a; exact (conj Hc (conj Ha eq_refl)). }
      assert (HcoreL : forall p m u a, PkgSet.In p S -> Installs S pi p m u ->
                 NSet.In a (peerNames I (snd m, u)) ->
                 T.PkgSet.In (Nm.Link (fst p) (snd p) m u a,
                              linkVal I S pi sg p m u a)
                   (coreResolution I S pi sg)).
      { intros p m u a Hp Hi Ha; apply mem_coreResolution; right; right; right.
        exists p, m, u, a.
        exact (conj Hp (conj (Hck _ _ _ Hi) (conj (Hrv _ _ _ Hi)
                                              (conj Hi (conj Ha eq_refl))))). }
      assert (Hchain : forall q a, PkgSet.In q S -> chains I q a = true ->
                 slotKey I (base q) a = (a, a)).
      { intros q a Hq Hch; apply slotKey_plain; intro Hd.
        destruct (Hslot q Hq a Hd) as [w [_ Hi]].
        exact (res_peer_local _ _ _ _ Hres q Hq a Hch w Hi). }
      assert (Hrg_real : forall p c a w, NSet.In a (peerNames I c) ->
                 InPeerRanges I p c a w ->
                 VSet.In w (realVersions (inst_repo I)
                              (snd (slotKey I (base p) a)))).
      { intros p c a w Ha Hrg; apply mem_peerNames in Ha.
        destruct Ha as [r [Hr Hn]].
        pose proof (peerCandsAt_real I (base p) r w (Hrg r Hr Hn)) as H.
        rewrite Hn in H; exact H. }
      constructor.
      - intros s Hs; apply mem_coreResolution in Hs.
        destruct Hs as
          [[k [v [Hp ->]]] |
           [[[pk pv] [m [u [Hp [Hm [Hu [Hi ->]]]]]]] |
            [[[ck cv] [a [Hc [Ha ->]]]] |
             [[pk pv] [m [u [a [Hp [Hm [Hu [Hi [Ha ->]]]]]]]]]]]];
          cbn [fst snd] in *; apply mem_reduceReal; split.
        + apply mem_targetNames; exact (Hreal _ Hp).
        + exact (versions_gran_real I k v (Hreal _ Hp)).
        + apply mem_targetNames; split; [exact (Hreal _ Hp) | exact Hm].
        + cbn [versions]; apply orig_embedVS.
          exact (installs_childCands I S pi sg (pk, pv) m u Hres Hp Hm Hi).
        + apply mem_targetNames; split; [exact (Hreal _ Hc) | exact Ha].
        + cbn [versions]; unfold sightVal.
          destruct (sg (ck, cv) a) as [w |];
            [destruct (VSet.mem w (realVersions (inst_repo I) a)) eqn:Hw |];
            apply T.VSet.add_spec;
            [right; apply orig_embedVS, VSet.mem_spec; exact Hw
            | left; reflexivity | left; reflexivity].
        + apply mem_targetNames.
          split; [exact (Hreal _ Hp) | split; [exact Hm | split; [exact Hu | exact Ha]]].
        + cbn [versions]; apply T.VSet.add_spec.
          destruct (linkVal_spec I S pi sg (pk, pv) m u a Hres Hp Hi Ha)
            as [[E _] | [w [E [_ [Hrg _]]]]]; rewrite E;
            [left; reflexivity |].
          right; apply orig_embedVS.
          exact (Hrg_real (pk, pv) (snd m, u) a w Ha Hrg).
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
             [[pk pv] [m [u [a [Hp [Hm [Hu [Hi [Ha ->]]]]]]]]]]]];
          cbn [fst snd] in Hd.
        + rewrite dependees_gran in Hd.
          apply T.DependeesSet.union_spec in Hd; destruct Hd as [Hd | Hd].
          * apply mem_entryEdges in Hd; destruct Hd as [a [Ha He]].
            injection He as -> ->.
            destruct (Hslot (k, v) Hp a Ha) as [w [Hw Hi]].
            exists (Vs.Orig w); split; [apply orig_embedVS; exact Hw |].
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
        + cbn [dependees] in Hd; apply SOhh.add_in in Hd.
          destruct Hd as [He | Hd]; [injection He as -> -> |].
          * exists (Vs.Orig u); split;
              [apply T.VSet.singleton_spec; reflexivity |].
            exact (HcoreG (m, u) (proj1 Hi)).
          * apply mem_linkEdges in Hd; destruct Hd as [r [Hr He]].
            injection He as -> ->.
            assert (Ha : NSet.In (p_name r) (peerNames I (snd m, u)))
              by (apply mem_peerNames; exists r; split; [exact Hr | reflexivity]).
            exists (linkVal I S pi sg (pk, pv) m u (p_name r)); split.
            -- destruct (linkVal_spec I S pi sg (pk, pv) m u (p_name r)
                           Hres Hp Hi Ha)
                 as [[E [_ Hno]] | [w [E [_ [Hrg _]]]]];
                 rewrite E; apply mem_linkCands.
               ++ left; split; [reflexivity | exact (Hno r Hr eq_refl)].
               ++ right; exists w; split;
                    [exact (Hrg r Hr eq_refl) | reflexivity].
            -- exact (HcoreL (pk, pv) m u (p_name r) Hp Hi Ha).
        + cbn [dependees] in Hd; destruct (SOhh.empty_in _ Hd).
        + destruct (linkVal_spec I S pi sg (pk, pv) m u a Hres Hp Hi Ha)
            as [[E [Hsg _]] | [w [E [Hs [Hrg Hsg]]]]];
            rewrite E in Hd; apply dependees_link in Hd.
          * destruct Hd as [He | [w [E' _]]]; [| discriminate E'].
            injection He as -> ->.
            exists Vs.Bot; split;
              [exact (proj2 (T.VSet.singleton_spec _ _) eq_refl) |].
            rewrite <- (sightVal_none I sg (m, u) a Hsg).
            exact (HcoreS (m, u) a (proj1 Hi) Ha).
          * destruct Hd as [He | [w' [E' He]]].
            -- injection He as -> ->.
               destruct (sg (m, u) a) as [w0 |] eqn:Hsg0.
               ++ destruct (Hsg w0 Hsg0) as [-> Hplain].
                  assert (Hw : VSet.In w (realVersions (inst_repo I) a)).
                  { pose proof (Hrg_real (pk, pv) (snd m, u) a w Ha Hrg) as H.
                    rewrite Hplain in H; exact H. }
                  exists (Vs.Orig w); split.
                  ** refine (proj2 (mem_sightSet I (pk, pv) a (Vs.Orig w)
                                     (Vs.Orig w)) _).
                     right; split; [reflexivity | split; [discriminate | exact Hplain]].
                  ** rewrite <- (sightVal_some I sg (m, u) a w Hsg0 Hw).
                     exact (HcoreS (m, u) a (proj1 Hi) Ha).
               ++ exists Vs.Bot; split;
                    [exact (proj2 (mem_sightSet I (pk, pv) a (Vs.Orig w) Vs.Bot)
                              (or_introl eq_refl)) |].
                  rewrite <- (sightVal_none I sg (m, u) a Hsg0).
                  exact (HcoreS (m, u) a (proj1 Hi) Ha).
            -- injection E' as <-.
               destruct (shows_cases I S pi sg (pk, pv) a w Hs)
                 as [[Hch Hs'] | [Hch Hs']].
               ++ pose proof (eq_trans He (holderEdge_chain I (pk, pv) a w Hch))
                    as He'.
                  injection He' as -> ->.
                  exists (Vs.Orig w);
                    split; [exact (proj2 (T.VSet.singleton_spec _ _) eq_refl) |].
                  assert (Hpa : NSet.In a (peerNames I (base (pk, pv)))).
                  { unfold chains in Hch; apply Bool.andb_true_iff in Hch.
                    apply NSet.mem_spec; exact (proj2 Hch). }
                  assert (Hw : VSet.In w (realVersions (inst_repo I) a)).
                  { pose proof (Hrg_real (pk, pv) (snd m, u) a w Ha Hrg) as H.
                    rewrite (Hchain (pk, pv) a Hp Hch) in H; exact H. }
                  rewrite <- (sightVal_some I sg (pk, pv) a w Hs' Hw).
                  exact (HcoreS (pk, pv) a Hp Hpa).
               ++ pose proof (eq_trans He (holderEdge_own I (pk, pv) a w Hch))
                    as He'.
                  injection He' as -> ->.
                  exists (Vs.Orig w);
                    split; [exact (proj2 (T.VSet.singleton_spec _ _) eq_refl) |].
                  exact (HcoreI (pk, pv) _ w Hp Hs').
      - intros n x1 x2 H1 H2.
        apply mem_coreResolution in H1; apply mem_coreResolution in H2.
        destruct H1 as
          [[k1 [v1 [Hp1 He1]]] |
           [[[pk1 pv1] [m1 [u1 [Hp1 [Hm1 [Hu1 [Hi1 He1]]]]]]] |
            [[[ck1 cv1] [a1 [Hc1 [Ha1 He1]]]] |
             [[pk1 pv1] [m1 [u1 [a1 [Hp1 [Hm1 [Hu1 [Hi1 [Ha1 He1]]]]]]]]]]]];
        destruct H2 as
          [[k2 [v2 [Hp2 He2]]] |
           [[[pk2 pv2] [m2 [u2 [Hp2 [Hm2 [Hu2 [Hi2 He2]]]]]]] |
            [[[ck2 cv2] [a2 [Hc2 [Ha2 He2]]]] |
             [[pk2 pv2] [m2 [u2 [a2 [Hp2 [Hm2 [Hu2 [Hi2 [Ha2 He2]]]]]]]]]]]];
          cbn [fst snd] in He1, He2; try congruence.
        assert (pk1 = pk2) by congruence; assert (pv1 = pv2) by congruence;
          assert (m1 = m2) by congruence; subst.
        rewrite (res_unique _ _ _ _ Hres (pk2, pv2) m2 u1 u2 Hi1 Hi2) in He1.
        congruence.
    Qed.

    Theorem dependees_targetNames : forall I s h,
        T.PkgSet.In s (reduceReal I) -> T.DependeesSet.In h (dependees I s) ->
        NmSet.In (fst h) (targetNames I).
    Proof.
      intros I [n x] h Hs Hh; apply mem_reduceReal in Hs.
      destruct Hs as [Hn Hx]; apply mem_targetNames in Hn; apply mem_targetNames.
      destruct n as [k w | k v m | k v a | k v m u a]; cbn [TargetName] in Hn.
      - cbn [versions] in Hx.
        apply SOvcv.in_if_empty in Hx as [_ Hx].
        apply T.VSet.singleton_spec in Hx; subst x.
        rewrite dependees_gran in Hh; apply T.DependeesSet.union_spec in Hh.
        destruct Hh as [Hh | Hh].
        + apply mem_entryEdges in Hh; destruct Hh as [a [Ha ->]].
          cbn [fst snd TargetName]; split; [exact Hn |].
          apply slotKey_childKeys, NSet.union_spec; left; exact Ha.
        + apply mem_rootPeerEdges in Hh; destruct Hh as [_ [r [Hr [_ ->]]]].
          cbn [fst snd TargetName]; split; [exact Hn |].
          exact (peerKeyAt_childKeys I _ _ r Hr).
      - destruct Hn as [Hkv Hm].
        cbn [versions] in Hx; apply mem_embedVS in Hx.
        destruct Hx as [u [Hu ->]].
        cbn [dependees] in Hh; apply SOhh.add_in in Hh.
        destruct Hh as [-> | Hh].
        + cbn [fst TargetName]; exact (childCands_real I (k, v) m u Hu).
        + apply mem_linkEdges in Hh; destruct Hh as [r [Hr ->]].
          cbn [fst snd TargetName].
          split; [exact Hkv | split; [exact Hm | split]].
          * pose proof (childCands_real I (k, v) m u Hu) as H.
            apply mem_realPkgs in H; destruct H as [_ H].
            apply mem_realVersions; exact H.
          * apply mem_peerNames; exists r; split; [exact Hr | reflexivity].
      - cbn [dependees] in Hh; destruct (SOhh.empty_in _ Hh).
      - destruct Hn as [Hkv [Hm [Hu Ha]]].
        apply dependees_link in Hh; destruct Hh as [-> | [w [_ ->]]].
        + cbn [fst TargetName]; split; [| exact Ha].
          apply mem_realPkgs; split; [exact (childKeys_keysOf I _ m Hm) |].
          apply mem_realVersions in Hu; exact Hu.
        + unfold holderEdge; destruct (chains I (k, v) a) eqn:Hch;
            cbn [fst snd TargetName]; split; try exact Hkv.
          * unfold chains in Hch; apply Bool.andb_true_iff in Hch.
            apply NSet.mem_spec; exact (proj2 Hch).
          * apply slotKey_childKeys, NSet.union_spec; right.
            apply mem_peerNames in Ha; destruct Ha as [r [Hr <-]].
            exact (peerDirs_peer I _ r Hr).
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

      Lemma mem_peerDirs_named : forall I ns deps n,
          NSet.mem n
            (peerDirs (subInst I ns deps (peerDependenciesNamed I n))) =
          NSet.mem n (peerDirs I).
      Proof.
        intros I ns deps n; apply Bool.eq_iff_eq_true.
        rewrite !NSet.mem_spec; unfold peerDirs; cbn [inst_peer subInst].
        rewrite !mem_namesOfL; unfold peerDependenciesNamed.
        split; intros [q [Hq Hn]]; exists q; split; try exact Hn.
        - apply List.filter_In in Hq; exact (proj1 Hq).
        - apply List.filter_In; split;
            [exact Hq | apply NEqb.eqb_true_iff; exact Hn].
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
          NSet.mem (fst m) (peerDirs (subInst I ns deps prs)) =
            NSet.mem (fst m) (peerDirs I) ->
          chains (subInst I ns deps prs) q (fst m) = chains I q (fst m) ->
          childCands (subInst I ns deps prs) q m =
          childCands I q m.
      Proof.
        intros I ns deps prs q m Hd Ht Hm Hpa Hch; unfold childCands.
        rewrite (slotKey_agree I ns deps prs (base q) (fst m) Hd).
        rewrite (dirs_agree I ns deps prs (base q) Hd).
        rewrite Hpa, Hch.
        destruct (KeyEqb.eqb m (slotKey I (base q) (fst m)));
          destruct (chains I q (fst m));
          destruct (NSet.mem (fst m) (dirs I (base q)));
          destruct (NSet.mem (fst m) (peerDirs I));
          try reflexivity.
        - apply slotCands_agree; assumption.
        - apply slotCands_agree; assumption.
        - apply realVersions_subInst; exact Hm.
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
        intros I k v m; cbn [versions]; f_equal.
        unfold intSubInst; apply childCands_agree.
        - apply ownDependencies_id.
        - intros d Hd; apply NSet.add_spec; right;
            apply slotTargets_spec; exact Hd.
        - apply NSet.add_spec; left; reflexivity.
        - apply mem_peerDirs_named.
        - apply chains_named.
      Qed.

      Definition sightSubInst (I : Inst) (a : N.t) : Inst :=
        subInst I (NSet.singleton a) nil nil.

      Theorem versions_lookupSight : forall I k v a,
          versions (sightSubInst I a) (Nm.Sight k v a) =
          versions I (Nm.Sight k v a).
      Proof.
        intros I k v a; cbn [versions]; unfold sightSubInst.
        rewrite realVersions_subInst;
          [reflexivity | apply NSet.singleton_spec; reflexivity].
      Qed.

      Lemma slotKey_target : forall I p a,
          NSet.In (snd (slotKey I p a)) (NSet.add a (slotTargets I p)).
      Proof.
        intros I p a; unfold slotKey; apply NSet.add_spec.
        destruct (slotOf I p a) as [d |] eqn:Hd; cbn [snd].
        - right; apply slotTargets_spec; exact (proj1 (findDepL_some _ _ _ Hd)).
        - left; reflexivity.
      Qed.

      Definition linkSubInst (I : Inst) (p : RPkg.t) (a : N.t) : Inst :=
        subInst I (NSet.add a (slotTargets I p)) (ownDependencies I p) nil.

      Theorem versions_lookupLink : forall I k v m u a,
          versions (linkSubInst I (snd k, v) a) (Nm.Link k v m u a) =
          versions I (Nm.Link k v m u a).
      Proof.
        intros I k v m u a; cbn [versions]; unfold linkSubInst.
        rewrite (slotKey_agree I _ _ _ (snd k, v) a
                   (ownDependencies_id I (snd k, v))).
        rewrite realVersions_subInst; [reflexivity | apply slotKey_target].
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
        unfold peerKeyAt, peerCandsAt, peerKeyAt.
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
        assert (Htgt : forall d, In d (dependenciesOf I (snd k, v)) ->
                   NSet.In (d_target d)
                     (NSet.union (slotTargets I (snd k, v))
                        (peerNames I (snd k, v)))).
        { intros d Hdr; apply NSet.union_spec; left;
            apply slotTargets_spec; exact Hdr. }
        unfold pkgSubInst; f_equal.
        - unfold entryEdges, base; cbn [fst snd].
          rewrite (dirs_agree I _ _ _ (snd k, v) Hd).
          unfold depsOfL; f_equal; apply map_ext_in; intros a _.
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
        subInst I (NSet.union (slotTargets I p) (peerNames I (snd m, u)))
          (ownDependencies I p) (ownPeerDependencies I (snd m, u)).

      Lemma linkEdges_agree : forall I k v m u,
          linkEdges (peerSubInst I (snd k, v) m u) (k, v) m u =
          linkEdges I (k, v) m u.
      Proof.
        intros I k v m u; unfold peerSubInst.
        pose proof (ownDependencies_id I (snd k, v)) as Hd.
        assert (Hpr : peerDependenciesAt
                        (subInst I
                           (NSet.union (slotTargets I (snd k, v))
                              (peerNames I (snd m, u)))
                           (ownDependencies I (snd k, v))
                           (ownPeerDependencies I (snd m, u))) (snd m, u) =
                      peerDependenciesAt I (snd m, u))
          by (unfold peerDependenciesAt; cbn [inst_peer subInst];
              apply ownPeerDependencies_id).
        unfold linkEdges; rewrite Hpr.
        unfold depsOfL; f_equal; apply map_ext_in; intros r Hr.
        f_equal; unfold linkCands, peerActive, peerCandsAt, peerKeyAt, base.
        cbn [fst snd].
        rewrite (dirs_agree I _ _ _ (snd k, v) Hd).
        rewrite (slotKey_agree I _ _ _ (snd k, v) (p_name r) Hd).
        rewrite realVersions_subInst;
          [reflexivity | apply slotKey_peerTargets; exact Hr].
      Qed.

      Theorem dependees_lookupIntermediate : forall I k v m u,
          dependees (peerSubInst I (snd k, v) m u)
            (Nm.Intermediate k v m, Vs.Orig u) =
          dependees I (Nm.Intermediate k v m, Vs.Orig u).
      Proof.
        intros I k v m u; cbn [dependees]; f_equal.
        apply linkEdges_agree.
      Qed.

      Definition holderSubInst (I : Inst) (p : RPkg.t) : Inst :=
        subInst I NSet.empty (ownDependencies I p) (ownPeerDependencies I p).

      Lemma peerNames_own : forall I ns deps p,
          peerNames (subInst I ns deps (ownPeerDependencies I p)) p =
          peerNames I p.
      Proof.
        intros I ns deps p; unfold peerNames, peerDependenciesAt.
        cbn [inst_peer subInst]; rewrite ownPeerDependencies_id; reflexivity.
      Qed.

      Theorem dependees_lookupLink : forall I k v m u a x,
          dependees (holderSubInst I (snd k, v)) (Nm.Link k v m u a, x) =
          dependees I (Nm.Link k v m u a, x).
      Proof.
        intros I k v m u a x; unfold holderSubInst.
        pose proof (ownDependencies_id I (snd k, v)) as Hd.
        destruct x as [w |]; cbn [dependees];
          unfold sightSet, holderEdge, plainKey, chains, base; cbn [fst snd];
          change (rootPkg (subInst I _ _ _)) with (rootPkg I);
          rewrite ?(slotKey_agree I _ _ _ (snd k, v) a Hd), ?peerNames_own;
          reflexivity.
      Qed.

      Theorem dependees_lookupSight : forall I k v a x,
          dependees I (Nm.Sight k v a, x) = T.DependeesSet.empty.
      Proof. intros I k v a x; reflexivity. Qed.

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
                  [p [m [u [a [_ [_ [_ [_ [_ He]]]]]]]]]]]];
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
                   [p [m' [u' [a [_ [_ [_ [_ [_ He]]]]]]]]]]]] _];
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
