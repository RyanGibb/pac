From Stdlib Require Import MSets List Bool.
From PackageCalculus Require Import Prelude Core Versions Semver Concurrent.

Module Npm (N V : UsualOrderedType) (PM : SemverMatch V).
  (* Module application is generative, so the concurrent instance is the
     only one: every set keyed by source names goes through C. *)
  Module NKey := PairUOT N N.
  Module Conc := Concurrent NKey V V.
  Module C := Conc.C.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.
  Module Nm := Conc.Reduction.Name.
  Module Vs := Conc.Reduction.Version.
  Module T := Conc.Reduction.T.
  Module NmOT := Conc.Reduction.NameOT.
  Module VsOT := Conc.Reduction.VersionOT.
  Module SOvcv := Conc.Reduction.SOvcv.
  Module SOptp := Conc.Reduction.SOptp.

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
  Module SOmt := SetOps NmOT T.Pkg NmSet T.PkgSet.
  Module SOwt := SetOps VsOT T.Pkg T.VSet T.PkgSet.
  Module SOhd := SetOps T.Dependees T.DepElt T.DependeesSet T.DepRel.
  Module SOqd := SetOps T.Pkg T.DepElt T.PkgSet T.DepRel.
  Module SOtp := SetOps T.Pkg Conc.ParentElt T.PkgSet Conc.ParentRel.
  Module SOpt := SetOps Pkg T.Pkg PkgSet T.PkgSet.
  Module SOkt := SetOps NKey T.Pkg KeySet T.PkgSet.
  Module SOvt := SetOps V T.Pkg VSet T.PkgSet.

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

  Definition ownedBy {A : Type} (l : list (RPkg.t * A)) (p : RPkg.t)
    : list A :=
    fold_right
      (fun q acc => if RPkgEqb.eqb (fst q) p then snd q :: acc else acc)
      nil l.

  Lemma in_ownedBy : forall (A : Type) (l : list (RPkg.t * A)) p a,
      In a (ownedBy l p) <-> In (p, a) l.
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
      ownedBy (List.filter f l) p = ownedBy l p.
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
    intros R n v; unfold realVersions; rewrite SOrv.mem_filterMap.
    split.
    - intros [[m u] [HR He]]; simpl in He.
      destruct (NEqb.eqb m n) eqn:Hm; [| discriminate].
      apply NEqb.eqb_true_iff in Hm; subst m.
      injection He as <-; exact HR.
    - intro H; exists (n, v); split; [exact H | simpl].
      rewrite NEqb.eqb_refl; reflexivity.
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
    List.filter (depActive I p) (ownedBy (inst_dep I) p).

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
    ownedBy (inst_peer I) p.

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

  Definition peerDirs (I : Inst) : NSet.t :=
    namesOfL (fun q => p_name (snd q)) (inst_peer I).

  Definition childDirs (I : Inst) (p : RPkg.t) : NSet.t :=
    NSet.union (dirs I p) (peerDirs I).

  Definition childKeys (I : Inst) (p : RPkg.t) : KeySet.t :=
    SOnk.map (slotKey I p) (childDirs I p).

  Definition childCands (I : Inst) (p : RPkg.t)
      (m : NKey.t) : VSet.t :=
    if KeyEqb.eqb m (slotKey I p (fst m))
    then if NSet.mem (fst m) (dirs I p)
         then slotCands I p (fst m)
         else if NSet.mem (fst m) (peerDirs I)
              then realVersions (inst_repo I) (snd m)
              else VSet.empty
    else VSet.empty.

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
    - intros [k0 [Hk0 Hm]]; apply SOvp.mem_map in Hm.
      destruct Hm as [u [Hu He]].
      assert (k0 = k) by congruence; assert (u = v) by congruence.
      subst k0 u; split; [exact Hk0 | apply mem_realVersions; exact Hu].
    - intros [Hk Hb]; exists k; split; [exact Hk |].
      apply SOvp.mem_map; exists v; split;
        [apply mem_realVersions; exact Hb | reflexivity].
  Qed.

  Definition Installs (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (p : Pkg.t) (m : NKey.t) (v : V.t) : Prop :=
    PkgSet.In (m, v) S /\ Conc.ParentRel.In ((m, v), p) pi.

  Record IsResolution (I : Inst)
      (S : PkgSet.t) (pi : Conc.ParentRel.t) : Prop :=
    { nres_subset : forall q, PkgSet.In q S -> Available I q
    ; nres_root : PkgSet.In (rootPkg I) S
    ; nres_unique :
        forall p m v v', Installs S pi p m v -> Installs S pi p m v' -> v = v'
    ; nres_slot :
        forall p, PkgSet.In p S ->
        forall a, NSet.In a (dirs I (base p)) ->
        exists v, VSet.In v (slotCands I (base p) a) /\
          Installs S pi p (slotKey I (base p) a) v
    ; nres_peer_install :
        forall p, PkgSet.In p S ->
        forall m u, Installs S pi p m u ->
        forall r, In ((snd m, u), r) (inst_peer I) ->
          p_optional r = false ->
        exists v, VSet.In v (peerCandsAt I (base p) r) /\
          Installs S pi p (peerKeyAt I (base p) r) v
    ; nres_peer_match :
        forall p, PkgSet.In p S ->
        forall m u, Installs S pi p m u ->
        forall r, In ((snd m, u), r) (inst_peer I) ->
          p_optional r = true ->
          NSet.In (p_name r) (dirs I (base p)) ->
        forall v, Installs S pi p (peerKeyAt I (base p) r) v ->
          VSet.In v (peerCandsAt I (base p) r)
    ; nres_root_peer :
        forall r, In (inst_root I, r) (inst_peer I) ->
          p_optional r = false ->
        exists v, VSet.In v (peerCandsAt I (inst_root I) r) /\
          Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) v
    ; nres_root_peer_match :
        forall r, In (inst_root I, r) (inst_peer I) ->
          p_optional r = true ->
          NSet.In (p_name r) (dirs I (inst_root I)) ->
        forall v, Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) v ->
          VSet.In v (peerCandsAt I (inst_root I) r)
    ; nres_parents :
        forall c q, Conc.ParentRel.In (c, q) pi ->
          PkgSet.In c S /\ PkgSet.In q S /\
          KeySet.In (fst c) (childKeys I (base q)) }.

  Module Reduction.

    Definition idg (v : V.t) : V.t := v.

    Definition versions (I : Inst) (n : Nm.t) : T.VSet.t :=
      match n with
      | Nm.Granular k w =>
          if PkgSet.mem (k, w) (realPkgs I)
          then T.VSet.singleton (Vs.Orig w)
          else T.VSet.empty
      | Nm.Intermediate k v m =>
          Conc.Reduction.embedVS (childCands I (snd k, v) m)
      end.

    Definition entryEdges (I : Inst) (q : Pkg.t)
      : T.DependeesSet.t :=
      depsOfL (fun a =>
          (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
           Conc.Reduction.embedVS (slotCands I (base q) a)))
        (NSet.elements (dirs I (base q))).

    Definition rootPeerEdges (I : Inst) (q : Pkg.t)
      : T.DependeesSet.t :=
      if PkgEqb.eqb q (rootPkg I)
      then depsOfL (fun r =>
               (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
                Conc.Reduction.embedVS (peerCandsAt I (base q) r)))
             (activePeers I (base q) (base q))
      else T.DependeesSet.empty.

    Definition peerEdgesAt (I : Inst) (q : Pkg.t)
        (m : NKey.t) (u : V.t) : T.DependeesSet.t :=
      depsOfL (fun r =>
          (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
           Conc.Reduction.embedVS (peerCandsAt I (base q) r)))
        (activePeers I (base q) (snd m, u)).

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
            (peerEdgesAt I (k, v) m u)
      | _ => T.DependeesSet.empty
      end.

    Lemma mem_entryEdges : forall I q h,
        T.DependeesSet.In h (entryEdges I q) <->
        exists a, NSet.In a (dirs I (base q)) /\
          h = (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
               Conc.Reduction.embedVS (slotCands I (base q) a)).
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
               Conc.Reduction.embedVS (peerCandsAt I (base q) r)).
    Proof.
      intros I q h; unfold rootPeerEdges.
      destruct (PkgEqb.eqb q (rootPkg I)) eqn:Hq.
      - apply PkgEqb.eqb_true_iff in Hq.
        rewrite mem_depsOfL; unfold activePeers, peerDependenciesAt; split.
        + intros [r [Hr He]]; apply List.filter_In in Hr.
          destruct Hr as [Hr Hact]; split; [exact Hq |].
          exists r; split; [apply in_ownedBy; exact Hr |].
          split; [exact Hact | symmetry; exact He].
        + intros [_ [r [Hr [Hact He]]]]; exists r; split;
            [| symmetry; exact He].
          apply List.filter_In; split;
            [apply in_ownedBy; exact Hr | exact Hact].
      - split; [intro H; destruct (SOhh.empty_in _ H) |].
        intros [He _]; subst q; rewrite PkgEqb.eqb_refl in Hq; discriminate.
    Qed.

    Lemma mem_peerEdgesAt : forall I q m u h,
        T.DependeesSet.In h (peerEdgesAt I q m u) <->
        exists r, In ((snd m, u), r) (inst_peer I) /\
          peerActive I (base q) r = true /\
          h = (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
               Conc.Reduction.embedVS (peerCandsAt I (base q) r)).
    Proof.
      intros I q m u h; unfold peerEdgesAt; rewrite mem_depsOfL.
      unfold activePeers, peerDependenciesAt; split.
      - intros [r [Hr He]]; apply List.filter_In in Hr.
        destruct Hr as [Hr Hact]; exists r.
        split; [apply in_ownedBy; exact Hr | split; [exact Hact |]].
        symmetry; exact He.
      - intros [r [Hr [Hact He]]]; exists r; split; [| symmetry; exact He].
        apply List.filter_In; split;
          [apply in_ownedBy; exact Hr | exact Hact].
    Qed.

    Definition targetNames (I : Inst) : NmSet.t :=
      NmSet.union
        (SOpn.map (fun q => Nm.Granular (fst q) (snd q)) (realPkgs I))
        (SOpn.unionMap (fun q =>
             SOnm.map (fun m => Nm.Intermediate (fst q) (snd q) m)
               (childKeys I (base q)))
           (realPkgs I)).

    Definition transR (I : Inst) : T.PkgSet.t :=
      SOmt.unionMap
        (fun n => SOwt.map (fun x => (n, x)) (versions I n))
        (targetNames I).

    Lemma mem_transR : forall I n x,
        T.PkgSet.In (n, x) (transR I) <->
        NmSet.In n (targetNames I) /\ T.VSet.In x (versions I n).
    Proof.
      intros I n x; unfold transR; rewrite SOmt.mem_unionMap; split.
      - intros [n0 [Hnm Hm]]; apply SOwt.mem_map in Hm.
        destruct Hm as [x0 [Hx He]].
        assert (n0 = n) by congruence; assert (x0 = x) by congruence.
        subst n0 x0; split; assumption.
      - intros [Hnm Hx]; exists n; split; [exact Hnm |].
        apply SOwt.mem_map; exists x; split; [exact Hx | reflexivity].
    Qed.

    Lemma targetNames_int : forall I k v m,
        NmSet.In (Nm.Intermediate k v m) (targetNames I) ->
        KeySet.In m (childKeys I (snd k, v)).
    Proof.
      intros I k v m H; unfold targetNames in H.
      apply NmSet.union_spec in H; destruct H as [H | H].
      - apply SOpn.mem_map in H; destruct H as [q [_ He]]; discriminate He.
      - apply SOpn.mem_unionMap in H; destruct H as [q [_ H]].
        apply SOnm.mem_map in H; destruct H as [m' [Hm He]].
        injection He as -> -> ->; exact Hm.
    Qed.

    Definition depEdges (s : T.Pkg.t) (hs : T.DependeesSet.t) : T.DepRel.t :=
      SOhd.map (fun h => (s, h)) hs.

    Definition transD (I : Inst) : T.DepRel.t :=
      SOqd.unionMap (fun s => depEdges s (dependees I s)) (transR I).

    Lemma mem_transD : forall I s h,
        T.DepRel.In (s, h) (transD I) <->
        T.PkgSet.In s (transR I) /\
        T.DependeesSet.In h (dependees I s).
    Proof.
      intros I s h; unfold transD; rewrite SOqd.mem_unionMap; split.
      - intros [s0 [Hs0 Hm]]; unfold depEdges in Hm.
        apply SOhd.mem_map in Hm; destruct Hm as [h0 [Hh0 He]].
        assert (s0 = s) by congruence; assert (h0 = h) by congruence.
        subst s0 h0; split; assumption.
      - intros [Hs Hh]; exists s; split; [exact Hs |].
        unfold depEdges; apply SOhd.mem_map.
        exists h; split; [exact Hh | reflexivity].
    Qed.

    Definition transRoot (I : Inst) : T.Pkg.t :=
      Conc.Reduction.embedPkg idg (rootPkg I).

    Definition npmResolution (S : T.PkgSet.t) : PkgSet.t :=
      Conc.Reduction.concurrentResolution idg S.

    Definition npmParents (S : T.PkgSet.t) : Conc.ParentRel.t :=
      SOtp.filterMap
        (fun s => match s with
                  | (Nm.Intermediate k v m, Vs.Orig u) =>
                      if T.PkgSet.mem (Conc.Reduction.embedPkg idg (k, v)) S
                      then Some ((m, u), (k, v))
                      else None
                  | _ => None
                  end)
        S.

    Lemma mem_npmParents : forall S c q,
        Conc.ParentRel.In (c, q) (npmParents S) <->
        T.PkgSet.In
          (Nm.Intermediate (fst q) (snd q) (fst c), Vs.Orig (snd c)) S /\
        T.PkgSet.In (Conc.Reduction.embedPkg idg q) S.
    Proof.
      intros S [m u] [k v]; cbn [fst snd].
      unfold npmParents; rewrite SOtp.mem_filterMap; split.
      - intros [[n x] [Hs He]]; destruct n as [k' w | k' v' m'];
          destruct x as [u' | w']; try discriminate He.
        destruct (T.PkgSet.mem (Conc.Reduction.embedPkg idg (k', v')) S) eqn:Hm;
          [| discriminate He].
        injection He as He1 He2 He3 He4; subst.
        split; [exact Hs | apply T.PkgSet.mem_spec; exact Hm].
      - intros [H1 H2].
        exists (Nm.Intermediate k v m, Vs.Orig u); split; [exact H1 |].
        assert (T.PkgSet.mem (Conc.Reduction.embedPkg idg (k, v)) S = true)
          as Hm
          by (apply T.PkgSet.mem_spec; exact H2).
        rewrite Hm; reflexivity.
    Qed.

    Lemma dependees_embedPkg : forall I q,
        dependees I (Conc.Reduction.embedPkg idg q) =
        T.DependeesSet.union (entryEdges I q) (rootPeerEdges I q).
    Proof.
      intros I [k v]; unfold Conc.Reduction.embedPkg, idg; cbn [fst snd].
      cbn [dependees]; rewrite VEqb.eqb_refl; reflexivity.
    Qed.

    Lemma exit_selected : forall I S k v m u,
        T.IsResolution (transR I) (transD I) (transRoot I) S ->
        T.PkgSet.In (Nm.Intermediate k v m, Vs.Orig u) S ->
        T.PkgSet.In (Conc.Reduction.embedPkg idg (m, u)) S.
    Proof.
      intros I S k v m u [Hsub Hroot Hdep Huniq] Hin.
      destruct (Hdep _ Hin (Nm.Granular m u) (T.VSet.singleton (Vs.Orig u)))
        as [x [Hx HxS]].
      { apply mem_transD; split; [exact (Hsub _ Hin) |].
        cbn [dependees]; apply SOhh.add_in; left; reflexivity. }
      apply SOvcv.singleton_in in Hx; subst x.
      unfold Conc.Reduction.embedPkg, idg; cbn [fst snd]; exact HxS.
    Qed.

    Lemma entry_selected : forall I S q a,
        T.IsResolution (transR I) (transD I) (transRoot I) S ->
        T.PkgSet.In (Conc.Reduction.embedPkg idg q) S ->
        NSet.In a (dirs I (base q)) ->
        exists v, VSet.In v (slotCands I (base q) a) /\
          T.PkgSet.In
            (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
             Vs.Orig v) S.
    Proof.
      intros I S q a [Hsub Hroot Hdep Huniq] Hq Ha.
      destruct (Hdep _ Hq
                  (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a))
                  (Conc.Reduction.embedVS (slotCands I (base q) a)))
        as [x [Hx HxS]].
      { apply mem_transD; split; [exact (Hsub _ Hq) |].
        rewrite dependees_embedPkg.
        apply T.DependeesSet.union_spec; left; apply mem_entryEdges.
        exists a; split; [exact Ha | reflexivity]. }
      apply SOvcv.mem_map in Hx; destruct Hx as [v [Hv ->]].
      exists v; split; assumption.
    Qed.

    Lemma root_peer_selected : forall I S r,
        T.IsResolution (transR I) (transD I) (transRoot I) S ->
        In (inst_root I, r) (inst_peer I) ->
        peerActive I (inst_root I) r = true ->
        exists v, VSet.In v (peerCandsAt I (inst_root I) r) /\
          T.PkgSet.In
            (Nm.Intermediate (fst (rootPkg I)) (snd (rootPkg I))
               (peerKeyAt I (inst_root I) r), Vs.Orig v) S.
    Proof.
      intros I S r [Hsub Hroot Hdep Huniq] Hr Hact.
      destruct (Hdep _ Hroot
                  (Nm.Intermediate (fst (rootPkg I)) (snd (rootPkg I))
                     (peerKeyAt I (inst_root I) r))
                  (Conc.Reduction.embedVS
                     (peerCandsAt I (inst_root I) r)))
        as [x [Hx HxS]].
      { apply mem_transD; split; [exact (Hsub _ Hroot) |].
        unfold transRoot; rewrite dependees_embedPkg.
        apply T.DependeesSet.union_spec; right; apply mem_rootPeerEdges.
        split; [reflexivity |]; rewrite base_rootPkg.
        exists r; split; [exact Hr | split; [exact Hact | reflexivity]]. }
      apply SOvcv.mem_map in Hx; destruct Hx as [v [Hv ->]].
      exists v; split; assumption.
    Qed.

    Lemma peer_selected : forall I S q m u r,
        T.IsResolution (transR I) (transD I) (transRoot I) S ->
        T.PkgSet.In (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S ->
        In ((snd m, u), r) (inst_peer I) ->
        peerActive I (base q) r = true ->
        exists v, VSet.In v (peerCandsAt I (base q) r) /\
          T.PkgSet.In
            (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
             Vs.Orig v) S.
    Proof.
      intros I S q m u r [Hsub Hroot Hdep Huniq] Hin Hr Hact.
      destruct (Hdep _ Hin
                  (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r))
                  (Conc.Reduction.embedVS (peerCandsAt I (base q) r)))
        as [x [Hx HxS]].
      { apply mem_transD; split; [exact (Hsub _ Hin) |].
        cbn [dependees]; apply SOhh.add_in; right.
        apply mem_peerEdgesAt; exists r; split;
          [exact Hr | split; [exact Hact | reflexivity]]. }
      apply SOvcv.mem_map in Hx; destruct Hx as [v [Hv ->]].
      exists v; split; assumption.
    Qed.

    Theorem npm_soundness : forall I S,
        T.IsResolution (transR I) (transD I) (transRoot I) S ->
        IsResolution I (npmResolution S) (npmParents S).
    Proof.
      intros I S Hres.
      assert (Hres' := Hres); destruct Hres' as [Hsub Hroot Hdep Huniq].
      assert (Hpi : forall q m v,
                 T.PkgSet.In (Conc.Reduction.embedPkg idg q) S ->
                 T.PkgSet.In
                   (Nm.Intermediate (fst q) (snd q) m, Vs.Orig v) S ->
                 Installs (npmResolution S) (npmParents S) q m v).
      { intros [k w] m v Hq Hi; split.
        - apply Conc.Reduction.mem_concurrentResolution.
          exact (exit_selected I S k w m v Hres Hi).
        - apply mem_npmParents; cbn [fst snd]; split; assumption. }
      constructor.
      - intros [k w] Hq; apply Conc.Reduction.mem_concurrentResolution in Hq.
        pose proof (Hsub _ Hq) as Hr; apply mem_transR in Hr.
        destruct Hr as [_ Hv].
        cbn [versions Conc.Reduction.embedPkg fst snd] in Hv.
        unfold idg in Hv.
        destruct (PkgSet.mem (k, w) (realPkgs I)) eqn:Hm;
          [| destruct (SOvcv.empty_in _ Hv)].
        apply PkgSet.mem_spec in Hm; apply mem_realPkgs; exact Hm.
      - apply Conc.Reduction.mem_concurrentResolution; exact Hroot.
      - intros p m v v' [_ H1] [_ H2].
        apply mem_npmParents in H1; apply mem_npmParents in H2.
        destruct H1 as [Hi1 _]; destruct H2 as [Hi2 _];
          cbn [fst snd] in Hi1, Hi2.
        pose proof (Huniq _ _ _ Hi1 Hi2) as He; injection He as ->;
          reflexivity.
      - intros p Hp a Ha; apply Conc.Reduction.mem_concurrentResolution in Hp.
        destruct (entry_selected I S p a Hres Hp Ha) as [v [Hv Hi]].
        exists v; split; [exact Hv | exact (Hpi p _ v Hp Hi)].
      - intros p Hp m u [_ Hu] r Hr Hopt.
        apply Conc.Reduction.mem_concurrentResolution in Hp.
        apply mem_npmParents in Hu; destruct Hu as [Hi _];
          cbn [fst snd] in Hi.
        destruct (peer_selected I S p _ u r Hres Hi Hr
                    (proj2 (Bool.orb_true_iff _ _)
                       (or_introl (proj2 (Bool.negb_true_iff _) Hopt))))
          as [v [Hv Hj]].
        exists v; split; [exact Hv | exact (Hpi p _ v Hp Hj)].
      - intros p Hp m u [_ Hu] r Hr Hopt Hname v [_ Hv].
        apply Conc.Reduction.mem_concurrentResolution in Hp.
        apply mem_npmParents in Hu; destruct Hu as [Hi _];
          cbn [fst snd] in Hi.
        assert (Hact : peerActive I (base p) r = true)
          by (unfold peerActive; apply Bool.orb_true_iff; right;
              apply NSet.mem_spec; exact Hname).
        destruct (peer_selected I S p _ u r Hres Hi Hr Hact)
          as [v0 [Hv0 Hj]].
        apply mem_npmParents in Hv; destruct Hv as [Hi' _];
          cbn [fst snd] in Hi'.
        pose proof (Huniq _ _ _ Hi' Hj) as Heq; injection Heq as ->; exact Hv0.
      - intros r Hr Hopt.
        destruct (root_peer_selected I S r Hres Hr
                    (proj2 (Bool.orb_true_iff _ _)
                       (or_introl (proj2 (Bool.negb_true_iff _) Hopt))))
          as [v [Hv Hj]].
        exists v; split; [exact Hv | exact (Hpi (rootPkg I) _ v Hroot Hj)].
      - intros r Hr Hopt Hname v [_ Hv].
        assert (Hact : peerActive I (inst_root I) r = true)
          by (unfold peerActive; apply Bool.orb_true_iff; right;
              apply NSet.mem_spec; exact Hname).
        destruct (root_peer_selected I S r Hres Hr Hact) as [v0 [Hv0 Hj]].
        apply mem_npmParents in Hv; destruct Hv as [Hi' _];
          cbn [fst snd] in Hi'.
        pose proof (Huniq _ _ _ Hi' Hj) as Heq; injection Heq as ->; exact Hv0.
      - intros [m u] [k w] Hcq; apply mem_npmParents in Hcq.
        cbn [fst snd] in Hcq; destruct Hcq as [Hi Hq].
        split; [| split].
        + apply Conc.Reduction.mem_concurrentResolution.
          exact (exit_selected I S k w m u Hres Hi).
        + apply Conc.Reduction.mem_concurrentResolution; exact Hq.
        + apply Hsub, mem_transR in Hi; destruct Hi as [Hn _].
          exact (targetNames_int I k w m Hn).
    Qed.

    Lemma installs_childCands : forall I S pi p m v,
        IsResolution I S pi -> PkgSet.In p S ->
        KeySet.In m (childKeys I (base p)) ->
        Installs S pi p m v ->
        VSet.In v (childCands I (base p) m).
    Proof.
      intros I S pi p m v Hres Hp Hm Hi.
      destruct Hres as [Hsub Hroot Huniq Hslot Hpin Hpm Hrp Hrpm Hpar].
      unfold childKeys in Hm; apply SOnk.mem_map in Hm.
      destruct Hm as [a [Ha ->]].
      unfold childCands; rewrite slotKey_fst, KeyEqb.eqb_refl.
      destruct (NSet.mem a (dirs I (base p))) eqn:Hsa.
      - apply NSet.mem_spec in Hsa.
        destruct (Hslot p Hp a Hsa) as [v' [Hv' Hi']].
        rewrite (Huniq p (slotKey I (base p) a) v v' Hi Hi'); exact Hv'.
      - unfold childDirs in Ha; apply NSet.union_spec in Ha.
        destruct Ha as [Ha | Ha];
          [apply NSet.mem_spec in Ha; rewrite Ha in Hsa; discriminate |].
        assert (Hpa : NSet.mem a (peerDirs I) = true)
          by (apply NSet.mem_spec; exact Ha).
        rewrite Hpa; destruct Hi as [HinS _].
        destruct (Hsub _ HinS) as [_ Hb]; unfold base in Hb.
        cbn [fst snd] in Hb; apply mem_realVersions; exact Hb.
    Qed.

    Lemma root_peer_installs : forall I S pi r,
        IsResolution I S pi ->
        In (inst_root I, r) (inst_peer I) ->
        peerActive I (inst_root I) r = true ->
        exists w, VSet.In w (peerCandsAt I (inst_root I) r) /\
          Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) w.
    Proof.
      intros I S pi r Hres Hr Hact.
      destruct Hres as [_ Hroot _ Hslot _ _ Hrp Hrpm _].
      destruct (p_optional r) eqn:Hopt; [| exact (Hrp r Hr Hopt)].
      unfold peerActive in Hact; rewrite Hopt in Hact;
        cbn [negb orb] in Hact; apply NSet.mem_spec in Hact.
      assert (Hdir : NSet.In (p_name r) (dirs I (base (rootPkg I))))
        by (rewrite base_rootPkg; exact Hact).
      destruct (Hslot (rootPkg I) Hroot (p_name r) Hdir) as [w [_ Hi]].
      rewrite base_rootPkg in Hi.
      exists w; unfold peerKeyAt;
        split; [exact (Hrpm r Hr Hopt Hact w Hi) | exact Hi].
    Qed.

    Definition instNode (S : PkgSet.t) (pi : Conc.ParentRel.t)
        (p : Pkg.t) (m : NKey.t) (u : V.t) : option T.Pkg.t :=
      if andb (PkgSet.mem (m, u) S) (Conc.ParentRel.mem ((m, u), p) pi)
      then Some (Nm.Intermediate (fst p) (snd p) m, Vs.Orig u)
      else None.

    Lemma instNode_some : forall S pi p m u s,
        instNode S pi p m u = Some s <->
        PkgSet.In (m, u) S /\ Conc.ParentRel.In ((m, u), p) pi /\
        s = (Nm.Intermediate (fst p) (snd p) m, Vs.Orig u).
    Proof.
      intros S pi p m u s; unfold instNode.
      destruct (PkgSet.mem (m, u) S) eqn:H1;
        destruct (Conc.ParentRel.mem ((m, u), p) pi) eqn:H2; cbn [andb];
        split; try discriminate.
      - intro H; split; [apply PkgSet.mem_spec; exact H1 |].
        split; [apply Conc.ParentRel.mem_spec; exact H2 | congruence].
      - intros [_ [_ ->]]; reflexivity.
      - intros [_ [H _]]; apply Conc.ParentRel.mem_spec in H; congruence.
      - intros [H _]; apply PkgSet.mem_spec in H; congruence.
      - intros [H _]; apply PkgSet.mem_spec in H; congruence.
    Qed.

    Definition coreResolution (I : Inst)
        (S : PkgSet.t) (pi : Conc.ParentRel.t) : T.PkgSet.t :=
      T.PkgSet.union (Conc.Reduction.embedSet idg S)
        (SOpt.unionMap (fun p =>
             SOkt.unionMap (fun m =>
                 SOvt.filterMap (instNode S pi p m)
                   (realVersions (inst_repo I) (snd m)))
               (childKeys I (base p)))
           S).

    Lemma embedSet_gran : forall S s,
        T.PkgSet.In s (Conc.Reduction.embedSet idg S) <->
        exists k v, PkgSet.In (k, v) S /\ s = (Nm.Granular k v, Vs.Orig v).
    Proof.
      intros S s; unfold Conc.Reduction.embedSet; rewrite SOptp.mem_map; split.
      - intros [[k v] [Hp ->]]; exists k, v; split;
          [exact Hp | unfold Conc.Reduction.embedPkg, idg; reflexivity].
      - intros [k [v [Hp ->]]]; exists (k, v); split;
          [exact Hp | unfold Conc.Reduction.embedPkg, idg; reflexivity].
    Qed.

    Lemma dependees_gran : forall I k v,
        dependees I (Nm.Granular k v, Vs.Orig v) =
        T.DependeesSet.union (entryEdges I (k, v))
          (rootPeerEdges I (k, v)).
    Proof.
      intros I k v; cbn [dependees]; rewrite VEqb.eqb_refl; reflexivity.
    Qed.

    Lemma mem_coreResolution : forall I S pi s,
        T.PkgSet.In s (coreResolution I S pi) <->
        (exists k v, PkgSet.In (k, v) S /\
           s = (Nm.Granular k v, Vs.Orig v)) \/
        (exists p m u, PkgSet.In p S /\ KeySet.In m (childKeys I (base p)) /\
           VSet.In u (realVersions (inst_repo I) (snd m)) /\
           PkgSet.In (m, u) S /\ Conc.ParentRel.In ((m, u), p) pi /\
           s = (Nm.Intermediate (fst p) (snd p) m, Vs.Orig u)).
    Proof.
      intros I S pi s; unfold coreResolution.
      rewrite T.PkgSet.union_spec, embedSet_gran, SOpt.mem_unionMap.
      split.
      - intros [H | [p [Hp Hm]]]; [left; exact H | right].
        cbn beta in Hm; apply SOkt.mem_unionMap in Hm.
        destruct Hm as [m [Hm Hu]]; cbn beta in Hu.
        apply SOvt.mem_filterMap in Hu; destruct Hu as [u [Hu Hc]].
        apply instNode_some in Hc; destruct Hc as [Hg1 [Hg2 Hg3]].
        exists p, m, u; repeat split; assumption.
      - intros [H | [p [m [u [Hp [Hm [Hu [HS [Hpi ->]]]]]]]]];
          [left; exact H | right].
        exists p; split; [exact Hp | cbn beta].
        apply SOkt.mem_unionMap; exists m; split; [exact Hm | cbn beta].
        apply SOvt.mem_filterMap; exists u; split; [exact Hu |].
        apply instNode_some; split;
          [exact HS | split; [exact Hpi | reflexivity]].
    Qed.

    Lemma mem_targetNames_gran : forall I p,
        PkgSet.In p (realPkgs I) ->
        NmSet.In (Nm.Granular (fst p) (snd p)) (targetNames I).
    Proof.
      intros I p Hp; unfold targetNames; apply NmSet.union_spec; left.
      apply SOpn.mem_map; exists p; split; [exact Hp | reflexivity].
    Qed.

    Lemma mem_targetNames_int : forall I p m,
        PkgSet.In p (realPkgs I) ->
        KeySet.In m (childKeys I (base p)) ->
        NmSet.In (Nm.Intermediate (fst p) (snd p) m) (targetNames I).
    Proof.
      intros I p m Hp Hm; unfold targetNames; apply NmSet.union_spec.
      right; apply SOpn.mem_unionMap; exists p; split; [exact Hp | cbn beta].
      apply SOnm.mem_map; exists m; split; [exact Hm | reflexivity].
    Qed.

    Theorem npm_completeness : forall I S pi,
        IsResolution I S pi ->
        T.IsResolution (transR I) (transD I) (transRoot I)
          (coreResolution I S pi).
    Proof.
      intros I S pi Hres.
      assert (Hres' := Hres).
      destruct Hres' as [Hsub Hroot Huniq Hslot Hpin Hpm Hrp Hrpm Hpar].
      assert (Hreal : forall q, PkgSet.In q S -> PkgSet.In q (realPkgs I))
        by (intros q Hq; apply mem_realPkgs; exact (Hsub _ Hq)).
      assert (Hgran : forall k v, PkgSet.In (k, v) S ->
                 T.PkgSet.In (Nm.Granular k v, Vs.Orig v) (transR I)).
      { intros k v Hq; apply mem_transR; split.
        - pose proof (mem_targetNames_gran I (k, v) (Hreal _ Hq)) as Ht.
          cbn [fst snd] in Ht; exact Ht.
        - cbn [versions].
          assert (PkgSet.mem (k, v) (realPkgs I) = true) as ->
            by (apply PkgSet.mem_spec; exact (Hreal _ Hq)).
          apply SOvcv.singleton_in; reflexivity. }
      constructor.
      - intros s Hs; apply mem_coreResolution in Hs.
        destruct Hs as
          [[k [v [Hp ->]]] | [p [m [u [Hp [Hm [Hu [HS [Hpi ->]]]]]]]]];
          [exact (Hgran k v Hp) |].
        apply mem_transR; split.
        + exact (mem_targetNames_int I p m (Hreal _ Hp) Hm).
        + cbn [versions]; apply SOvcv.mem_map; exists u; split;
            [| reflexivity].
          exact (installs_childCands I S pi p m u Hres Hp Hm
                   (conj HS Hpi)).
      - apply mem_coreResolution; left.
        exists (rootKey I), (snd (inst_root I)); split;
          [exact Hroot |].
        unfold transRoot, rootPkg, Conc.Reduction.embedPkg, idg; reflexivity.
      - intros s Hs n vs Hd.
        apply mem_transD in Hd; destruct Hd as [_ Hd].
        apply mem_coreResolution in Hs.
        destruct Hs as
          [[k [v [Hp He]]] | [p [m [u [Hp [Hm [Hu [HS [Hpi He]]]]]]]]].
        + subst s; rewrite dependees_gran in Hd.
          apply T.DependeesSet.union_spec in Hd; destruct Hd as [Hd | Hd].
          * apply mem_entryEdges in Hd; destruct Hd as [a [Ha He]].
            injection He as -> ->.
            destruct (Hslot (k, v) Hp a Ha) as [w [Hw [HwS Hwpi]]].
            exists (Vs.Orig w); split.
            { apply SOvcv.mem_map; exists w; split;
                [exact Hw | reflexivity]. }
            apply mem_coreResolution; right.
            exists (k, v), (slotKey I (base (k, v)) a), w.
            repeat split; try assumption; try reflexivity.
            -- unfold childKeys; apply SOnk.mem_map; exists a; split;
                 [apply NSet.union_spec; left; exact Ha | reflexivity].
            -- apply mem_realVersions.
               exact (slotCands_real I (base (k, v)) a w Hw).
          * apply mem_rootPeerEdges in Hd.
            destruct Hd as [Hq [r [Hr [Hact He]]]].
            injection He as -> ->.
            assert (Hbr : base (k, v) = inst_root I)
              by (rewrite Hq; apply base_rootPkg).
            rewrite Hbr in Hr, Hact |- *.
            destruct (root_peer_installs I S pi r Hres Hr Hact)
              as [w [Hw [HwS Hwpi]]].
            rewrite <- Hq in Hwpi.
            exists (Vs.Orig w); split.
            { apply SOvcv.mem_map; exists w; split;
                [exact Hw | reflexivity]. }
            apply mem_coreResolution; right.
            exists (k, v), (peerKeyAt I (inst_root I) r), w.
            repeat split; try assumption; try reflexivity.
            -- rewrite Hbr; unfold childKeys, peerKeyAt.
               apply SOnk.mem_map; exists (p_name r); split; [| reflexivity].
               apply NSet.union_spec; right; unfold peerDirs.
               apply mem_namesOfL; exists (inst_root I, r); split;
                 [exact Hr | reflexivity].
            -- apply mem_realVersions.
               destruct (Hsub _ HwS) as [_ Hb]; unfold base in Hb.
               cbn [fst snd] in Hb; exact Hb.
        + destruct p as [pk pv]; cbn [fst snd] in He; subst s.
          cbn [dependees] in Hd; apply SOhh.add_in in Hd.
          assert (HI : Installs S pi (pk, pv) m u) by (split; assumption).
          destruct Hd as [He | Hd]; [injection He as -> -> |].
          * exists (Vs.Orig u); split;
              [apply SOvcv.singleton_in; reflexivity |].
            apply mem_coreResolution; left; exists m, u; split;
              [exact HS | reflexivity].
          * apply mem_peerEdgesAt in Hd; destruct Hd as [r [Hr [Hact He]]].
            injection He as -> ->.
            assert (Hgot : exists w,
                       VSet.In w (peerCandsAt I (base (pk, pv)) r) /\
                       Installs S pi (pk, pv)
                         (peerKeyAt I (base (pk, pv)) r) w).
            { destruct (p_optional r) eqn:Hopt.
              - unfold peerActive in Hact; rewrite Hopt in Hact;
                  cbn [negb orb] in Hact.
                apply NSet.mem_spec in Hact.
                destruct (Hslot (pk, pv) Hp (p_name r) Hact) as [w [_ Hi]].
                exists w; split; [| exact Hi].
                exact (Hpm (pk, pv) Hp m u HI r Hr Hopt Hact w Hi).
              - exact (Hpin (pk, pv) Hp m u HI r Hr Hopt). }
            destruct Hgot as [w [Hw [HwS Hwpi]]].
            exists (Vs.Orig w); split.
            { apply SOvcv.mem_map; exists w; split;
                [exact Hw | reflexivity]. }
            apply mem_coreResolution; right.
            exists (pk, pv), (peerKeyAt I (base (pk, pv)) r), w.
            repeat split; try assumption; try reflexivity.
            -- unfold childKeys, peerKeyAt; apply SOnk.mem_map.
               exists (p_name r); split; [| reflexivity].
               apply NSet.union_spec; right; unfold peerDirs.
               apply mem_namesOfL; exists ((snd m, u), r); split;
                 [exact Hr | reflexivity].
            -- apply mem_realVersions.
               destruct (Hsub _ HwS) as [_ Hb]; unfold base in Hb.
               cbn [fst snd] in Hb; exact Hb.
      - intros n x1 x2 H1 H2.
        apply mem_coreResolution in H1; apply mem_coreResolution in H2.
        destruct H1 as
          [[k1 [v1 [Hp1 He1]]]
          | [p1 [m1 [u1 [Hp1 [Hm1 [Hu1 [HS1 [Hpi1 He1]]]]]]]]];
        destruct H2 as
          [[k2 [v2 [Hp2 He2]]]
          | [p2 [m2 [u2 [Hp2 [Hm2 [Hu2 [HS2 [Hpi2 He2]]]]]]]]].
        + congruence.
        + congruence.
        + congruence.
        + destruct p1 as [k1 v1]; destruct p2 as [k2 v2];
            cbn [fst snd] in He1, He2.
          assert (k1 = k2) by congruence; assert (v1 = v2) by congruence;
            assert (m1 = m2) by congruence; subst.
          assert (u1 = u2) as Hu
            by exact (Huniq (k2, v2) m2 u1 u2 (conj HS1 Hpi1)
                        (conj HS2 Hpi2)).
          congruence.
    Qed.

    Theorem npmResolution_coreResolution : forall I S pi,
        npmResolution (coreResolution I S pi) = S.
    Proof.
      intros I S pi; apply PkgSet.ext; intros [k v].
      unfold npmResolution; rewrite Conc.Reduction.mem_concurrentResolution.
      rewrite mem_coreResolution.
      unfold Conc.Reduction.embedPkg, idg; cbn [fst snd]; split.
      - intros [[k' [v' [Hp He]]] | [p [m [u [_ [_ [_ [_ [_ He]]]]]]]]];
          [| discriminate He].
        injection He; intros; subst; exact Hp.
      - intro Hp; left; exists k, v; split; [exact Hp | reflexivity].
    Qed.

    (* Only this direction holds: a core resolution may carry
       intermediates the witness would not rebuild. *)
    Theorem npmParents_coreResolution : forall I S pi,
        IsResolution I S pi ->
        npmParents (coreResolution I S pi) = pi.
    Proof.
      intros I S pi Hres.
      destruct Hres as [Hsub _ _ _ _ _ _ _ Hpar].
      apply Conc.ParentRel.ext; intros [[m u] [k v]].
      rewrite mem_npmParents, !mem_coreResolution; cbn [fst snd]; split.
      - intros [[[k' [v' [_ He]]] | [p [m' [u' [_ [_ [_ [_ [Hpi He]]]]]]]]] _];
          [discriminate He |].
        destruct p as [pk pv]; cbn [fst snd] in He.
        injection He; intros; subst; exact Hpi.
      - intro Hcq; destruct (Hpar _ _ Hcq) as [Hc [Hq Hk]].
        split.
        + right; exists (k, v), m, u.
          split; [exact Hq |]; split; [exact Hk |].
          split; [| split; [exact Hc | split; [exact Hcq | reflexivity]]].
          apply mem_realVersions; exact (proj2 (Hsub _ Hc)).
        + left; exists k, v; split;
            [exact Hq | unfold Conc.Reduction.embedPkg, idg; reflexivity].
    Qed.

    Corollary peer_installed : forall I S,
        T.IsResolution (transR I) (transD I) (transRoot I) S ->
        forall k v m u,
          T.PkgSet.In (Conc.Reduction.embedPkg idg (k, v)) S ->
          T.PkgSet.In (Nm.Intermediate k v m, Vs.Orig u) S ->
        forall r, In ((snd m, u), r) (inst_peer I) ->
          p_optional r = false ->
        exists w,
          PkgSet.In (peerKeyAt I (snd k, v) r, w) (npmResolution S) /\
          Conc.ParentRel.In
            ((peerKeyAt I (snd k, v) r, w), (k, v)) (npmParents S) /\
          VSet.In w (peerCandsAt I (snd k, v) r).
    Proof.
      intros I S Hres k v m u Hq Hi r Hr Hopt.
      pose proof (npm_soundness I S Hres) as Hsrc.
      assert (Hp : PkgSet.In (k, v) (npmResolution S))
        by (apply Conc.Reduction.mem_concurrentResolution; exact Hq).
      assert (HI : Installs (npmResolution S) (npmParents S) (k, v) m u).
      { split.
        - apply Conc.Reduction.mem_concurrentResolution.
          exact (exit_selected I S k v m u Hres Hi).
        - apply mem_npmParents; cbn [fst snd]; split; assumption. }
      destruct Hsrc as [_ _ _ _ Hpin _ _ _ _].
      destruct (Hpin (k, v) Hp m u HI r Hr Hopt) as [w [Hw [HwS Hwpi]]].
      exists w; split; [exact HwS | split; [exact Hwpi | exact Hw]].
    Qed.

    Lemma targetNames_gran_real : forall I k w,
        NmSet.In (Nm.Granular k w) (targetNames I) ->
        PkgSet.In (k, w) (realPkgs I).
    Proof.
      intros I k w H; unfold targetNames in H.
      apply NmSet.union_spec in H; destruct H as [H | H].
      - apply SOpn.mem_map in H; destruct H as [[k' w'] [Hq He]].
        injection He as -> ->; exact Hq.
      - apply SOpn.mem_unionMap in H; destruct H as [q [_ H]].
        apply SOnm.mem_map in H; destruct H as [m' [_ He]]; discriminate He.
    Qed.

    Lemma targetNames_int_real : forall I k v m,
        NmSet.In (Nm.Intermediate k v m) (targetNames I) ->
        PkgSet.In (k, v) (realPkgs I).
    Proof.
      intros I k v m H; unfold targetNames in H.
      apply NmSet.union_spec in H; destruct H as [H | H].
      - apply SOpn.mem_map in H; destruct H as [q [_ He]]; discriminate He.
      - apply SOpn.mem_unionMap in H; destruct H as [[k' v'] [Hq H]].
        apply SOnm.mem_map in H; destruct H as [m' [_ He]].
        injection He as -> -> _; exact Hq.
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
      apply NSet.union_spec; right; unfold peerDirs; apply mem_namesOfL.
      exists (q, r); split; [exact Hr | reflexivity].
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

    (* Every dependee of a package of transR names a node of targetNames,
       so a lookup that starts at the root and follows dependees never
       leaves the names on which versions and dependees agree with transR
       and transD. *)
    Theorem dependees_targetNames : forall I s h,
        T.PkgSet.In s (transR I) -> T.DependeesSet.In h (dependees I s) ->
        NmSet.In (fst h) (targetNames I).
    Proof.
      intros I [n x] h Hs Hh; apply mem_transR in Hs; destruct Hs as [Hn Hx].
      destruct n as [k w | k v m].
      - apply targetNames_gran_real in Hn.
        cbn [versions] in Hx.
        destruct (PkgSet.mem (k, w) (realPkgs I));
          [| destruct (SOvcv.empty_in _ Hx)].
        apply SOvcv.singleton_in in Hx; subst x.
        rewrite dependees_gran in Hh; apply T.DependeesSet.union_spec in Hh.
        destruct Hh as [Hh | Hh].
        + apply mem_entryEdges in Hh; destruct Hh as [a [Ha ->]].
          cbn [fst snd].
          apply (mem_targetNames_int I (k, w)); [exact Hn |].
          apply slotKey_childKeys, NSet.union_spec; left; exact Ha.
        + apply mem_rootPeerEdges in Hh; destruct Hh as [_ [r [Hr [_ ->]]]].
          cbn [fst snd].
          apply (mem_targetNames_int I (k, w)); [exact Hn |].
          exact (peerKeyAt_childKeys I _ _ r Hr).
      - pose proof (targetNames_int_real I k v m Hn) as Hkv.
        cbn [versions] in Hx; apply SOvcv.mem_map in Hx.
        destruct Hx as [u [Hu ->]].
        cbn [dependees] in Hh; apply SOhh.add_in in Hh.
        destruct Hh as [-> | Hh].
        + cbn [fst]; apply (mem_targetNames_gran I (m, u)).
          unfold childCands in Hu.
          destruct (KeyEqb.eqb m (slotKey I (snd k, v) (fst m))) eqn:Hk;
            [| destruct (SOrv.empty_in _ Hu)].
          apply KeyEqb.eqb_true_iff in Hk.
          apply mem_realPkgs; unfold Available, base; cbn [fst snd].
          destruct (NSet.mem (fst m) (dirs I (snd k, v))) eqn:Hd.
          * apply NSet.mem_spec in Hd.
            split; [rewrite Hk; apply slotKey_keysOf; left; exact Hd |].
            pose proof (slotCands_real I _ _ u Hu) as Hr.
            rewrite <- Hk in Hr; exact Hr.
          * destruct (NSet.mem (fst m) (peerDirs I)) eqn:Hp;
              [| destruct (SOrv.empty_in _ Hu)].
            apply NSet.mem_spec in Hp.
            split; [rewrite Hk; apply slotKey_keysOf; right; exact Hp |].
            apply mem_realVersions; exact Hu.
        + apply mem_peerEdgesAt in Hh; destruct Hh as [r [Hr [_ ->]]].
          cbn [fst snd].
          apply (mem_targetNames_int I (k, v)); [exact Hkv |].
          exact (peerKeyAt_childKeys I _ _ r Hr).
    Qed.

    (* The packages a lookup-driven solver can reach: the root, and any
       version its versions lookup offers at the target of a dependee of
       a package already reached. *)
    Inductive Reached (I : Inst) : T.Pkg.t -> Prop :=
    | reached_root : Reached I (transRoot I)
    | reached_dependee : forall s h x,
        Reached I s -> T.DependeesSet.In h (dependees I s) ->
        T.VSet.In x (versions I (fst h)) -> Reached I (fst h, x).

    Lemma versions_gran_real : forall I k w,
        PkgSet.In (k, w) (realPkgs I) ->
        T.VSet.In (Vs.Orig w) (versions I (Nm.Granular k w)).
    Proof.
      intros I k w H; cbn [versions]; apply PkgSet.mem_spec in H.
      rewrite H; apply T.VSet.singleton_spec; reflexivity.
    Qed.

    Theorem reached_transR : forall I s,
        RepoSet.In (inst_root I) (inst_repo I) ->
        Reached I s -> T.PkgSet.In s (transR I).
    Proof.
      intros I s Hroot H; induction H as [| s h x Hs IH Hh Hx].
      - assert (Hr : PkgSet.In (rootPkg I) (realPkgs I)).
        { apply mem_realPkgs; split; [| rewrite base_rootPkg; exact Hroot].
          unfold keysOf; apply KeySet.add_spec; left; reflexivity. }
        unfold transRoot, Conc.Reduction.embedPkg, idg.
        apply mem_transR; split; [exact (mem_targetNames_gran I _ Hr) |].
        exact (versions_gran_real I (fst (rootPkg I)) (snd (rootPkg I)) Hr).
      - apply mem_transR; split; [| exact Hx].
        exact (dependees_targetNames I s h IH Hh).
    Qed.

    (* A set of reached packages that the lookups close is a resolution of
       the whole translated instance. *)
    Theorem lookup_resolution : forall I S,
        RepoSet.In (inst_root I) (inst_repo I) ->
        (forall s, T.PkgSet.In s S -> Reached I s) ->
        T.PkgSet.In (transRoot I) S ->
        (forall s, T.PkgSet.In s S ->
         forall n vs, T.DependeesSet.In (n, vs) (dependees I s) ->
         exists v, T.VSet.In v vs /\ T.PkgSet.In (n, v) S) ->
        T.VersionUnique S ->
        T.IsResolution (transR I) (transD I) (transRoot I) S.
    Proof.
      intros I S Hroot Hreach HrS Hclo Huniq; constructor.
      - intros s Hs; exact (reached_transR I s Hroot (Hreach s Hs)).
      - exact HrS.
      - intros s Hs n vs Hd; apply mem_transD in Hd.
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

      Definition peerNamesAt (I : Inst) (q : RPkg.t) : NSet.t :=
        namesOfL p_name (peerDependenciesAt I q).

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
          ownedBy (ownDependencies I p) p = ownedBy (inst_dep I) p.
      Proof.
        intros I p; unfold ownDependencies; apply ownedBy_filter.
        intros d _; cbn [fst]; apply RPkgEqb.eqb_refl.
      Qed.

      Lemma ownPeerDependencies_id : forall I p,
          ownedBy (ownPeerDependencies I p) p = ownedBy (inst_peer I) p.
      Proof.
        intros I p; unfold ownPeerDependencies; apply ownedBy_filter.
        intros r _; cbn [fst]; apply RPkgEqb.eqb_refl.
      Qed.

      Lemma mem_peerDirs_named : forall I ns deps n,
          NSet.mem n
            (peerDirs (subInst I ns deps (peerDependenciesNamed I n))) =
          NSet.mem n (peerDirs I).
      Proof.
        intros I ns deps n.
        destruct (NSet.mem n
                    (peerDirs (subInst I ns deps (peerDependenciesNamed I n))))
          eqn:H1; destruct (NSet.mem n (peerDirs I)) eqn:H2;
          try reflexivity.
        - apply NSet.mem_spec in H1; unfold peerDirs in H1.
          cbn [inst_peer subInst] in H1; apply mem_namesOfL in H1.
          destruct H1 as [q [Hq Hn]]; unfold peerDependenciesNamed in Hq.
          apply List.filter_In in Hq; destruct Hq as [Hq _].
          assert (NSet.In n (peerDirs I)) as Hc
            by (unfold peerDirs; apply mem_namesOfL; exists q;
                split; assumption).
          apply NSet.mem_spec in Hc; congruence.
        - apply NSet.mem_spec in H2; unfold peerDirs in H2.
          apply mem_namesOfL in H2; destruct H2 as [q [Hq Hn]].
          assert (NSet.In n
                    (peerDirs (subInst I ns deps (peerDependenciesNamed I n))))
            as Hc.
          { unfold peerDirs; cbn [inst_peer subInst].
            apply mem_namesOfL; exists q; split; [| exact Hn].
            unfold peerDependenciesNamed; apply List.filter_In; split;
              [exact Hq | apply NEqb.eqb_true_iff; exact Hn]. }
          apply NSet.mem_spec in Hc; congruence.
      Qed.

      Lemma dependenciesOf_agree : forall I ns deps prs p,
          ownedBy deps p = ownedBy (inst_dep I) p ->
          dependenciesOf (subInst I ns deps prs) p = dependenciesOf I p.
      Proof.
        intros I ns deps prs p Hdeps; unfold dependenciesOf, depActive.
        cbn [inst_dep inst_root subInst]; rewrite Hdeps; reflexivity.
      Qed.

      Lemma slotOf_agree : forall I ns deps prs p a,
          ownedBy deps p = ownedBy (inst_dep I) p ->
          slotOf (subInst I ns deps prs) p a = slotOf I p a.
      Proof.
        intros I ns deps prs p a Hdeps; unfold slotOf.
        rewrite (dependenciesOf_agree I ns deps prs p Hdeps); reflexivity.
      Qed.

      Lemma dirs_agree : forall I ns deps prs p,
          ownedBy deps p = ownedBy (inst_dep I) p ->
          dirs (subInst I ns deps prs) p = dirs I p.
      Proof.
        intros I ns deps prs p Hdeps; unfold dirs.
        rewrite (dependenciesOf_agree I ns deps prs p Hdeps); reflexivity.
      Qed.

      Lemma slotKey_agree : forall I ns deps prs p a,
          ownedBy deps p = ownedBy (inst_dep I) p ->
          slotKey (subInst I ns deps prs) p a = slotKey I p a.
      Proof.
        intros I ns deps prs p a Hdeps; unfold slotKey.
        rewrite (slotOf_agree I ns deps prs p a Hdeps); reflexivity.
      Qed.

      Lemma slotCands_agree : forall I ns deps prs p,
          ownedBy deps p = ownedBy (inst_dep I) p ->
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
        intros s s' x H; destruct (PkgSet.mem x s) eqn:H1;
          destruct (PkgSet.mem x s') eqn:H2; try reflexivity.
        - apply PkgSet.mem_spec in H1; apply H in H1;
            apply PkgSet.mem_spec in H1; congruence.
        - apply PkgSet.mem_spec in H2; apply H in H2;
            apply PkgSet.mem_spec in H2; congruence.
      Qed.

      Lemma slotTargets_spec : forall I p d,
          In d (dependenciesOf I p) -> NSet.In (d_target d) (slotTargets I p).
      Proof.
        intros I p d Hd; unfold slotTargets; apply mem_namesOfL.
        exists d; split; [exact Hd | reflexivity].
      Qed.

      Lemma childCands_agree : forall I ns deps prs
          (p : RPkg.t) (m : NKey.t),
          ownedBy deps p = ownedBy (inst_dep I) p ->
          (forall d, In d (dependenciesOf I p) -> NSet.In (d_target d) ns) ->
          NSet.In (snd m) ns ->
          NSet.mem (fst m) (peerDirs (subInst I ns deps prs)) =
            NSet.mem (fst m) (peerDirs I) ->
          childCands (subInst I ns deps prs) p m =
          childCands I p m.
      Proof.
        intros I ns deps prs p m Hd Ht Hm Hpa; unfold childCands.
        rewrite (slotKey_agree I ns deps prs p (fst m) Hd).
        rewrite (dirs_agree I ns deps prs p Hd).
        rewrite Hpa.
        destruct (KeyEqb.eqb m (slotKey I p (fst m)));
          destruct (NSet.mem (fst m) (dirs I p));
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

      (* keysOf is asked only whether it holds k, so any one dependency
         introducing k answers, or failing that any one peer dependency;
         the repository is asked only about the one package. *)
      Definition GranSubInst (I : Inst) (k : NKey.t) (w : V.t)
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
          GranSubInst I k w I' ->
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

      Theorem versions_lookupGran : forall I k w I',
          GranSubInst I k w I' ->
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

      Theorem versions_lookupInt : forall I k v m,
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
      Qed.

      Definition pkgSubInst (I : Inst) (p : RPkg.t) : Inst :=
        subInst I (NSet.union (slotTargets I p) (peerNamesAt I p))
          (ownDependencies I p) (ownPeerDependencies I p).

      Theorem dependees_lookupGran : forall I k v,
          dependees (pkgSubInst I (snd k, v))
            (Nm.Granular k v, Vs.Orig v) =
          dependees I (Nm.Granular k v, Vs.Orig v).
      Proof.
        intros I k v; rewrite !dependees_gran.
        pose proof (ownDependencies_id I (snd k, v)) as Hd.
        assert (Htgt : forall d, In d (dependenciesOf I (snd k, v)) ->
                   NSet.In (d_target d)
                     (NSet.union (slotTargets I (snd k, v))
                        (peerNamesAt I (snd k, v)))).
        { intros d Hdr; apply NSet.union_spec; left;
            apply slotTargets_spec; exact Hdr. }
        assert (Hn : forall r, In r (peerDependenciesAt I (snd k, v)) ->
                   NSet.In (snd (slotKey I (snd k, v) (p_name r)))
                     (NSet.union (slotTargets I (snd k, v))
                        (peerNamesAt I (snd k, v)))).
        { intros r Hr; unfold slotKey.
          destruct (slotOf I (snd k, v) (p_name r)) as [d |] eqn:Hd2.
          - cbn [snd]; apply NSet.union_spec; left.
            apply slotTargets_spec; exact (proj1 (findDepL_some _ _ _ Hd2)).
          - cbn [snd]; apply NSet.union_spec; right; unfold peerNamesAt.
            apply mem_namesOfL; exists r; split; [exact Hr | reflexivity]. }
        unfold pkgSubInst; f_equal.
        - unfold entryEdges, base; cbn [fst snd].
          rewrite (dirs_agree I _ _ _ (snd k, v) Hd).
          unfold depsOfL; f_equal; apply map_ext_in; intros a _.
          rewrite (slotKey_agree I _ _ _ (snd k, v) a Hd).
          rewrite (slotCands_agree I _ _ _ (snd k, v) Hd Htgt a).
          reflexivity.
        - assert (Hrt : rootPkg (subInst I
                            (NSet.union (slotTargets I (snd k, v))
                               (peerNamesAt I (snd k, v)))
                            (ownDependencies I (snd k, v))
                            (ownPeerDependencies I (snd k, v))) = rootPkg I)
            by reflexivity.
          unfold rootPeerEdges; rewrite Hrt.
          destruct (PkgEqb.eqb (k, v) (rootPkg I)); [| reflexivity].
          unfold base; cbn [fst snd].
          assert (Hpr : peerDependenciesAt (subInst I
                            (NSet.union (slotTargets I (snd k, v))
                               (peerNamesAt I (snd k, v)))
                            (ownDependencies I (snd k, v))
                            (ownPeerDependencies I (snd k, v))) (snd k, v) =
                        peerDependenciesAt I (snd k, v))
            by (unfold peerDependenciesAt; cbn [inst_peer subInst];
                apply ownPeerDependencies_id).
          unfold activePeers, peerActive; rewrite Hpr.
          rewrite (dirs_agree I _ _ _ (snd k, v) Hd).
          unfold depsOfL; f_equal; apply map_ext_in; intros r Hr.
          apply List.filter_In in Hr; destruct Hr as [Hr _].
          unfold peerKeyAt, peerCandsAt, peerKeyAt.
          rewrite (slotKey_agree I _ _ _ (snd k, v) (p_name r) Hd).
          rewrite realVersions_subInst; [reflexivity | apply Hn; exact Hr].
      Qed.

      Definition peerSubInst (I : Inst) (p : RPkg.t) (m : NKey.t) (u : V.t)
        : Inst :=
        subInst I (NSet.union (slotTargets I p) (peerNamesAt I (snd m, u)))
          (ownDependencies I p) (ownPeerDependencies I (snd m, u)).

      Theorem dependees_lookupInt : forall I k v m u,
          dependees (peerSubInst I (snd k, v) m u)
            (Nm.Intermediate k v m, Vs.Orig u) =
          dependees I (Nm.Intermediate k v m, Vs.Orig u).
      Proof.
        intros I k v m u; cbn [dependees]; f_equal.
        unfold peerEdgesAt, base; cbn [fst snd].
        pose proof (ownDependencies_id I (snd k, v)) as Hd.
        assert (Hpr :
                  peerDependenciesAt (peerSubInst I (snd k, v) m u)
                    (snd m, u) = peerDependenciesAt I (snd m, u)).
        { unfold peerSubInst, peerDependenciesAt; cbn [inst_peer subInst].
          apply ownPeerDependencies_id. }
        assert (Hn : forall r, In r (peerDependenciesAt I (snd m, u)) ->
                   NSet.In (snd (slotKey I (snd k, v) (p_name r)))
                     (NSet.union (slotTargets I (snd k, v))
                        (peerNamesAt I (snd m, u)))).
        { intros r Hr; unfold slotKey.
          destruct (slotOf I (snd k, v) (p_name r)) as [d |] eqn:Hd2.
          - cbn [snd]; apply NSet.union_spec; left.
            apply slotTargets_spec; exact (proj1 (findDepL_some _ _ _ Hd2)).
          - cbn [snd]; apply NSet.union_spec; right; unfold peerNamesAt.
            apply mem_namesOfL; exists r; split; [exact Hr | reflexivity]. }
        unfold peerSubInst in Hpr |- *; unfold activePeers, peerActive.
        rewrite Hpr.
        rewrite (dirs_agree I
                   (NSet.union (slotTargets I (snd k, v))
                      (peerNamesAt I (snd m, u)))
                   (ownDependencies I (snd k, v))
                   (ownPeerDependencies I (snd m, u))
                   (snd k, v) Hd).
        unfold depsOfL; f_equal; apply map_ext_in; intros r Hr.
        apply List.filter_In in Hr; destruct Hr as [Hr _].
        unfold peerKeyAt, peerCandsAt, peerKeyAt.
        rewrite (slotKey_agree I
                   (NSet.union (slotTargets I (snd k, v))
                      (peerNamesAt I (snd m, u)))
                   (ownDependencies I (snd k, v))
                   (ownPeerDependencies I (snd m, u))
                   (snd k, v) (p_name r) Hd).
        rewrite realVersions_subInst; [reflexivity | apply Hn; exact Hr].
      Qed.

    End Lookup.

  End Reduction.

End Npm.

(* Smoke instances.  Functor bodies are checked abstractly, so some errors
   surface only at application time, and the reflexivity examples fail if
   any definition stops computing to a normal form. *)

Module NatVM <: SemverMatch Nat_as_OT.
  Definition isPre (_ : nat) : bool := false.
  Definition sameCore (a b : nat) : bool := Nat.eqb a b.
End NatVM.

Module NpmS := Npm Nat_as_OT Nat_as_OT NatVM.

Definition npmA : nat := 1.
Definition npmB : nat := 2.
Definition npmC : nat := 3.
Definition npmX : nat := 4.

Definition npmEq (v : nat) : NpmS.Range := (NpmS.COp OpEq v :: nil) :: nil.

Definition npmBetween (lo hi : nat) : NpmS.Range :=
  (NpmS.COp OpGe lo :: NpmS.COp OpLt hi :: nil) :: nil.

Definition npmRepo : NpmS.RepoSet.t :=
  fold_right NpmS.RepoSet.add NpmS.RepoSet.empty
    ((npmA, 1) :: (npmB, 1) :: (npmC, 1) :: (npmC, 2) :: (npmC, 3) :: nil).

Definition npmDepB : NpmS.Dependency := NpmS.MkDep npmB npmB (npmEq 1) false.
Definition npmDepC : NpmS.Dependency :=
  NpmS.MkDep npmC npmC (npmBetween 2 4) false.
Definition npmPeerC : NpmS.PeerDependency :=
  NpmS.MkPeer npmC (npmBetween 1 3) false.
Definition npmPeerCOpt : NpmS.PeerDependency :=
  NpmS.MkPeer npmC (npmBetween 1 3) true.

Definition kA : NpmS.NKey.t := (npmA, npmA).
Definition kB : NpmS.NKey.t := (npmB, npmB).
Definition kC : NpmS.NKey.t := (npmC, npmC).
Definition kX : NpmS.NKey.t := (npmX, npmC).

Definition npmShow (h : NpmS.T.Dependees.t)
  : NpmS.Nm.t * list NpmS.Vs.t :=
  (fst h, NpmS.T.VSet.elements (snd h)).

Definition npmDeps (I : NpmS.Inst) (s : NpmS.T.Pkg.t) :=
  List.map npmShow
    (NpmS.T.DependeesSet.elements (NpmS.Reduction.dependees I s)).

Definition npmInst : NpmS.Inst :=
  NpmS.MkInst npmRepo
    (((npmA, 1), npmDepB) :: ((npmA, 1), npmDepC) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstAuto : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstRootPeer : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil)
    (((npmA, 1), npmPeerC) :: nil) nil (npmA, 1).

Definition npmInstRootPeerOpt : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil)
    (((npmA, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmInstRootPeerOptBare : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmA, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmInstOpt : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), npmPeerCOpt) :: nil) nil (npmA, 1).

Definition npmDepAlias : NpmS.Dependency :=
  NpmS.MkDep npmX npmC (npmEq 1) false.

Definition npmInstAlias : NpmS.Inst :=
  NpmS.MkInst npmRepo
    (((npmA, 1), npmDepC) :: ((npmA, 1), npmDepAlias) :: nil)
    nil nil (npmA, 1).

Definition npmInstOvr : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil) nil
    ((npmC, npmEq 3) :: nil) (npmA, 1).

Example npm_versions_computes :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmInst (NpmS.Nm.Granular kC 2))
  = NpmS.Vs.Orig 2 :: nil.
Proof. reflexivity. Qed.

Example npm_entry_edges_computes :
  npmDeps npmInst (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_slot_versions_computes :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmInst (NpmS.Nm.Intermediate kA 1 kC))
  = NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil.
Proof. reflexivity. Qed.

Example npm_peer_edge_computes :
  npmDeps npmInst (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Granular kB 1, NpmS.Vs.Orig 1 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_auto_versions_computes :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmInstAuto
       (NpmS.Nm.Intermediate kA 1 kC))
  = NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil.
Proof. reflexivity. Qed.

Example npm_auto_edge_computes :
  npmDeps npmInstAuto (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Granular kB 1, NpmS.Vs.Orig 1 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_optional_edge_computes :
  npmDeps npmInstOpt (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Granular kB 1, NpmS.Vs.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_root_peer_computes :
  npmDeps npmInstRootPeer (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kC, NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_root_peer_optional_computes :
  npmDeps npmInstRootPeerOpt (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = npmDeps npmInstRootPeer (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1).
Proof. reflexivity. Qed.

Example npm_root_peer_optional_bare_computes :
  npmDeps npmInstRootPeerOptBare (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_alias_computes :
  npmDeps npmInstAlias (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kC,
     NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kX, NpmS.Vs.Orig 1 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_override_computes :
  npmDeps npmInstOvr (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kC, NpmS.Vs.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

Module NatVMPre <: SemverMatch Nat_as_OT.
  Definition isPre (v : nat) : bool := Nat.odd v.
  Definition sameCore (a b : nat) : bool :=
    Nat.eqb (Nat.div a 2) (Nat.div b 2).
End NatVMPre.

Module NpmP := Npm Nat_as_OT Nat_as_OT NatVMPre.

Definition npmPreRepo : NpmP.RepoSet.t :=
  fold_right NpmP.RepoSet.add NpmP.RepoSet.empty
    ((npmC, 4) :: (npmC, 5) :: (npmC, 6) :: (npmC, 7) :: nil).

Example npm_prerelease_excluded :
  NpmP.VSet.elements
    (NpmP.rangeEval ((NpmP.COp OpGe 4 :: NpmP.COp OpLt 8 :: nil) :: nil)
       (NpmP.realVersions npmPreRepo npmC)) = 4 :: 6 :: nil.
Proof. reflexivity. Qed.

Example npm_prerelease_admitted :
  NpmP.VSet.elements
    (NpmP.rangeEval ((NpmP.COp OpGe 5 :: NpmP.COp OpLt 8 :: nil) :: nil)
       (NpmP.realVersions npmPreRepo npmC)) = 5 :: 6 :: nil.
Proof. reflexivity. Qed.
