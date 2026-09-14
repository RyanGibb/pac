From Stdlib Require Import MSets List Bool.
From PackageCalculus Require Import Prelude Core Versions Semver Concurrent.

(* npm's dependency semantics over the concurrent calculus at per-version
   granularity: nested node_modules is concurrency with g = id, and this
   file owns its peer encoding rather than reusing PeerDependency, whose
   guard is npm's --legacy-peer-deps rule.  Both npm flavours are here: a
   mandatory peer is installed beside its declarer by an edge leaving the
   declarer's own intermediate node, so the install is conditioned on that
   dependee version actually being selected; an optional peer keeps the
   legacy guard and only constrains a directory the depender fills itself.
   Nothing installs the root, so the root's own peers are the same pair of
   rules anchored at its granular node instead of at a parent.
   Ranges stay formulas evaluated by the translation, and engines/os/cpu
   gate repository membership rather than individual edges.  Source names
   are pairs (directory key, registry name): an npm node is a directory,
   and the parent relation is over source packages, so two aliases of one
   registry package under one depender are only distinguishable if the key
   is part of the name. *)

Module Npm (N V X Y : UsualOrderedType) (PM : SemverMatch V).
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
  Module SOrr := SetOps RPkg RPkg RepoSet RepoSet.
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

  (* npm's ranges are the shared semver language with nothing added, so
     they are included under their own names rather than qualified. *)
  Module Sv := Semver V VSet PM.
  Include Sv.

  Definition Valuation : Type := X.t -> option Y.t.

  Inductive Gate : Type :=
  | GTrue
  | GFalse
  | GCmp (op : CmpOp) (x : X.t) (y : Y.t)
  | GAnd (a b : Gate)
  | GOr (a b : Gate)
  | GNot (a : Gate).

  (* An unset platform variable fails its comparison: this models
     engine-strict, under which npm refuses a package whose engines, os
     or cpu it cannot satisfy. *)
  Fixpoint gateEval (rho : Valuation) (g : Gate) : bool :=
    match g with
    | GTrue => true
    | GFalse => false
    | GCmp op x y =>
        match rho x with
        | Some w => cmpOpEvalBy Y.compare op w y
        | None => false
        end
    | GAnd a b => andb (gateEval rho a) (gateEval rho b)
    | GOr a b => orb (gateEval rho a) (gateEval rho b)
    | GNot a => negb (gateEval rho a)
    end.

  Record DepRow : Type := MkDep
    { d_dir : N.t
    ; d_target : N.t
    ; d_range : Range
    ; d_dev : bool }.

  Record PeerRow : Type := MkPeer
    { p_name : N.t
    ; p_range : Range
    ; p_optional : bool }.

  (* Row-valued fields are lists: they feed only the spec and the
     translation, and sets would demand comparators for Range and Gate
     used nowhere.  optionalDependencies are absent rather than inert --
     use-if-present is a post-resolution decision, not a constraint --
     and bundledDependencies are placement. *)
  Record Inst : Type := MkInst
    { inst_repo : RepoSet.t
    ; inst_dep : list (RPkg.t * DepRow)
    ; inst_peer : list (RPkg.t * PeerRow)
    ; inst_plat : list (RPkg.t * Gate)
    ; inst_ovr : list (N.t * Range)
    ; inst_root : RPkg.t }.

  Definition ownRows {A : Type} (l : list (RPkg.t * A)) (p : RPkg.t)
    : list A :=
    fold_right
      (fun q acc => if RPkgEqb.eqb (fst q) p then snd q :: acc else acc)
      nil l.

  Lemma in_ownRows : forall (A : Type) (l : list (RPkg.t * A)) p a,
      In a (ownRows l p) <-> In (p, a) l.
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

  Lemma ownRows_filter : forall (A : Type) (l : list (RPkg.t * A)) f p,
      (forall a, In (p, a) l -> f (p, a) = true) ->
      ownRows (List.filter f l) p = ownRows l p.
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

  Definition platOK (rho : Valuation) (I : Inst) (p : RPkg.t) : Prop :=
    forall g, In (p, g) (inst_plat I) -> gateEval rho g = true.

  Definition platOKb (rho : Valuation) (I : Inst) (p : RPkg.t) : bool :=
    forallb (gateEval rho) (ownRows (inst_plat I) p).

  Lemma platOKb_iff : forall rho I p,
      platOKb rho I p = true <-> platOK rho I p.
  Proof.
    intros rho I p; unfold platOKb, platOK; rewrite forallb_forall.
    split; intros H g Hg; apply H, in_ownRows; exact Hg.
  Qed.

  (* The packages some gate of theirs rejects, collected in one pass over
     the gate rows.  Asking platOKb once per candidate instead would scan
     every row for every candidate, which is quadratic wherever a package
     gates all of its own versions -- the common case, since a package
     that declares engines declares them throughout its history. *)
  Definition badPkgs (rho : Valuation) (I : Inst) : RepoSet.t :=
    fold_right
      (fun q acc =>
         if gateEval rho (snd q) then acc else RepoSet.add (fst q) acc)
      RepoSet.empty (inst_plat I).

  Lemma mem_badPkgs : forall rho I p,
      RepoSet.In p (badPkgs rho I) <->
      exists g, In (p, g) (inst_plat I) /\ gateEval rho g = false.
  Proof.
    intros rho I p; unfold badPkgs.
    induction (inst_plat I) as [| [q g] l IH]; cbn [fold_right fst snd].
    - split; [intro H; destruct (SOrr.empty_in _ H) | intros [g [[] _]]].
    - destruct (gateEval rho g) eqn:Hg.
      + split.
        * intro H; apply IH in H; destruct H as [g0 [H1 H2]].
          exists g0; split; [right; exact H1 | exact H2].
        * intros [g0 [[He | H1] H2]];
            [exfalso; congruence
            | apply IH; exists g0; split; assumption].
      + split.
        * intro H; apply SOrr.add_in in H; destruct H as [He | H].
          -- exists g; split; [left; rewrite He; reflexivity | exact Hg].
          -- apply IH in H; destruct H as [g0 [H1 H2]].
             exists g0; split; [right; exact H1 | exact H2].
        * intros [g0 [[He | H1] H2]]; apply SOrr.add_in.
          -- injection He as Hq _; left; symmetry; exact Hq.
          -- right; apply IH; exists g0; split; assumption.
  Qed.

  (* engines/os/cpu gate repository membership, not individual edges:
     they are properties of a package against a fixed environment, never
     solved for, so they cut R the way opam's available: does. *)
  Definition effRepo (rho : Valuation) (I : Inst) : RepoSet.t :=
    RepoSet.diff (inst_repo I) (badPkgs rho I).

  Lemma mem_effRepo : forall rho I p,
      RepoSet.In p (effRepo rho I) <->
      RepoSet.In p (inst_repo I) /\ platOKb rho I p = true.
  Proof.
    intros rho I p; unfold effRepo; rewrite RepoSet.diff_spec.
    split; intros [H1 H2]; split; try exact H1.
    - apply platOKb_iff; intros g Hg.
      destruct (gateEval rho g) eqn:He; [reflexivity | exfalso].
      apply H2, mem_badPkgs; exists g; split; assumption.
    - intro Hc; apply mem_badPkgs in Hc; destruct Hc as [g [Hg He]].
      apply platOKb_iff in H2; rewrite (H2 g Hg) in He; discriminate.
  Qed.

  Fixpoint lookupOvr (l : list (N.t * Range)) (n : N.t) : option Range :=
    match l with
    | nil => None
    | (m, rg) :: l' => if NEqb.eqb m n then Some rg else lookupOvr l' n
    end.

  (* A flat override replaces the declared range wherever the name is
     depended on.  Path-scoped overrides are indexed by the parent chain,
     which is an output of resolution, so they cannot be a static row. *)
  Definition override (I : Inst) (n : N.t) (rg : Range) : Range :=
    match lookupOvr (inst_ovr I) n with
    | Some rg' => rg'
    | None => rg
    end.

  (* devDependencies participate only from the root package. *)
  Definition depActive (I : Inst) (p : RPkg.t) (d : DepRow) : bool :=
    orb (negb (d_dev d)) (RPkgEqb.eqb p (inst_root I)).

  Definition depRows (I : Inst) (p : RPkg.t) : list DepRow :=
    List.filter (depActive I p) (ownRows (inst_dep I) p).

  Fixpoint findDepL (l : list DepRow) (a : N.t) : option DepRow :=
    match l with
    | nil => None
    | d :: l' => if NEqb.eqb (d_dir d) a then Some d else findDepL l' a
    end.

  (* A slot is a directory a package declares a dependency for; duplicate
     manifest keys cannot occur, so the first row wins and the lookup is
     a total function of the key. *)
  Definition slotOf (I : Inst) (p : RPkg.t) (a : N.t) : option DepRow :=
    findDepL (depRows I p) a.

  Definition dirs (I : Inst) (p : RPkg.t) : NSet.t :=
    namesOfL d_dir (depRows I p).

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

  Lemma dirs_slotOf : forall I p a,
      NSet.In a (dirs I p) -> exists d, slotOf I p a = Some d.
  Proof.
    intros I p a Ha; unfold dirs in Ha; apply mem_namesOfL in Ha.
    destruct Ha as [d [Hd Hal]]; unfold slotOf.
    destruct (findDepL (depRows I p) a) as [e |] eqn:He;
      [exists e; reflexivity |].
    exfalso; exact (findDepL_none _ _ He d Hd Hal).
  Qed.

  Lemma slotOf_dirs : forall I p a d,
      slotOf I p a = Some d -> NSet.In a (dirs I p).
  Proof.
    intros I p a d Hd; unfold slotOf in Hd.
    destruct (findDepL_some _ _ _ Hd) as [H1 H2].
    unfold dirs; apply mem_namesOfL; exists d; split; assumption.
  Qed.

  (* The source name a package installs under one of its directory keys:
     the key together with the registry package it points at, which the
     key alone does not determine under "npm:" aliasing. *)
  Definition slotKey (I : Inst) (p : RPkg.t) (a : N.t) : NKey.t :=
    match slotOf I p a with
    | Some d => (a, d_target d)
    | None => (a, a)
    end.

  Lemma slotKey_fst : forall I p a, fst (slotKey I p a) = a.
  Proof. intros I p a; unfold slotKey; destruct (slotOf I p a); reflexivity.
  Qed.

  Definition slotCands (rho : Valuation) (I : Inst) (p : RPkg.t) (a : N.t)
    : VSet.t :=
    match slotOf I p a with
    | Some d => rangeEval (override I (d_target d) (d_range d))
                  (realVersions (effRepo rho I) (d_target d))
    | None => VSet.empty
    end.

  Lemma slotCands_real : forall rho I p a v,
      VSet.In v (slotCands rho I p a) ->
      RepoSet.In (snd (slotKey I p a), v) (effRepo rho I).
  Proof.
    intros rho I p a v Hv; unfold slotCands, slotKey in *.
    destruct (slotOf I p a) as [d |]; [| destruct (SOrv.empty_in _ Hv)].
    apply mem_rangeEval in Hv; destruct Hv as [Hv _]; simpl.
    apply mem_realVersions; exact Hv.
  Qed.

  Definition peerRowsAt (I : Inst) (p : RPkg.t) : list PeerRow :=
    ownRows (inst_peer I) p.

  (* A peer names a directory, so it lands on whatever key the depender
     already uses for that directory, aliased or not. *)
  Definition peerKeyAt (I : Inst) (p : RPkg.t) (r : PeerRow) : NKey.t :=
    slotKey I p (p_name r).

  Definition peerCandsAt (rho : Valuation) (I : Inst) (p : RPkg.t)
      (r : PeerRow) : VSet.t :=
    rangeEval (p_range r)
      (realVersions (effRepo rho I) (snd (peerKeyAt I p r))).

  (* A mandatory peer is installed beside its declarer whatever the
     depender declares; an optional one keeps npm's legacy rule and only
     constrains a directory the depender fills itself. *)
  Definition peerActive (I : Inst) (p : RPkg.t) (r : PeerRow) : bool :=
    orb (negb (p_optional r)) (NSet.mem (p_name r) (dirs I p)).

  Definition activePeers (I : Inst) (p : RPkg.t) (q : RPkg.t)
    : list PeerRow :=
    List.filter (peerActive I p) (peerRowsAt I q).

  (* Every directory a peer could ask for.  Minting the real set from the
     whole instance rather than from a package's own candidates is what
     makes peers transitive -- an auto-installed peer declares peers of
     its own -- and over-minting is harmless: only an edge forces an
     install, and those edges leave the declaring dependee's own
     intermediate node. *)
  Definition peerDirs (I : Inst) : NSet.t :=
    namesOfL (fun q => p_name (snd q)) (inst_peer I).

  Definition childDirs (I : Inst) (p : RPkg.t) : NSet.t :=
    NSet.union (dirs I p) (peerDirs I).

  Definition childKeys (I : Inst) (p : RPkg.t) : KeySet.t :=
    SOnk.map (slotKey I p) (childDirs I p).

  (* The versions a package may install under a child key: its own
     dependency range when it declares one, else -- for a key only a peer
     asks for -- every version of that package, which the peer edges then
     narrow. *)
  Definition childCands (rho : Valuation) (I : Inst) (p : RPkg.t)
      (m : NKey.t) : VSet.t :=
    if KeyEqb.eqb m (slotKey I p (fst m))
    then if NSet.mem (fst m) (dirs I p)
         then slotCands rho I p (fst m)
         else if NSet.mem (fst m) (peerDirs I)
              then realVersions (effRepo rho I) (snd m)
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

  (* The directory keys the instance can mint: the root's own, every
     dependency row's, and every peer row's. *)
  Definition keysOf (I : Inst) : KeySet.t :=
    KeySet.add (rootKey I)
      (KeySet.union
         (keysOfL (fun q => (d_dir (snd q), d_target (snd q)))
            (inst_dep I))
         (keysOfL (fun q => (p_name (snd q), p_name (snd q)))
            (inst_peer I))).

  Definition Available (rho : Valuation) (I : Inst) (q : Pkg.t) : Prop :=
    KeySet.In (fst q) (keysOf I) /\ RepoSet.In (base q) (effRepo rho I).

  Definition realPkgs (rho : Valuation) (I : Inst) : PkgSet.t :=
    SOkp.unionMap (fun k =>
        SOvp.map (fun v => (k, v)) (realVersions (effRepo rho I) (snd k)))
      (keysOf I).

  Lemma mem_realPkgs : forall rho I q,
      PkgSet.In q (realPkgs rho I) <-> Available rho I q.
  Proof.
    intros rho I [k v]; unfold realPkgs, Available, base; simpl.
    rewrite SOkp.mem_unionMap; split.
    - intros [k0 [Hk0 Hm]]; apply SOvp.mem_map in Hm.
      destruct Hm as [u [Hu He]].
      assert (k0 = k) by congruence; assert (u = v) by congruence.
      subst k0 u; split; [exact Hk0 | apply mem_realVersions; exact Hu].
    - intros [Hk Hb]; exists k; split; [exact Hk |].
      apply SOvp.mem_map; exists v; split;
        [apply mem_realVersions; exact Hb | reflexivity].
  Qed.

  (* p installs version v under its directory key m.  The key carries the
     registry name, so two aliases of one package stay apart. *)
  Definition Installs (S : PkgSet.t) (pi : Conc.ParentRel.t)
      (p : Pkg.t) (m : NKey.t) (v : V.t) : Prop :=
    PkgSet.In (m, v) S /\ Conc.ParentRel.In ((m, v), p) pi.

  (* S is the set of installed copies and pi is npm's node_modules
     nesting.  There is no version-uniqueness field: g is the identity,
     so any number of versions of a package may coexist; what is unique
     is the version a given depender installs under a given key. *)
  Record IsResolution (rho : Valuation) (I : Inst)
      (S : PkgSet.t) (pi : Conc.ParentRel.t) : Prop :=
    { nres_subset : forall q, PkgSet.In q S -> Available rho I q
    ; nres_root : PkgSet.In (rootPkg I) S
    ; nres_unique :
        forall p m v v', Installs S pi p m v -> Installs S pi p m v' -> v = v'
    ; nres_slot :
        forall p, PkgSet.In p S ->
        forall a, NSet.In a (dirs I (base p)) ->
        exists v, VSet.In v (slotCands rho I (base p) a) /\
          Installs S pi p (slotKey I (base p) a) v
      (* A mandatory peer of anything p installs is installed by p too,
         beside its declarer, at a version the peer range admits. *)
    ; nres_peer_install :
        forall p, PkgSet.In p S ->
        forall m u, Installs S pi p m u ->
        forall r, In ((snd m, u), r) (inst_peer I) ->
          p_optional r = false ->
        exists v, VSet.In v (peerCandsAt rho I (base p) r) /\
          Installs S pi p (peerKeyAt I (base p) r) v
      (* An optional peer forces nothing; it constrains only a directory
         p fills itself -- npm's legacy rule, which is what
         peerDependenciesMeta.optional means. *)
    ; nres_peer_match :
        forall p, PkgSet.In p S ->
        forall m u, Installs S pi p m u ->
        forall r, In ((snd m, u), r) (inst_peer I) ->
          p_optional r = true ->
          NSet.In (p_name r) (dirs I (base p)) ->
        forall v, Installs S pi p (peerKeyAt I (base p) r) v ->
          VSet.In v (peerCandsAt rho I (base p) r)
      (* Nothing installs the root, so the two clauses above never range
         over it; npm 7+ nevertheless installs the root project's own
         mandatory peers into the root's node_modules, and these two say
         so.  They are the same pair anchored at the root: the mandatory
         one forces the install, the optional one only narrows a
         directory the root fills itself. *)
    ; nres_root_peer :
        forall r, In (inst_root I, r) (inst_peer I) ->
          p_optional r = false ->
        exists v, VSet.In v (peerCandsAt rho I (inst_root I) r) /\
          Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) v
    ; nres_root_peer_match :
        forall r, In (inst_root I, r) (inst_peer I) ->
          p_optional r = true ->
          NSet.In (p_name r) (dirs I (inst_root I)) ->
        forall v, Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) v ->
          VSet.In v (peerCandsAt rho I (inst_root I) r)
    ; nres_parents :
        forall c q, Conc.ParentRel.In (c, q) pi ->
          PkgSet.In c S /\ PkgSet.In q S }.

  Module Reduction.

    (* npm duplicates freely, so the granularity is the identity and every
       installed copy is its own core name. *)
    Definition idg (v : V.t) : V.t := v.

    (* -- the per-query lookups: these are the definitions, and the global
       translation below is their aggregation -- *)

    (* THE per-name version lookup. *)
    Definition versions (rho : Valuation) (I : Inst) (nm : Nm.t) : T.VSet.t :=
      match nm with
      | Nm.Granular k w =>
          if PkgSet.mem (k, w) (realPkgs rho I)
          then T.VSet.singleton (Vs.Orig w)
          else T.VSet.empty
      | Nm.Intermediate k v m =>
          Conc.Reduction.embedVS (childCands rho I (snd k, v) m)
      end.

    Definition entryEdges (rho : Valuation) (I : Inst) (q : Pkg.t)
      : T.DependeesSet.t :=
      depsOfL (fun a =>
          (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
           Conc.Reduction.embedVS (slotCands rho I (base q) a)))
        (NSet.elements (dirs I (base q))).

    (* The root's own peers have no parent to hang off, so their edges
       leave the root's granular node instead of a parent's intermediate
       one.  The filter is the same peerActive, so a mandatory root peer
       is installed and an optional one only narrows a directory the root
       fills itself; the key is the same peerKeyAt, so a name the root
       also depends on gets one edge kind, narrowed by both ranges. *)
    Definition rootPeerEdges (rho : Valuation) (I : Inst) (q : Pkg.t)
      : T.DependeesSet.t :=
      if PkgEqb.eqb q (rootPkg I)
      then depsOfL (fun r =>
               (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
                Conc.Reduction.embedVS (peerCandsAt rho I (base q) r)))
             (activePeers I (base q) (base q))
      else T.DependeesSet.empty.

    (* The peer edges leave the dependee's own intermediate node, so a
       mandatory peer is forced only for the dependee version actually
       selected -- npm 7+ auto-installation, conditioned on the choice. *)
    Definition peerEdgesAt (rho : Valuation) (I : Inst) (q : Pkg.t)
        (m : NKey.t) (u : V.t) : T.DependeesSet.t :=
      depsOfL (fun r =>
          (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
           Conc.Reduction.embedVS (peerCandsAt rho I (base q) r)))
        (activePeers I (base q) (snd m, u)).

    (* THE per-package dependency lookup. *)
    Definition dependees (rho : Valuation) (I : Inst) (s : T.Pkg.t)
      : T.DependeesSet.t :=
      match s with
      | (Nm.Granular k w, Vs.Orig v) =>
          if VEqb.eqb w v
          then T.DependeesSet.union (entryEdges rho I (k, v))
                 (rootPeerEdges rho I (k, v))
          else T.DependeesSet.empty
      | (Nm.Intermediate k v m, Vs.Orig u) =>
          T.DependeesSet.add (Nm.Granular m u, T.VSet.singleton (Vs.Orig u))
            (peerEdgesAt rho I (k, v) m u)
      | _ => T.DependeesSet.empty
      end.

    Lemma mem_entryEdges : forall rho I q h,
        T.DependeesSet.In h (entryEdges rho I q) <->
        exists a, NSet.In a (dirs I (base q)) /\
          h = (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
               Conc.Reduction.embedVS (slotCands rho I (base q) a)).
    Proof.
      intros rho I q h; unfold entryEdges; rewrite mem_depsOfL.
      split; intros [a [Ha He]]; exists a; split;
        try (apply SOnn.elements_in; exact Ha);
        try (apply SOnn.elements_in in Ha; exact Ha);
        [symmetry; exact He | symmetry; exact He].
    Qed.

    Lemma mem_rootPeerEdges : forall rho I q h,
        T.DependeesSet.In h (rootPeerEdges rho I q) <->
        q = rootPkg I /\
        exists r, In (base q, r) (inst_peer I) /\
          peerActive I (base q) r = true /\
          h = (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
               Conc.Reduction.embedVS (peerCandsAt rho I (base q) r)).
    Proof.
      intros rho I q h; unfold rootPeerEdges.
      destruct (PkgEqb.eqb q (rootPkg I)) eqn:Hq.
      - apply PkgEqb.eqb_true_iff in Hq.
        rewrite mem_depsOfL; unfold activePeers, peerRowsAt; split.
        + intros [r [Hr He]]; apply List.filter_In in Hr.
          destruct Hr as [Hr Hact]; split; [exact Hq |].
          exists r; split; [apply in_ownRows; exact Hr |].
          split; [exact Hact | symmetry; exact He].
        + intros [_ [r [Hr [Hact He]]]]; exists r; split;
            [| symmetry; exact He].
          apply List.filter_In; split;
            [apply in_ownRows; exact Hr | exact Hact].
      - split; [intro H; destruct (SOhh.empty_in _ H) |].
        intros [He _]; subst q; rewrite PkgEqb.eqb_refl in Hq; discriminate.
    Qed.

    Lemma mem_peerEdgesAt : forall rho I q m u h,
        T.DependeesSet.In h (peerEdgesAt rho I q m u) <->
        exists r, In ((snd m, u), r) (inst_peer I) /\
          peerActive I (base q) r = true /\
          h = (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
               Conc.Reduction.embedVS (peerCandsAt rho I (base q) r)).
    Proof.
      intros rho I q m u h; unfold peerEdgesAt; rewrite mem_depsOfL.
      unfold activePeers, peerRowsAt; split.
      - intros [r [Hr He]]; apply List.filter_In in Hr.
        destruct Hr as [Hr Hact]; exists r.
        split; [apply in_ownRows; exact Hr | split; [exact Hact |]].
        symmetry; exact He.
      - intros [r [Hr [Hact He]]]; exists r; split; [| symmetry; exact He].
        apply List.filter_In; split;
          [apply in_ownRows; exact Hr | exact Hact].
    Qed.

    (* -- the global translation: an aggregation of the lookups -- *)

    (* Over-minting is harmless: a name no edge reaches contributes an
       inert package, and the per-name versions above are empty for a key
       nothing asks for. *)
    Definition targetNames (rho : Valuation) (I : Inst) : NmSet.t :=
      NmSet.union
        (SOpn.map (fun q => Nm.Granular (fst q) (snd q)) (realPkgs rho I))
        (SOpn.unionMap (fun q =>
             SOnm.map (fun m => Nm.Intermediate (fst q) (snd q) m)
               (childKeys I (base q)))
           (realPkgs rho I)).

    Definition transR (rho : Valuation) (I : Inst) : T.PkgSet.t :=
      SOmt.unionMap
        (fun nm => SOwt.map (fun x => (nm, x)) (versions rho I nm))
        (targetNames rho I).

    Lemma mem_transR : forall rho I nm x,
        T.PkgSet.In (nm, x) (transR rho I) <->
        NmSet.In nm (targetNames rho I) /\ T.VSet.In x (versions rho I nm).
    Proof.
      intros rho I nm x; unfold transR; rewrite SOmt.mem_unionMap; split.
      - intros [nm0 [Hnm Hm]]; apply SOwt.mem_map in Hm.
        destruct Hm as [x0 [Hx He]].
        assert (nm0 = nm) by congruence; assert (x0 = x) by congruence.
        subst nm0 x0; split; assumption.
      - intros [Hnm Hx]; exists nm; split; [exact Hnm |].
        apply SOwt.mem_map; exists x; split; [exact Hx | reflexivity].
    Qed.

    Definition depEdges (s : T.Pkg.t) (hs : T.DependeesSet.t) : T.DepRel.t :=
      SOhd.map (fun h => (s, h)) hs.

    Definition transD (rho : Valuation) (I : Inst) : T.DepRel.t :=
      SOqd.unionMap (fun s => depEdges s (dependees rho I s)) (transR rho I).

    Lemma mem_transD : forall rho I s h,
        T.DepRel.In (s, h) (transD rho I) <->
        T.PkgSet.In s (transR rho I) /\
        T.DependeesSet.In h (dependees rho I s).
    Proof.
      intros rho I s h; unfold transD; rewrite SOqd.mem_unionMap; split.
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

    (* -- soundness -- *)

    Definition npmResolution (S : T.PkgSet.t) : PkgSet.t :=
      Conc.Reduction.concurrentResolution idg S.

    (* The nesting is read straight off the selected intermediates: each
       one is a directory of its owner holding one chosen version. *)
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
      - intros [[nm x] [Hs He]]; destruct nm as [k' w | k' v' m'];
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

    Lemma dependees_embedPkg : forall rho I q,
        dependees rho I (Conc.Reduction.embedPkg idg q) =
        T.DependeesSet.union (entryEdges rho I q) (rootPeerEdges rho I q).
    Proof.
      intros rho I [k v]; unfold Conc.Reduction.embedPkg, idg; cbn [fst snd].
      cbn [dependees]; rewrite VEqb.eqb_refl; reflexivity.
    Qed.

    (* Every selected intermediate drags its chosen version in: the exit
       edge is the only edge a directory node carries unconditionally. *)
    Lemma exit_selected : forall rho I S k v m u,
        T.IsResolution (transR rho I) (transD rho I) (transRoot I) S ->
        T.PkgSet.In (Nm.Intermediate k v m, Vs.Orig u) S ->
        T.PkgSet.In (Conc.Reduction.embedPkg idg (m, u)) S.
    Proof.
      intros rho I S k v m u [Hsub Hroot Hdep Huniq] Hin.
      destruct (Hdep _ Hin (Nm.Granular m u) (T.VSet.singleton (Vs.Orig u)))
        as [x [Hx HxS]].
      { apply mem_transD; split; [exact (Hsub _ Hin) |].
        cbn [dependees]; apply SOhh.add_in; left; reflexivity. }
      apply SOvcv.singleton_in in Hx; subst x.
      unfold Conc.Reduction.embedPkg, idg; cbn [fst snd]; exact HxS.
    Qed.

    Lemma entry_selected : forall rho I S q a,
        T.IsResolution (transR rho I) (transD rho I) (transRoot I) S ->
        T.PkgSet.In (Conc.Reduction.embedPkg idg q) S ->
        NSet.In a (dirs I (base q)) ->
        exists v, VSet.In v (slotCands rho I (base q) a) /\
          T.PkgSet.In
            (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a),
             Vs.Orig v) S.
    Proof.
      intros rho I S q a [Hsub Hroot Hdep Huniq] Hq Ha.
      destruct (Hdep _ Hq
                  (Nm.Intermediate (fst q) (snd q) (slotKey I (base q) a))
                  (Conc.Reduction.embedVS (slotCands rho I (base q) a)))
        as [x [Hx HxS]].
      { apply mem_transD; split; [exact (Hsub _ Hq) |].
        rewrite dependees_embedPkg.
        apply T.DependeesSet.union_spec; left; apply mem_entryEdges.
        exists a; split; [exact Ha | reflexivity]. }
      apply SOvcv.mem_map in Hx; destruct Hx as [v [Hv ->]].
      exists v; split; assumption.
    Qed.

    (* The root's peer edge leaves the root's own granular node, which is
       in every resolution, so a mandatory root peer is always forced. *)
    Lemma root_peer_selected : forall rho I S r,
        T.IsResolution (transR rho I) (transD rho I) (transRoot I) S ->
        In (inst_root I, r) (inst_peer I) ->
        peerActive I (inst_root I) r = true ->
        exists v, VSet.In v (peerCandsAt rho I (inst_root I) r) /\
          T.PkgSet.In
            (Nm.Intermediate (fst (rootPkg I)) (snd (rootPkg I))
               (peerKeyAt I (inst_root I) r), Vs.Orig v) S.
    Proof.
      intros rho I S r [Hsub Hroot Hdep Huniq] Hr Hact.
      destruct (Hdep _ Hroot
                  (Nm.Intermediate (fst (rootPkg I)) (snd (rootPkg I))
                     (peerKeyAt I (inst_root I) r))
                  (Conc.Reduction.embedVS
                     (peerCandsAt rho I (inst_root I) r)))
        as [x [Hx HxS]].
      { apply mem_transD; split; [exact (Hsub _ Hroot) |].
        unfold transRoot; rewrite dependees_embedPkg.
        apply T.DependeesSet.union_spec; right; apply mem_rootPeerEdges.
        split; [reflexivity |]; rewrite base_rootPkg.
        exists r; split; [exact Hr | split; [exact Hact | reflexivity]]. }
      apply SOvcv.mem_map in Hx; destruct Hx as [v [Hv ->]].
      exists v; split; assumption.
    Qed.

    Lemma peer_selected : forall rho I S q m u r,
        T.IsResolution (transR rho I) (transD rho I) (transRoot I) S ->
        T.PkgSet.In (Nm.Intermediate (fst q) (snd q) m, Vs.Orig u) S ->
        In ((snd m, u), r) (inst_peer I) ->
        peerActive I (base q) r = true ->
        exists v, VSet.In v (peerCandsAt rho I (base q) r) /\
          T.PkgSet.In
            (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r),
             Vs.Orig v) S.
    Proof.
      intros rho I S q m u r [Hsub Hroot Hdep Huniq] Hin Hr Hact.
      destruct (Hdep _ Hin
                  (Nm.Intermediate (fst q) (snd q) (peerKeyAt I (base q) r))
                  (Conc.Reduction.embedVS (peerCandsAt rho I (base q) r)))
        as [x [Hx HxS]].
      { apply mem_transD; split; [exact (Hsub _ Hin) |].
        cbn [dependees]; apply SOhh.add_in; right.
        apply mem_peerEdgesAt; exists r; split;
          [exact Hr | split; [exact Hact | reflexivity]]. }
      apply SOvcv.mem_map in Hx; destruct Hx as [v [Hv ->]].
      exists v; split; assumption.
    Qed.

    Theorem npm_soundness : forall rho I S,
        T.IsResolution (transR rho I) (transD rho I) (transRoot I) S ->
        IsResolution rho I (npmResolution S) (npmParents S).
    Proof.
      intros rho I S Hres.
      assert (Hres' := Hres); destruct Hres' as [Hsub Hroot Hdep Huniq].
      (* the parent edges a selected intermediate contributes *)
      assert (Hpi : forall q m v,
                 T.PkgSet.In (Conc.Reduction.embedPkg idg q) S ->
                 T.PkgSet.In
                   (Nm.Intermediate (fst q) (snd q) m, Vs.Orig v) S ->
                 Installs (npmResolution S) (npmParents S) q m v).
      { intros [k w] m v Hq Hi; split.
        - apply Conc.Reduction.mem_concurrentResolution.
          exact (exit_selected rho I S k w m v Hres Hi).
        - apply mem_npmParents; cbn [fst snd]; split; assumption. }
      constructor.
      - intros [k w] Hq; apply Conc.Reduction.mem_concurrentResolution in Hq.
        pose proof (Hsub _ Hq) as Hr; apply mem_transR in Hr.
        destruct Hr as [_ Hv].
        cbn [versions Conc.Reduction.embedPkg fst snd] in Hv.
        unfold idg in Hv.
        destruct (PkgSet.mem (k, w) (realPkgs rho I)) eqn:Hm;
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
        destruct (entry_selected rho I S p a Hres Hp Ha) as [v [Hv Hi]].
        exists v; split; [exact Hv | exact (Hpi p _ v Hp Hi)].
      - intros p Hp m u [_ Hu] r Hr Hopt.
        apply Conc.Reduction.mem_concurrentResolution in Hp.
        apply mem_npmParents in Hu; destruct Hu as [Hi _];
          cbn [fst snd] in Hi.
        destruct (peer_selected rho I S p _ u r Hres Hi Hr
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
        destruct (peer_selected rho I S p _ u r Hres Hi Hr Hact)
          as [v0 [Hv0 Hj]].
        apply mem_npmParents in Hv; destruct Hv as [Hi' _];
          cbn [fst snd] in Hi'.
        pose proof (Huniq _ _ _ Hi' Hj) as Heq; injection Heq as ->; exact Hv0.
      - intros r Hr Hopt.
        destruct (root_peer_selected rho I S r Hres Hr
                    (proj2 (Bool.orb_true_iff _ _)
                       (or_introl (proj2 (Bool.negb_true_iff _) Hopt))))
          as [v [Hv Hj]].
        exists v; split; [exact Hv | exact (Hpi (rootPkg I) _ v Hroot Hj)].
      - intros r Hr Hopt Hname v [_ Hv].
        assert (Hact : peerActive I (inst_root I) r = true)
          by (unfold peerActive; apply Bool.orb_true_iff; right;
              apply NSet.mem_spec; exact Hname).
        destruct (root_peer_selected rho I S r Hres Hr Hact) as [v0 [Hv0 Hj]].
        apply mem_npmParents in Hv; destruct Hv as [Hi' _];
          cbn [fst snd] in Hi'.
        pose proof (Huniq _ _ _ Hi' Hj) as Heq; injection Heq as ->; exact Hv0.
      - intros [m u] [k w] Hcq; apply mem_npmParents in Hcq.
        cbn [fst snd] in Hcq; destruct Hcq as [Hi Hq].
        split; apply Conc.Reduction.mem_concurrentResolution;
          [exact (exit_selected rho I S k w m u Hres Hi) | exact Hq].
    Qed.

    (* -- completeness -- *)

    (* The version a depender installs under one of its keys is one the
       encoding minted there: a slot's own range when it declares one --
       pinned by the slot obligation and by uniqueness -- and otherwise
       any published version, which the peer edges narrow. *)
    Lemma installs_childCands : forall rho I S pi p m v,
        IsResolution rho I S pi -> PkgSet.In p S ->
        KeySet.In m (childKeys I (base p)) ->
        Installs S pi p m v ->
        VSet.In v (childCands rho I (base p) m).
    Proof.
      intros rho I S pi p m v Hres Hp Hm Hi.
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

    (* The two root-peer clauses read as one obligation: whichever flavour
       a root peer row has, an active one names a directory the root fills
       at a version its range admits. *)
    Lemma root_peer_installs : forall rho I S pi r,
        IsResolution rho I S pi ->
        In (inst_root I, r) (inst_peer I) ->
        peerActive I (inst_root I) r = true ->
        exists w, VSet.In w (peerCandsAt rho I (inst_root I) r) /\
          Installs S pi (rootPkg I) (peerKeyAt I (inst_root I) r) w.
    Proof.
      intros rho I S pi r Hres Hr Hact.
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

    Definition coreResolution (rho : Valuation) (I : Inst)
        (S : PkgSet.t) (pi : Conc.ParentRel.t) : T.PkgSet.t :=
      T.PkgSet.union (Conc.Reduction.embedSet idg S)
        (SOpt.unionMap (fun p =>
             SOkt.unionMap (fun m =>
                 SOvt.filterMap (instNode S pi p m)
                   (realVersions (effRepo rho I) (snd m)))
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

    Lemma dependees_gran : forall rho I k v,
        dependees rho I (Nm.Granular k v, Vs.Orig v) =
        T.DependeesSet.union (entryEdges rho I (k, v))
          (rootPeerEdges rho I (k, v)).
    Proof.
      intros rho I k v; cbn [dependees]; rewrite VEqb.eqb_refl; reflexivity.
    Qed.

    Lemma mem_coreResolution : forall rho I S pi s,
        T.PkgSet.In s (coreResolution rho I S pi) <->
        (exists k v, PkgSet.In (k, v) S /\
           s = (Nm.Granular k v, Vs.Orig v)) \/
        (exists p m u, PkgSet.In p S /\ KeySet.In m (childKeys I (base p)) /\
           VSet.In u (realVersions (effRepo rho I) (snd m)) /\
           PkgSet.In (m, u) S /\ Conc.ParentRel.In ((m, u), p) pi /\
           s = (Nm.Intermediate (fst p) (snd p) m, Vs.Orig u)).
    Proof.
      intros rho I S pi s; unfold coreResolution.
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

    Lemma mem_targetNames_gran : forall rho I p,
        PkgSet.In p (realPkgs rho I) ->
        NmSet.In (Nm.Granular (fst p) (snd p)) (targetNames rho I).
    Proof.
      intros rho I p Hp; unfold targetNames; apply NmSet.union_spec; left.
      apply SOpn.mem_map; exists p; split; [exact Hp | reflexivity].
    Qed.

    Lemma mem_targetNames_int : forall rho I p m,
        PkgSet.In p (realPkgs rho I) ->
        KeySet.In m (childKeys I (base p)) ->
        NmSet.In (Nm.Intermediate (fst p) (snd p) m) (targetNames rho I).
    Proof.
      intros rho I p m Hp Hm; unfold targetNames; apply NmSet.union_spec.
      right; apply SOpn.mem_unionMap; exists p; split; [exact Hp | cbn beta].
      apply SOnm.mem_map; exists m; split; [exact Hm | reflexivity].
    Qed.

    Theorem npm_completeness : forall rho I S pi,
        IsResolution rho I S pi ->
        T.IsResolution (transR rho I) (transD rho I) (transRoot I)
          (coreResolution rho I S pi).
    Proof.
      intros rho I S pi Hres.
      assert (Hres' := Hres).
      destruct Hres' as [Hsub Hroot Huniq Hslot Hpin Hpm Hrp Hrpm Hpar].
      assert (Hreal : forall q, PkgSet.In q S -> PkgSet.In q (realPkgs rho I))
        by (intros q Hq; apply mem_realPkgs; exact (Hsub _ Hq)).
      assert (Hgran : forall k v, PkgSet.In (k, v) S ->
                 T.PkgSet.In (Nm.Granular k v, Vs.Orig v) (transR rho I)).
      { intros k v Hq; apply mem_transR; split.
        - pose proof (mem_targetNames_gran rho I (k, v) (Hreal _ Hq)) as Ht.
          cbn [fst snd] in Ht; exact Ht.
        - cbn [versions].
          assert (PkgSet.mem (k, v) (realPkgs rho I) = true) as ->
            by (apply PkgSet.mem_spec; exact (Hreal _ Hq)).
          apply SOvcv.singleton_in; reflexivity. }
      constructor.
      - intros s Hs; apply mem_coreResolution in Hs.
        destruct Hs as
          [[k [v [Hp ->]]] | [p [m [u [Hp [Hm [Hu [HS [Hpi ->]]]]]]]]];
          [exact (Hgran k v Hp) |].
        apply mem_transR; split.
        + exact (mem_targetNames_int rho I p m (Hreal _ Hp) Hm).
        + cbn [versions]; apply SOvcv.mem_map; exists u; split;
            [| reflexivity].
          exact (installs_childCands rho I S pi p m u Hres Hp Hm
                   (conj HS Hpi)).
      - apply mem_coreResolution; left.
        exists (rootKey I), (snd (inst_root I)); split;
          [exact Hroot |].
        unfold transRoot, rootPkg, Conc.Reduction.embedPkg, idg; reflexivity.
      - intros s Hs nm vs Hd.
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
               exact (slotCands_real rho I (base (k, v)) a w Hw).
          * apply mem_rootPeerEdges in Hd.
            destruct Hd as [Hq [r [Hr [Hact He]]]].
            injection He as -> ->.
            assert (Hbr : base (k, v) = inst_root I)
              by (rewrite Hq; apply base_rootPkg).
            rewrite Hbr in Hr, Hact |- *.
            destruct (root_peer_installs rho I S pi r Hres Hr Hact)
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
                       VSet.In w (peerCandsAt rho I (base (pk, pv)) r) /\
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
      - intros nm x1 x2 H1 H2.
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

    (* What the encoding buys over the guarded form: the mandatory peer of
       a dependee version that was actually selected is installed as its
       sibling, under the same depender, at a version its range admits.
       The edge that forces this leaves the dependee's own intermediate
       node, so nothing is forced for a candidate that lost. *)
    Corollary peer_installed : forall rho I S,
        T.IsResolution (transR rho I) (transD rho I) (transRoot I) S ->
        forall k v m u,
          T.PkgSet.In (Conc.Reduction.embedPkg idg (k, v)) S ->
          T.PkgSet.In (Nm.Intermediate k v m, Vs.Orig u) S ->
        forall r, In ((snd m, u), r) (inst_peer I) ->
          p_optional r = false ->
        exists w,
          PkgSet.In (peerKeyAt I (snd k, v) r, w) (npmResolution S) /\
          Conc.ParentRel.In
            ((peerKeyAt I (snd k, v) r, w), (k, v)) (npmParents S) /\
          VSet.In w (peerCandsAt rho I (snd k, v) r).
    Proof.
      intros rho I S Hres k v m u Hq Hi r Hr Hopt.
      pose proof (npm_soundness rho I S Hres) as Hsrc.
      assert (Hp : PkgSet.In (k, v) (npmResolution S))
        by (apply Conc.Reduction.mem_concurrentResolution; exact Hq).
      assert (HI : Installs (npmResolution S) (npmParents S) (k, v) m u).
      { split.
        - apply Conc.Reduction.mem_concurrentResolution.
          exact (exit_selected rho I S k v m u Hres Hi).
        - apply mem_npmParents; cbn [fst snd]; split; assumption. }
      destruct Hsrc as [_ _ _ _ Hpin _ _ _ _].
      destruct (Hpin (k, v) Hp m u HI r Hr Hopt) as [w [Hw [HwS Hwpi]]].
      exists w; split; [exact HwS | split; [exact Hwpi | exact Hw]].
    Qed.

    Module Lookup.

      Definition repoSlice (I : Inst) (ns : NSet.t) : RepoSet.t :=
        RepoSet.filter (fun p => NSet.mem (fst p) ns) (inst_repo I).

      (* platOKb reads the gate rows only through the fibre over the
         package it is asked about, so the cut is by package rather than
         by name: a package the repository cut keeps takes its own rows
         with it, and a package the cut drops takes none.  Cutting by name
         would keep the rows of every version of that name, which a
         frontend answering a query about one version cannot use. *)
      Definition platSlice (I : Inst) (R : RepoSet.t)
        : list (RPkg.t * Gate) :=
        List.filter (fun q => RepoSet.mem (fst q) R) (inst_plat I).

      (* Any instance whose repository agrees with I at the names in ns,
         whose gate rows agree with I on each package that repository
         keeps, and whose rows are the queried package's own, answers that
         query alike. *)
      Definition sliceInst (I : Inst) (ns : NSet.t)
          (deps : list (RPkg.t * DepRow)) (prs : list (RPkg.t * PeerRow))
        : Inst :=
        {| inst_repo := repoSlice I ns
         ; inst_dep := deps
         ; inst_peer := prs
         ; inst_plat := platSlice I (repoSlice I ns)
         ; inst_ovr := inst_ovr I
         ; inst_root := inst_root I |}.

      Definition ownDepRows (I : Inst) (p : RPkg.t)
        : list (RPkg.t * DepRow) :=
        List.filter (fun q => RPkgEqb.eqb (fst q) p) (inst_dep I).

      Definition ownPeerRows (I : Inst) (p : RPkg.t)
        : list (RPkg.t * PeerRow) :=
        List.filter (fun q => RPkgEqb.eqb (fst q) p) (inst_peer I).

      Definition peerRowsNamed (I : Inst) (n : N.t)
        : list (RPkg.t * PeerRow) :=
        List.filter (fun q => NEqb.eqb (p_name (snd q)) n) (inst_peer I).

      Definition slotTargets (I : Inst) (p : RPkg.t) : NSet.t :=
        namesOfL d_target (depRows I p).

      Definition peerNamesAt (I : Inst) (q : RPkg.t) : NSet.t :=
        namesOfL p_name (peerRowsAt I q).

      Lemma mem_eq_of_iff : forall (s s' : RepoSet.t) x,
          (RepoSet.In x s <-> RepoSet.In x s') ->
          RepoSet.mem x s = RepoSet.mem x s'.
      Proof.
        intros s s' x H; destruct (RepoSet.mem x s) eqn:H1;
          destruct (RepoSet.mem x s') eqn:H2; try reflexivity.
        - apply RepoSet.mem_spec, H, RepoSet.mem_spec in H1; congruence.
        - apply RepoSet.mem_spec in H2; apply H in H2;
            apply RepoSet.mem_spec in H2; congruence.
      Qed.

      Lemma mem_repoSlice : forall I ns p,
          RepoSet.In p (repoSlice I ns) <->
          RepoSet.In p (inst_repo I) /\ NSet.In (fst p) ns.
      Proof.
        intros I ns p; unfold repoSlice; rewrite RSS.filter_spec'.
        rewrite NSet.mem_spec; reflexivity.
      Qed.

      Lemma platOKb_slice : forall rho I ns deps prs p,
          RepoSet.In p (repoSlice I ns) ->
          platOKb rho (sliceInst I ns deps prs) p = platOKb rho I p.
      Proof.
        intros rho I ns deps prs p Hp; unfold platOKb.
        cbn [inst_plat sliceInst]; unfold platSlice.
        rewrite ownRows_filter; [reflexivity |].
        intros g _; cbn [fst]; apply RepoSet.mem_spec; exact Hp.
      Qed.

      Lemma effRepo_slice : forall rho I ns deps prs n w,
          NSet.In n ns ->
          (RepoSet.In (n, w) (effRepo rho (sliceInst I ns deps prs)) <->
           RepoSet.In (n, w) (effRepo rho I)).
      Proof.
        intros rho I ns deps prs n w Hn.
        split; intro H; apply mem_effRepo in H; destruct H as [H1 H2];
          cbn [inst_repo sliceInst] in H1 |- *.
        - assert (Hs : RepoSet.In (n, w) (repoSlice I ns)) by exact H1.
          apply mem_repoSlice in H1; apply mem_effRepo; split;
            [exact (proj1 H1) |].
          rewrite <- (platOKb_slice rho I ns deps prs (n, w) Hs); exact H2.
        - assert (Hs : RepoSet.In (n, w) (repoSlice I ns))
            by (apply mem_repoSlice; split; [exact H1 | exact Hn]).
          apply mem_effRepo; split; [exact Hs |].
          rewrite (platOKb_slice rho I ns deps prs (n, w) Hs); exact H2.
      Qed.

      Lemma realVersions_slice : forall rho I ns deps prs n,
          NSet.In n ns ->
          realVersions (effRepo rho (sliceInst I ns deps prs)) n =
          realVersions (effRepo rho I) n.
      Proof.
        intros rho I ns deps prs n Hn; apply VSet.ext; intro w.
        rewrite !mem_realVersions; apply effRepo_slice; exact Hn.
      Qed.

      (* -- the rows a query reads -- *)

      Lemma depRows_slice : forall I ns deps prs p,
          ownRows deps p = ownRows (inst_dep I) p ->
          depRows (sliceInst I ns deps prs) p = depRows I p.
      Proof.
        intros I ns deps prs p Ho; unfold depRows, depActive.
        cbn [inst_dep inst_root sliceInst]; rewrite Ho; reflexivity.
      Qed.

      Lemma ownDepRows_id : forall I p,
          ownRows (ownDepRows I p) p = ownRows (inst_dep I) p.
      Proof.
        intros I p; unfold ownDepRows; apply ownRows_filter.
        intros d _; cbn [fst]; apply RPkgEqb.eqb_refl.
      Qed.

      Lemma ownPeerRows_id : forall I p,
          ownRows (ownPeerRows I p) p = ownRows (inst_peer I) p.
      Proof.
        intros I p; unfold ownPeerRows; apply ownRows_filter.
        intros r _; cbn [fst]; apply RPkgEqb.eqb_refl.
      Qed.

      Lemma mem_peerDirs_named : forall I ns deps n,
          NSet.mem n (peerDirs (sliceInst I ns deps (peerRowsNamed I n))) =
          NSet.mem n (peerDirs I).
      Proof.
        intros I ns deps n.
        destruct (NSet.mem n
                    (peerDirs (sliceInst I ns deps (peerRowsNamed I n))))
          eqn:H1; destruct (NSet.mem n (peerDirs I)) eqn:H2;
          try reflexivity.
        - apply NSet.mem_spec in H1; unfold peerDirs in H1.
          cbn [inst_peer sliceInst] in H1; apply mem_namesOfL in H1.
          destruct H1 as [q [Hq Hn]]; unfold peerRowsNamed in Hq.
          apply List.filter_In in Hq; destruct Hq as [Hq _].
          assert (NSet.In n (peerDirs I)) as Hc
            by (unfold peerDirs; apply mem_namesOfL; exists q;
                split; assumption).
          apply NSet.mem_spec in Hc; congruence.
        - apply NSet.mem_spec in H2; unfold peerDirs in H2.
          apply mem_namesOfL in H2; destruct H2 as [q [Hq Hn]].
          assert (NSet.In n
                    (peerDirs (sliceInst I ns deps (peerRowsNamed I n))))
            as Hc.
          { unfold peerDirs; cbn [inst_peer sliceInst].
            apply mem_namesOfL; exists q; split; [| exact Hn].
            unfold peerRowsNamed; apply List.filter_In; split;
              [exact Hq | apply NEqb.eqb_true_iff; exact Hn]. }
          apply NSet.mem_spec in Hc; congruence.
      Qed.

      (* -- agreement of the per-query reads under a slice -- *)

      Lemma depRows_agree : forall I ns deps prs p,
          ownRows deps p = ownRows (inst_dep I) p ->
          depRows (sliceInst I ns deps prs) p = depRows I p.
      Proof.
        intros I ns deps prs p Hdeps; unfold depRows, depActive.
        cbn [inst_dep inst_root sliceInst]; rewrite Hdeps; reflexivity.
      Qed.

      Lemma slotOf_agree : forall I ns deps prs p a,
          ownRows deps p = ownRows (inst_dep I) p ->
          slotOf (sliceInst I ns deps prs) p a = slotOf I p a.
      Proof.
        intros I ns deps prs p a Hdeps; unfold slotOf.
        rewrite (depRows_agree I ns deps prs p Hdeps); reflexivity.
      Qed.

      Lemma dirs_agree : forall I ns deps prs p,
          ownRows deps p = ownRows (inst_dep I) p ->
          dirs (sliceInst I ns deps prs) p = dirs I p.
      Proof.
        intros I ns deps prs p Hdeps; unfold dirs.
        rewrite (depRows_agree I ns deps prs p Hdeps); reflexivity.
      Qed.

      Lemma slotKey_agree : forall I ns deps prs p a,
          ownRows deps p = ownRows (inst_dep I) p ->
          slotKey (sliceInst I ns deps prs) p a = slotKey I p a.
      Proof.
        intros I ns deps prs p a Hdeps; unfold slotKey.
        rewrite (slotOf_agree I ns deps prs p a Hdeps); reflexivity.
      Qed.

      Lemma slotCands_agree : forall I ns deps prs p,
          ownRows deps p = ownRows (inst_dep I) p ->
          (forall d, In d (depRows I p) -> NSet.In (d_target d) ns) ->
          forall rho a,
            slotCands rho (sliceInst I ns deps prs) p a =
            slotCands rho I p a.
      Proof.
        intros I ns deps prs p Hdeps Htgt rho a; unfold slotCands.
        rewrite (slotOf_agree I ns deps prs p a Hdeps).
        destruct (slotOf I p a) as [d |] eqn:Hd; [| reflexivity].
        cbn [inst_ovr sliceInst].
        rewrite realVersions_slice; [reflexivity |].
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
          In d (depRows I p) -> NSet.In (d_target d) (slotTargets I p).
      Proof.
        intros I p d Hd; unfold slotTargets; apply mem_namesOfL.
        exists d; split; [exact Hd | reflexivity].
      Qed.

      Lemma childCands_agree : forall rho I ns deps prs
          (p : RPkg.t) (m : NKey.t),
          ownRows deps p = ownRows (inst_dep I) p ->
          (forall d, In d (depRows I p) -> NSet.In (d_target d) ns) ->
          NSet.In (snd m) ns ->
          NSet.mem (fst m) (peerDirs (sliceInst I ns deps prs)) =
            NSet.mem (fst m) (peerDirs I) ->
          childCands rho (sliceInst I ns deps prs) p m =
          childCands rho I p m.
      Proof.
        intros rho I ns deps prs p m Hd Ht Hm Hpa; unfold childCands.
        rewrite (slotKey_agree I ns deps prs p (fst m) Hd).
        rewrite (dirs_agree I ns deps prs p Hd).
        rewrite Hpa.
        destruct (KeyEqb.eqb m (slotKey I p (fst m)));
          destruct (NSet.mem (fst m) (dirs I p));
          destruct (NSet.mem (fst m) (peerDirs I));
          try reflexivity.
        - apply slotCands_agree; assumption.
        - apply slotCands_agree; assumption.
        - apply realVersions_slice; exact Hm.
      Qed.

      (* -- the four lookups -- *)

      Definition granSlice (I : Inst) (k : NKey.t) : Inst :=
        sliceInst I (NSet.singleton (snd k)) (inst_dep I) (inst_peer I).

      Theorem versions_lookupGran : forall rho I k w,
          versions rho (granSlice I k) (Nm.Granular k w) =
          versions rho I (Nm.Granular k w).
      Proof.
        intros rho I k w; cbn [versions].
        assert (Hs : NSet.In (snd k) (NSet.singleton (snd k)))
          by (apply NSet.singleton_spec; reflexivity).
        pose proof (effRepo_slice rho I (NSet.singleton (snd k))
                      (inst_dep I) (inst_peer I) (snd k) w Hs) as He.
        assert (Hm : PkgSet.mem (k, w) (realPkgs rho (granSlice I k)) =
                     PkgSet.mem (k, w) (realPkgs rho I)).
        { apply mem_eq_of_iffP; rewrite !mem_realPkgs.
          unfold Available, base, granSlice; cbn [fst snd].
          split; intros [H1 H2]; split; try exact H1; apply He; exact H2. }
        apply if_scrutinee; exact Hm.
      Qed.

      Definition intSlice (I : Inst) (p : RPkg.t) (m : NKey.t) : Inst :=
        sliceInst I (NSet.add (snd m) (slotTargets I p)) (ownDepRows I p)
          (peerRowsNamed I (fst m)).

      Theorem versions_lookupInt : forall rho I k v m,
          versions rho (intSlice I (snd k, v) m) (Nm.Intermediate k v m) =
          versions rho I (Nm.Intermediate k v m).
      Proof.
        intros rho I k v m; cbn [versions]; f_equal.
        unfold intSlice; apply childCands_agree.
        - apply ownDepRows_id.
        - intros d Hd; apply NSet.add_spec; right;
            apply slotTargets_spec; exact Hd.
        - apply NSet.add_spec; left; reflexivity.
        - apply mem_peerDirs_named.
      Qed.

      (* A package's own peer rows come along because the granular node of
         the root now carries the root's peer edges; for any other package
         they are inert, since rootPeerEdges tests the whole package. *)
      Definition pkgSlice (I : Inst) (p : RPkg.t) : Inst :=
        sliceInst I (NSet.union (slotTargets I p) (peerNamesAt I p))
          (ownDepRows I p) (ownPeerRows I p).

      Theorem dependees_lookupGran : forall rho I k v,
          dependees rho (pkgSlice I (snd k, v))
            (Nm.Granular k v, Vs.Orig v) =
          dependees rho I (Nm.Granular k v, Vs.Orig v).
      Proof.
        intros rho I k v; rewrite !dependees_gran.
        pose proof (ownDepRows_id I (snd k, v)) as Hd.
        assert (Htgt : forall d, In d (depRows I (snd k, v)) ->
                   NSet.In (d_target d)
                     (NSet.union (slotTargets I (snd k, v))
                        (peerNamesAt I (snd k, v)))).
        { intros d Hdr; apply NSet.union_spec; left;
            apply slotTargets_spec; exact Hdr. }
        assert (Hn : forall r, In r (peerRowsAt I (snd k, v)) ->
                   NSet.In (snd (slotKey I (snd k, v) (p_name r)))
                     (NSet.union (slotTargets I (snd k, v))
                        (peerNamesAt I (snd k, v)))).
        { intros r Hr; unfold slotKey.
          destruct (slotOf I (snd k, v) (p_name r)) as [d |] eqn:Hd2.
          - cbn [snd]; apply NSet.union_spec; left.
            apply slotTargets_spec; exact (proj1 (findDepL_some _ _ _ Hd2)).
          - cbn [snd]; apply NSet.union_spec; right; unfold peerNamesAt.
            apply mem_namesOfL; exists r; split; [exact Hr | reflexivity]. }
        unfold pkgSlice; f_equal.
        - unfold entryEdges, base; cbn [fst snd].
          rewrite (dirs_agree I _ _ _ (snd k, v) Hd).
          unfold depsOfL; f_equal; apply map_ext_in; intros a _.
          rewrite (slotKey_agree I _ _ _ (snd k, v) a Hd).
          rewrite (slotCands_agree I _ _ _ (snd k, v) Hd Htgt rho a).
          reflexivity.
        - assert (Hrt : rootPkg (sliceInst I
                            (NSet.union (slotTargets I (snd k, v))
                               (peerNamesAt I (snd k, v)))
                            (ownDepRows I (snd k, v))
                            (ownPeerRows I (snd k, v))) = rootPkg I)
            by reflexivity.
          unfold rootPeerEdges; rewrite Hrt.
          destruct (PkgEqb.eqb (k, v) (rootPkg I)); [| reflexivity].
          unfold base; cbn [fst snd].
          assert (Hpr : peerRowsAt (sliceInst I
                            (NSet.union (slotTargets I (snd k, v))
                               (peerNamesAt I (snd k, v)))
                            (ownDepRows I (snd k, v))
                            (ownPeerRows I (snd k, v))) (snd k, v) =
                        peerRowsAt I (snd k, v))
            by (unfold peerRowsAt; cbn [inst_peer sliceInst];
                apply ownPeerRows_id).
          unfold activePeers, peerActive; rewrite Hpr.
          rewrite (dirs_agree I _ _ _ (snd k, v) Hd).
          unfold depsOfL; f_equal; apply map_ext_in; intros r Hr.
          apply List.filter_In in Hr; destruct Hr as [Hr _].
          unfold peerKeyAt, peerCandsAt, peerKeyAt.
          rewrite (slotKey_agree I _ _ _ (snd k, v) (p_name r) Hd).
          rewrite realVersions_slice; [reflexivity | apply Hn; exact Hr].
      Qed.

      Definition peerSlice (I : Inst) (p : RPkg.t) (m : NKey.t) (u : V.t)
        : Inst :=
        sliceInst I (NSet.union (slotTargets I p) (peerNamesAt I (snd m, u)))
          (ownDepRows I p) (ownPeerRows I (snd m, u)).

      Theorem dependees_lookupInt : forall rho I k v m u,
          dependees rho (peerSlice I (snd k, v) m u)
            (Nm.Intermediate k v m, Vs.Orig u) =
          dependees rho I (Nm.Intermediate k v m, Vs.Orig u).
      Proof.
        intros rho I k v m u; cbn [dependees]; f_equal.
        unfold peerEdgesAt, base; cbn [fst snd].
        pose proof (ownDepRows_id I (snd k, v)) as Hd.
        assert (Hpr : peerRowsAt (peerSlice I (snd k, v) m u) (snd m, u) =
                      peerRowsAt I (snd m, u)).
        { unfold peerSlice, peerRowsAt; cbn [inst_peer sliceInst].
          apply ownPeerRows_id. }
        assert (Hn : forall r, In r (peerRowsAt I (snd m, u)) ->
                   NSet.In (snd (slotKey I (snd k, v) (p_name r)))
                     (NSet.union (slotTargets I (snd k, v))
                        (peerNamesAt I (snd m, u)))).
        { intros r Hr; unfold slotKey.
          destruct (slotOf I (snd k, v) (p_name r)) as [d |] eqn:Hd2.
          - cbn [snd]; apply NSet.union_spec; left.
            apply slotTargets_spec; exact (proj1 (findDepL_some _ _ _ Hd2)).
          - cbn [snd]; apply NSet.union_spec; right; unfold peerNamesAt.
            apply mem_namesOfL; exists r; split; [exact Hr | reflexivity]. }
        unfold peerSlice in Hpr |- *; unfold activePeers, peerActive.
        rewrite Hpr.
        rewrite (dirs_agree I
                   (NSet.union (slotTargets I (snd k, v))
                      (peerNamesAt I (snd m, u)))
                   (ownDepRows I (snd k, v)) (ownPeerRows I (snd m, u))
                   (snd k, v) Hd).
        unfold depsOfL; f_equal; apply map_ext_in; intros r Hr.
        apply List.filter_In in Hr; destruct Hr as [Hr _].
        unfold peerKeyAt, peerCandsAt, peerKeyAt.
        rewrite (slotKey_agree I
                   (NSet.union (slotTargets I (snd k, v))
                      (peerNamesAt I (snd m, u)))
                   (ownDepRows I (snd k, v)) (ownPeerRows I (snd m, u))
                   (snd k, v) (p_name r) Hd).
        rewrite realVersions_slice; [reflexivity | apply Hn; exact Hr].
      Qed.

    End Lookup.

  End Reduction.

End Npm.

(* Smoke instances.  Functor bodies are checked abstractly, so some errors
   surface only at application time, and the reflexivity examples fail if
   any definition stops computing to a normal form.  They live here rather
   than in Smoke.v so that no existing theory file is touched. *)

Module NatVM <: SemverMatch Nat_as_OT.
  Definition isPre (_ : nat) : bool := false.
  Definition sameCore (a b : nat) : bool := Nat.eqb a b.
End NatVM.

Module NpmS := Npm Nat_as_OT Nat_as_OT Nat_as_OT Nat_as_OT NatVM.

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

Definition npmDepB : NpmS.DepRow := NpmS.MkDep npmB npmB (npmEq 1) false.
Definition npmDepC : NpmS.DepRow :=
  NpmS.MkDep npmC npmC (npmBetween 2 4) false.
Definition npmPeerC : NpmS.PeerRow :=
  NpmS.MkPeer npmC (npmBetween 1 3) false.
Definition npmPeerCOpt : NpmS.PeerRow :=
  NpmS.MkPeer npmC (npmBetween 1 3) true.

Definition npmRho : NpmS.Valuation := fun _ => None.

Definition kA : NpmS.NKey.t := (npmA, npmA).
Definition kB : NpmS.NKey.t := (npmB, npmB).
Definition kC : NpmS.NKey.t := (npmC, npmC).
Definition kX : NpmS.NKey.t := (npmX, npmC).

Definition npmShow (h : NpmS.T.Dependees.t)
  : NpmS.Nm.t * list NpmS.Vs.t :=
  (fst h, NpmS.T.VSet.elements (snd h)).

Definition npmDeps (I : NpmS.Inst) (s : NpmS.T.Pkg.t) :=
  List.map npmShow
    (NpmS.T.DependeesSet.elements (NpmS.Reduction.dependees npmRho I s)).

(* A depends on B and on C in [2,4); B declares C in [1,3) as a peer. *)
Definition npmInst : NpmS.Inst :=
  NpmS.MkInst npmRepo
    (((npmA, 1), npmDepB) :: ((npmA, 1), npmDepC) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil nil (npmA, 1).

(* The same, with A's own dependency on C dropped. *)
Definition npmInstAuto : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), npmPeerC) :: nil) nil nil (npmA, 1).

(* The root's own peers, which npm 7+ installs into the root's own
   node_modules: A names C both as a dependency in [2,4) and as a peer in
   [1,3), so its granular node carries both edges to the same directory
   and only 2 satisfies the two ranges at once. *)
Definition npmInstRootPeer : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil)
    (((npmA, 1), npmPeerC) :: nil) nil nil (npmA, 1).

(* The same with the root peer optional; A still fills the directory, so
   the range still binds -- the legacy guard, read at the root. *)
Definition npmInstRootPeerOpt : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil)
    (((npmA, 1), npmPeerCOpt) :: nil) nil nil (npmA, 1).

(* An optional root peer naming a directory A does not fill forces
   nothing, which is the legacy guard again. *)
Definition npmInstRootPeerOptBare : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmA, 1), npmPeerCOpt) :: nil) nil nil (npmA, 1).

(* The same again, with the peer marked optional. *)
Definition npmInstOpt : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepB) :: nil)
    (((npmB, 1), npmPeerCOpt) :: nil) nil nil (npmA, 1).

(* An alias installs the registry package under another directory, so one
   depender can hold two copies of one package. *)
Definition npmDepAlias : NpmS.DepRow := NpmS.MkDep npmX npmC (npmEq 1) false.

Definition npmInstAlias : NpmS.Inst :=
  NpmS.MkInst npmRepo
    (((npmA, 1), npmDepC) :: ((npmA, 1), npmDepAlias) :: nil)
    nil nil nil (npmA, 1).

Definition npmInstPlat : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil) nil
    (((npmC, 3), NpmS.GFalse) :: nil) nil (npmA, 1).

Definition npmInstOvr : NpmS.Inst :=
  NpmS.MkInst npmRepo (((npmA, 1), npmDepC) :: nil) nil nil
    ((npmC, npmEq 3) :: nil) (npmA, 1).

Example npm_versions_computes :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmRho npmInst (NpmS.Nm.Granular kC 2))
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
    (NpmS.Reduction.versions npmRho npmInst (NpmS.Nm.Intermediate kA 1 kC))
  = NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil.
Proof. reflexivity. Qed.

(* The mandatory peer edge leaves B's own directory node, so it fires only
   for the B version that was selected, and it narrows A's copy of C. *)
Example npm_peer_edge_computes :
  npmDeps npmInst (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Granular kB 1, NpmS.Vs.Orig 1 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: nil) :: nil.
Proof. reflexivity. Qed.

(* With A declaring no dependency on C, the peer directory is minted at
   every published version and the same edge auto-installs it. *)
Example npm_auto_versions_computes :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmRho npmInstAuto
       (NpmS.Nm.Intermediate kA 1 kC))
  = NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: NpmS.Vs.Orig 3 :: nil.
Proof. reflexivity. Qed.

Example npm_auto_edge_computes :
  npmDeps npmInstAuto (NpmS.Nm.Intermediate kA 1 kB, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Granular kB 1, NpmS.Vs.Orig 1 :: nil)
    :: (NpmS.Nm.Intermediate kA 1 kC,
        NpmS.Vs.Orig 1 :: NpmS.Vs.Orig 2 :: nil) :: nil.
Proof. reflexivity. Qed.

(* The optional peer keeps npm's legacy guard: A declares no directory for
   C, so no edge is emitted and nothing is forced. *)
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

(* engines/os/cpu cut the repository before anything else. *)
Example npm_platform_cut :
  NpmS.T.VSet.elements
    (NpmS.Reduction.versions npmRho npmInstPlat (NpmS.Nm.Granular kC 3))
  = nil.
Proof. reflexivity. Qed.

Example npm_platform_edge_computes :
  npmDeps npmInstPlat (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kC, NpmS.Vs.Orig 2 :: nil) :: nil.
Proof. reflexivity. Qed.

Example npm_override_computes :
  npmDeps npmInstOvr (NpmS.Nm.Granular kA 1, NpmS.Vs.Orig 1)
  = (NpmS.Nm.Intermediate kA 1 kC, NpmS.Vs.Orig 3 :: nil) :: nil.
Proof. reflexivity. Qed.

(* The prerelease rule, with odd versions coding prereleases of v / 2:
   a comparator set admits one only when it names a prerelease sharing
   the release core. *)
Module NatVMPre <: SemverMatch Nat_as_OT.
  Definition isPre (v : nat) : bool := Nat.odd v.
  Definition sameCore (a b : nat) : bool :=
    Nat.eqb (Nat.div a 2) (Nat.div b 2).
End NatVMPre.

Module NpmP := Npm Nat_as_OT Nat_as_OT Nat_as_OT Nat_as_OT NatVMPre.

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
