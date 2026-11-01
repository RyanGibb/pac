From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Concurrent.

Module PeerDependency (N V : UsualOrderedType) (G : UsualOrderedType).
  Module Conc := Concurrent N V G.
  Module Source := Conc.Source.
  Module Package := Source.Package.
  Module PackageSet := Source.PackageSet.
  Module VSet := Source.VSet.
  Module ParentElt := Conc.ParentElt.
  Module ParentRel := Conc.ParentRel.

  Module PeerDependencyElt := PairUOT Package Source.Dependee.
  Module PeerDependencyRel := FSetUOT PeerDependencyElt.
  Record IsResolution
      (R : PackageSet.t) (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
      (g : V.t -> G.t) (r : Package.t)
      (S : PackageSet.t) (pi : ParentRel.t) : Prop :=
    { res_concurrent : Conc.IsResolution R D g r S pi
    ; res_peer_satisfaction :
        forall p, PackageSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          PeerDependencyRel.In (p, (n, vs)) Th ->
          forall q, ParentRel.In (p, q) pi ->
          forall (us : VSet.t), Source.DependencyRel.In (q, (n, us)) D ->
          forall v, VSet.In v us -> ParentRel.In ((n, v), q) pi ->
            VSet.In v vs }.

  Module Reduction.
    Module PackageEqb := UOTEqb Package.
    Module NEqb := UOTEqb N.
    Definition hasDepOnb (D : Source.DependencyRel.t) (p : Package.t) (n : N.t) : bool :=
      Source.DependencyRel.exists_ (fun '(q, (m, _)) =>
          andb (PackageEqb.eqb q p) (NEqb.eqb m n))
        D.

    Lemma hasDepOnb_iff : forall D (p : Package.t) (n : N.t),
        hasDepOnb D p n = true <-> exists vs, Source.DependencyRel.In (p, (n, vs)) D.
    Proof.
      intros D p m; unfold hasDepOnb; rewrite Source.DependencyRel.exists_spec'.
      split.
      - intros [[q [m' vs]] [He Hb]]; cbn [fst snd] in Hb.
        rewrite Bool.andb_true_iff, PackageEqb.eqb_true_iff, NEqb.eqb_true_iff
          in Hb.
        destruct Hb as [-> ->]; eauto.
      - intros [vs He]; exists (p, (m, vs)); split; [exact He |].
        cbn [fst snd]; rewrite PackageEqb.eqb_refl, NEqb.eqb_refl; reflexivity.
    Qed.

    Module Reduced := Conc.Reduction.Reduced.
    Module Name := Conc.Reduction.Name.
    Module Version := Conc.Reduction.Version.
    Module SOvtp := Conc.Reduction.SOvtp.

    Module SOetp := SetOps PeerDependencyElt Reduced.Package PeerDependencyRel Reduced.PackageSet.
    Definition peerReals (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
        (n : N.t) (v : V.t) (o : N.t) (u : V.t) : Reduced.PackageSet.t :=
      SOetp.unionMap (fun '(q, (m, ws)) =>
          if Package.eq_dec q (o, u)
          then if hasDepOnb D (n, v) m
               then SOvtp.map (fun w =>
                        (Name.Intermediate n v m, Version.Orig w))
                      ws
               else Reduced.PackageSet.empty
          else Reduced.PackageSet.empty)
        Th.

    Definition peerRealsOfVS (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
        (n : N.t) (v : V.t) (o : N.t) (us : VSet.t) : Reduced.PackageSet.t :=
      SOvtp.unionMap (peerReals D Th n v o) us.

    Module SOdtp := Conc.Reduction.SOdtp.
    Definition reduceRealIntermediate (D : Source.DependencyRel.t) : Reduced.PackageSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          SOvtp.map (fun u => (Name.Intermediate n v m, Version.Orig u)) vs)
        D.

    Definition reduceRealPeer (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t) : Reduced.PackageSet.t :=
      SOdtp.unionMap (fun '((n, v), (o, us)) => peerRealsOfVS D Th n v o us) D.

    Definition reduceReal (R : PackageSet.t) (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
        (g : V.t -> G.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.union (Conc.Reduction.embedSet g R)
        (Reduced.PackageSet.union (reduceRealIntermediate D) (reduceRealPeer D Th)).

    Module SOetd := SetOps PeerDependencyElt Reduced.DependencyElt PeerDependencyRel Reduced.DependencyRel.
    Definition peerEdges (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
        (n : N.t) (v : V.t) (o : N.t) (u : V.t) : Reduced.DependencyRel.t :=
      SOetd.filterMap (fun '(q, (m, ws)) =>
          if Package.eq_dec q (o, u)
          then if hasDepOnb D (n, v) m
               then Some ((Name.Intermediate n v o, Version.Orig u),
                          (Name.Intermediate n v m,
                           Conc.Reduction.embedVS ws))
               else None
          else None)
        Th.

    Module SOvtd := Conc.Reduction.SOvtd.
    Definition peerEdgesOfVS (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
        (n : N.t) (v : V.t) (o : N.t) (us : VSet.t) : Reduced.DependencyRel.t :=
      SOvtd.unionMap (peerEdges D Th n v o) us.

    Module SOdtd := Conc.Reduction.SOdtd.
    Definition reduceDepsDepToInt (D : Source.DependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyRel.t :=
      SOdtd.map (fun '((n, v), (m, vs)) =>
          ((Name.Granular n (g v), Version.Orig v),
           (Name.Intermediate n v m, Conc.Reduction.embedVS vs)))
        D.

    Definition reduceDepsIntToDep (D : Source.DependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          SOvtd.map (fun u =>
              ((Name.Intermediate n v m, Version.Orig u),
               (Name.Granular m (g u), Reduced.VSet.singleton (Version.Orig u))))
            vs)
        D.

    Definition reduceDepsPeer (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t) : Reduced.DependencyRel.t :=
      SOdtd.unionMap (fun '((n, v), (o, us)) => peerEdgesOfVS D Th n v o us) D.

    Definition reduceDeps (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyRel.t :=
      Reduced.DependencyRel.union (reduceDepsDepToInt D g)
        (Reduced.DependencyRel.union (reduceDepsIntToDep D g) (reduceDepsPeer D Th)).

    Module SOdpp := Conc.Reduction.SOdpp.
    Module SOvpp := Conc.Reduction.SOvpp.
    Definition parents (D : Source.DependencyRel.t) (g : V.t -> G.t) (S : Reduced.PackageSet.t) :
        ParentRel.t :=
      SOdpp.unionMap (fun '((n, v), (m, vs)) =>
          SOvpp.filterMap (fun u =>
              if andb (Reduced.PackageSet.mem
                         (Name.Intermediate n v m, Version.Orig u) S)
                   (Reduced.PackageSet.mem
                      (Name.Granular n (g v), Version.Orig v) S)
              then Some ((m, u), (n, v))
              else None)
            vs)
        D.

    Lemma mem_parents : forall D g S m u n v,
        ParentRel.In ((m, u), (n, v)) (parents D g S) <->
        exists vs, Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          Reduced.PackageSet.In (Name.Granular n (g v), Version.Orig v) S /\
          Reduced.PackageSet.In (Name.Intermediate n v m, Version.Orig u) S.
    Proof.
      intros D g S m u n v; unfold parents; rewrite SOdpp.mem_unionMap.
      split.
      - intros [[[n' v'] [m' vs]] [HeD Hh]]; cbn beta iota in Hh.
        apply SOvpp.mem_filterMap_if in Hh; destruct Hh as [u' [Hu [Hb E]]].
        injection E as <- <- <- <-.
        rewrite Bool.andb_true_iff, !Reduced.PackageSet.mem_spec in Hb.
        exists vs; intuition.
      - intros (vs & HD & Hu & HvS & HuS).
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvpp.mem_filterMap_if; exists u.
        rewrite Bool.andb_true_iff, !Reduced.PackageSet.mem_spec; repeat split; auto.
    Qed.

    Lemma mem_reduceRealIntermediate : forall D p,
        Reduced.PackageSet.In p (reduceRealIntermediate D) <->
        exists n v m vs u,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          p = (Name.Intermediate n v m, Version.Orig u).
    Proof.
      intros D p; unfold reduceRealIntermediate; rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        apply SOvtp.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [Hu ->]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvtp.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_peerReals : forall D Th n v o u p,
        Reduced.PackageSet.In p (peerReals D Th n v o u) <->
        exists m ws w,
          PeerDependencyRel.In ((o, u), (m, ws)) Th /\ hasDepOnb D (n, v) m = true /\
          VSet.In w ws /\ p = (Name.Intermediate n v m, Version.Orig w).
    Proof.
      intros D Th n v o u p; unfold peerReals; rewrite SOetp.mem_unionMap.
      split.
      - intros [[q [m ws]] [HtTh Hh]]; cbn beta iota in Hh.
        destruct (Package.eq_dec q (o, u)) as [-> | NE];
          [| destruct (SOvtp.empty_in _ Hh)].
        destruct (hasDepOnb D (n, v) m) eqn:Hb;
          [| destruct (SOvtp.empty_in _ Hh)].
        apply SOvtp.mem_map in Hh; destruct Hh as [w [Hw ->]].
        exists m, ws, w; repeat split; assumption.
      - intros [m [ws [w [HTh [Hb [Hw ->]]]]]].
        exists ((o, u), (m, ws)); split; [exact HTh | cbn beta iota].
        rewrite dec_refl, Hb; apply SOvtp.mem_map; eauto.
    Qed.

    Lemma mem_peerRealsOfVS : forall D Th n v o us p,
        Reduced.PackageSet.In p (peerRealsOfVS D Th n v o us) <->
        exists u m ws w,
          VSet.In u us /\ PeerDependencyRel.In ((o, u), (m, ws)) Th /\
          hasDepOnb D (n, v) m = true /\ VSet.In w ws /\
          p = (Name.Intermediate n v m, Version.Orig w).
    Proof.
      intros D Th n v o us p; unfold peerRealsOfVS;
        rewrite SOvtp.mem_unionMap.
      split.
      - intros [u [Hu Hh]]; apply mem_peerReals in Hh.
        destruct Hh as [m [ws [w [HTh [Hb [Hw ->]]]]]].
        exists u, m, ws, w; repeat split; assumption.
      - intros [u [m [ws [w [Hu [HTh [Hb [Hw ->]]]]]]]].
        exists u; split; [exact Hu |].
        apply mem_peerReals; exists m, ws, w; repeat split; assumption.
    Qed.

    Lemma mem_reduceRealPeer : forall D Th p,
        Reduced.PackageSet.In p (reduceRealPeer D Th) <->
        exists n v o us u m ws w,
          Source.DependencyRel.In ((n, v), (o, us)) D /\ VSet.In u us /\
          PeerDependencyRel.In ((o, u), (m, ws)) Th /\ hasDepOnb D (n, v) m = true /\
          VSet.In w ws /\ p = (Name.Intermediate n v m, Version.Orig w).
    Proof.
      intros D Th p; unfold reduceRealPeer; rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [o us]] [HeD Hh]]; cbn beta iota in Hh.
        apply mem_peerRealsOfVS in Hh.
        destruct Hh as [u [m [ws [w [Hu [HTh [Hb [Hw ->]]]]]]]].
        exists n, v, o, us, u, m, ws, w; repeat split; assumption.
      - intros [n [v [o [us [u [m [ws [w [HD [Hu [HTh [Hb [Hw ->]]]]]]]]]]]]].
        exists ((n, v), (o, us)); split; [exact HD | cbn beta iota].
        apply mem_peerRealsOfVS.
        exists u, m, ws, w; repeat split; assumption.
    Qed.

    Module SOptp := Conc.Reduction.SOptp.
    Inductive ReducedPkg (R : PackageSet.t) (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
        (g : V.t -> G.t) : Reduced.Package.t -> Prop :=
    | PkgEmbed : forall n v, PackageSet.In (n, v) R ->
        ReducedPkg R D Th g (Name.Granular n (g v), Version.Orig v)
    | PkgIntermediate : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> VSet.In u vs ->
        ReducedPkg R D Th g (Name.Intermediate n v m, Version.Orig u)
    | PkgPeer : forall n v m vs o us u ws w,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        Source.DependencyRel.In ((n, v), (o, us)) D -> VSet.In u us ->
        PeerDependencyRel.In ((o, u), (m, ws)) Th -> VSet.In w ws ->
        ReducedPkg R D Th g (Name.Intermediate n v m, Version.Orig w).

    Lemma mem_reduceReal : forall R D Th g q,
        Reduced.PackageSet.In q (reduceReal R D Th g) <-> ReducedPkg R D Th g q.
    Proof.
      intros R D Th g q; unfold reduceReal, Conc.Reduction.embedSet.
      rewrite !Reduced.PackageSet.union_spec, SOptp.mem_map,
        mem_reduceRealIntermediate, mem_reduceRealPeer.
      split.
      - intros [[[n v] [Hp ->]] | [H | H]].
        + apply PkgEmbed; exact Hp.
        + destruct H as (n & v & m & vs & u & HD & Hu & ->).
          eapply PkgIntermediate; eassumption.
        + destruct H
            as (n & v & o & us & u & m & ws & w & HD & Hu & HTh & Hb & Hw & ->).
          apply hasDepOnb_iff in Hb; destruct Hb as [vs HDm].
          exact (PkgPeer _ _ _ _ n v m vs o us u ws w HDm HD Hu HTh Hw).
      - destruct 1 as [n v Hp | n v m vs u HD Hu
                      | n v m vs o us u ws w HDm HD Hu HTh Hw];
          [left; exists (n, v) | right; left | right; right]; try eauto 20.
        assert (hasDepOnb D (n, v) m = true)
          by (apply hasDepOnb_iff; exists vs; exact HDm).
        eauto 20.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall g (p : Package.t) R D Th,
        Reduced.PackageSet.In (Conc.Reduction.embedPkg g p) (reduceReal R D Th g) ->
        PackageSet.In p R.
    Proof.
      intros g [n v] R D Th H; apply mem_reduceReal in H.
      unfold Conc.Reduction.embedPkg in H; cbn [fst snd] in H.
      inversion H; subst; assumption.
    Qed.

    Lemma mem_reduceDepsDepToInt : forall D g y,
        Reduced.DependencyRel.In y (reduceDepsDepToInt D g) <->
        exists n v m vs,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\
          y = ((Name.Granular n (g v), Version.Orig v),
               (Name.Intermediate n v m, Conc.Reduction.embedVS vs)).
    Proof.
      intros D g y; unfold reduceDepsDepToInt; rewrite SOdtd.mem_map.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh; subst y.
        exists n, v, m, vs; split; [assumption | reflexivity].
      - intros [n [v [m [vs [HD ->]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | reflexivity].
    Qed.

    Lemma mem_reduceDepsIntToDep : forall D g y,
        Reduced.DependencyRel.In y (reduceDepsIntToDep D g) <->
        exists n v m vs u,
          Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          y = ((Name.Intermediate n v m, Version.Orig u),
               (Name.Granular m (g u),
                Reduced.VSet.singleton (Version.Orig u))).
    Proof.
      intros D g y; unfold reduceDepsIntToDep; rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        apply SOvtd.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [Hu ->]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvtd.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_peerEdges : forall D Th n v o u y,
        Reduced.DependencyRel.In y (peerEdges D Th n v o u) <->
        exists m ws,
          PeerDependencyRel.In ((o, u), (m, ws)) Th /\ hasDepOnb D (n, v) m = true /\
          y = ((Name.Intermediate n v o, Version.Orig u),
               (Name.Intermediate n v m, Conc.Reduction.embedVS ws)).
    Proof.
      intros D Th n v o u y; unfold peerEdges; rewrite SOetd.mem_filterMap.
      split.
      - intros [[q [m ws]] [HtTh Hh]]; cbn beta iota in Hh.
        destruct (Package.eq_dec q (o, u)) as [-> | NE]; [| discriminate].
        destruct (hasDepOnb D (n, v) m) eqn:Hb; [| discriminate].
        injection Hh as <-.
        exists m, ws; repeat split; assumption.
      - intros [m [ws [HTh [Hb ->]]]].
        exists ((o, u), (m, ws)); split; [exact HTh | cbn beta iota].
        rewrite dec_refl, Hb; reflexivity.
    Qed.

    Lemma mem_peerEdgesOfVS : forall D Th n v o us y,
        Reduced.DependencyRel.In y (peerEdgesOfVS D Th n v o us) <->
        exists u m ws,
          VSet.In u us /\ PeerDependencyRel.In ((o, u), (m, ws)) Th /\
          hasDepOnb D (n, v) m = true /\
          y = ((Name.Intermediate n v o, Version.Orig u),
               (Name.Intermediate n v m, Conc.Reduction.embedVS ws)).
    Proof.
      intros D Th n v o us y; unfold peerEdgesOfVS;
        rewrite SOvtd.mem_unionMap.
      split.
      - intros [u [Hu Hh]]; apply mem_peerEdges in Hh.
        destruct Hh as [m [ws [HTh [Hb ->]]]].
        exists u, m, ws; repeat split; assumption.
      - intros [u [m [ws [Hu [HTh [Hb ->]]]]]].
        exists u; split; [exact Hu |].
        apply mem_peerEdges; exists m, ws; repeat split; assumption.
    Qed.

    Lemma mem_reduceDepsPeer : forall D Th y,
        Reduced.DependencyRel.In y (reduceDepsPeer D Th) <->
        exists n v o us u m ws,
          Source.DependencyRel.In ((n, v), (o, us)) D /\ VSet.In u us /\
          PeerDependencyRel.In ((o, u), (m, ws)) Th /\ hasDepOnb D (n, v) m = true /\
          y = ((Name.Intermediate n v o, Version.Orig u),
               (Name.Intermediate n v m, Conc.Reduction.embedVS ws)).
    Proof.
      intros D Th y; unfold reduceDepsPeer; rewrite SOdtd.mem_unionMap.
      split.
      - intros [[[n v] [o us]] [HeD Hh]]; cbn beta iota in Hh.
        apply mem_peerEdgesOfVS in Hh.
        destruct Hh as [u [m [ws [Hu [HTh [Hb ->]]]]]].
        exists n, v, o, us, u, m, ws; repeat split; assumption.
      - intros [n [v [o [us [u [m [ws [HD [Hu [HTh [Hb ->]]]]]]]]]]].
        exists ((n, v), (o, us)); split; [exact HD | cbn beta iota].
        apply mem_peerEdgesOfVS.
        exists u, m, ws; repeat split; assumption.
    Qed.

    Inductive ReducedEdge (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t) (g : V.t -> G.t) :
        Reduced.DependencyElt.t -> Prop :=
    | EdgeDepToInt : forall n v m vs,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        ReducedEdge D Th g
          ((Name.Granular n (g v), Version.Orig v),
           (Name.Intermediate n v m, Conc.Reduction.embedVS vs))
    | EdgeIntToDep : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> VSet.In u vs ->
        ReducedEdge D Th g
          ((Name.Intermediate n v m, Version.Orig u),
           (Name.Granular m (g u), Reduced.VSet.singleton (Version.Orig u)))
    | EdgePeer : forall n v m vs o us u ws,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        Source.DependencyRel.In ((n, v), (o, us)) D -> VSet.In u us ->
        PeerDependencyRel.In ((o, u), (m, ws)) Th ->
        ReducedEdge D Th g
          ((Name.Intermediate n v o, Version.Orig u),
           (Name.Intermediate n v m, Conc.Reduction.embedVS ws)).

    Lemma mem_reduceDeps : forall D Th g y,
        Reduced.DependencyRel.In y (reduceDeps D Th g) <-> ReducedEdge D Th g y.
    Proof.
      intros D Th g y; unfold reduceDeps.
      rewrite !Reduced.DependencyRel.union_spec, mem_reduceDepsDepToInt,
        mem_reduceDepsIntToDep, mem_reduceDepsPeer.
      split.
      - intros [H | [H | H]].
        + destruct H as (n & v & m & vs & HD & ->).
          eapply EdgeDepToInt; eassumption.
        + destruct H as (n & v & m & vs & u & HD & Hu & ->).
          eapply EdgeIntToDep; eassumption.
        + destruct H as (n & v & o & us & u & m & ws & HD & Hu & HTh & Hb & ->).
          apply hasDepOnb_iff in Hb; destruct Hb as [vs HDm].
          exact (EdgePeer _ _ _ n v m vs o us u ws HDm HD Hu HTh).
      - destruct 1 as [n v m vs HD | n v m vs u HD Hu
                      | n v m vs o us u ws HDm HD Hu HTh];
          [left | right; left | right; right]; try eauto 15.
        assert (hasDepOnb D (n, v) m = true)
          by (apply hasDepOnb_iff; exists vs; exact HDm).
        eauto 15.
    Qed.

    Lemma mem_reduceDeps_dep_to_int : forall D Th g n v m vs,
        Source.DependencyRel.In ((n, v), (m, vs)) D ->
        Reduced.DependencyRel.In ((Name.Granular n (g v), Version.Orig v),
                     (Name.Intermediate n v m, Conc.Reduction.embedVS vs))
          (reduceDeps D Th g).
    Proof. intros; apply mem_reduceDeps, EdgeDepToInt; assumption. Qed.

    Lemma mem_reduceDeps_int_to_dep : forall D Th g n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> VSet.In u vs ->
        Reduced.DependencyRel.In ((Name.Intermediate n v m, Version.Orig u),
                     (Name.Granular m (g u),
                      Reduced.VSet.singleton (Version.Orig u)))
          (reduceDeps D Th g).
    Proof. intros; apply mem_reduceDeps; eapply EdgeIntToDep; eassumption. Qed.

    Lemma mem_reduceDeps_peer : forall D Th g n v o us m ws u,
        Source.DependencyRel.In ((n, v), (o, us)) D ->
        VSet.In u us ->
        PeerDependencyRel.In ((o, u), (m, ws)) Th ->
        (exists vs, Source.DependencyRel.In ((n, v), (m, vs)) D) ->
        Reduced.DependencyRel.In ((Name.Intermediate n v o, Version.Orig u),
                     (Name.Intermediate n v m, Conc.Reduction.embedVS ws))
          (reduceDeps D Th g).
    Proof.
      intros D Th g n v o us m ws u HD Hou HTh [vs Hpar].
      apply mem_reduceDeps; eapply EdgePeer; eassumption.
    Qed.

    Module SOvcv := Conc.Reduction.SOvcv.
    Theorem peer_soundness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
             (g : V.t -> G.t) (r : Package.t) (S : Reduced.PackageSet.t),
        Reduced.IsResolution (reduceReal R D Th g) (reduceDeps D Th g)
          (Conc.Reduction.embedPkg g r) S ->
        IsResolution R D Th g r (Conc.Reduction.concurrentResolution g S)
          (parents D g S).
    Proof.
      intros R D Th g r S Hres.
      destruct Hres as [Hsub Hroot Hdep Huniq].
      constructor.
      - constructor.
        + intros p Hp; apply Conc.Reduction.mem_concurrentResolution in Hp.
          exact (embedPkg_mem_reduceReal g p R D Th (Hsub _ Hp)).
        + apply Conc.Reduction.mem_concurrentResolution; exact Hroot.
        + intros [pn pv] Hp m vs Hdep0.
          apply Conc.Reduction.mem_concurrentResolution in Hp;
            unfold Conc.Reduction.embedPkg in Hp; simpl in Hp.
          destruct (Hdep _ Hp _ _
              (mem_reduceDeps_dep_to_int D Th g pn pv m vs Hdep0))
            as [cv [Hcv HcvS]].
          unfold Conc.Reduction.embedVS in Hcv; apply SOvcv.mem_map in Hcv;
            destruct Hcv as [u [Hu ->]].
          destruct (Hdep _ HcvS _ _
              (mem_reduceDeps_int_to_dep D Th g pn pv m vs u Hdep0 Hu))
            as [cv2 [Hcv2 Hcv2S]].
          apply SOvcv.singleton_in in Hcv2; subst cv2.
          exists u; split; [exact Hu | split].
          * apply Conc.Reduction.mem_concurrentResolution; exact Hcv2S.
          * apply mem_parents.
            exists vs; repeat split; assumption.
        + intros m u u' [pn pv] H1 H2.
          apply mem_parents in H1, H2.
          destruct H1 as (vs & _ & _ & _ & HiS).
          destruct H2 as (vs' & _ & _ & _ & HiS').
          pose proof (Huniq _ _ _ HiS HiS') as He.
          injection He as He; exact He.
        + intros n v v' Hv Hv' Hne Hg.
          apply Conc.Reduction.mem_concurrentResolution in Hv, Hv';
            unfold Conc.Reduction.embedPkg in Hv, Hv';
            simpl in Hv, Hv'.
          rewrite Hg in Hv.
          pose proof (Huniq _ _ _ Hv Hv') as He.
          injection He as He; exact (Hne He).
        + intros [m u] [n v] Hcp.
          apply mem_parents in Hcp.
          destruct Hcp as (vs & HD & Hu & HvS & HiS).
          split; [| apply Conc.Reduction.mem_concurrentResolution; exact HvS].
          destruct (Hdep _ HiS _ _
              (mem_reduceDeps_int_to_dep D Th g n v m vs u HD Hu))
            as [cv [Hcv HcvS]].
          apply SOvcv.singleton_in in Hcv; subst cv.
          apply Conc.Reduction.mem_concurrentResolution; exact HcvS.
      - intros [pn pv] Hp n vs HTh [qn qv] Hpq us Hqus v Hv Hnvq.
        apply mem_parents in Hpq.
        destruct Hpq as (vs1 & HD1 & Hou & HqS & HiS).
        apply mem_parents in Hnvq.
        destruct Hnvq as (us' & HD2 & Hv' & _ & HvS).
        destruct (Hdep _ HiS _ _
            (mem_reduceDeps_peer D Th g qn qv pn vs1 n vs pv HD1 Hou HTh
               (ex_intro _ us Hqus)))
          as [cv [Hcv HcvS]].
        unfold Conc.Reduction.embedVS in Hcv; apply SOvcv.mem_map in Hcv;
          destruct Hcv as [w [Hw ->]].
        pose proof (Huniq _ _ _ HvS HcvS) as He.
        injection He as <-; exact Hw.
    Qed.

    Definition coreResolution (D : Source.DependencyRel.t) (g : V.t -> G.t)
        (S : PackageSet.t) (pi : ParentRel.t) : Reduced.PackageSet.t :=
      Reduced.PackageSet.union (SOptp.map (Conc.Reduction.embedPkg g) S)
        (SOdtp.unionMap (fun '((n, v), (m, vs)) =>
             if PackageSet.mem (n, v) S
             then SOvtp.filterMap (fun u =>
                      if andb (PackageSet.mem (m, u) S)
                           (ParentRel.mem ((m, u), (n, v)) pi)
                      then Some (Name.Intermediate n v m, Version.Orig u)
                      else None)
                    vs
             else Reduced.PackageSet.empty)
           D).

    Inductive CorePkg (S : PackageSet.t) (pi : ParentRel.t) (D : Source.DependencyRel.t)
        (g : V.t -> G.t) : Reduced.Package.t -> Prop :=
    | CoreGranular : forall n v, PackageSet.In (n, v) S ->
        CorePkg S pi D g (Name.Granular n (g v), Version.Orig v)
    | CoreIntermediate : forall n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> PackageSet.In (n, v) S ->
        PackageSet.In (m, u) S -> VSet.In u vs ->
        ParentRel.In ((m, u), (n, v)) pi ->
        CorePkg S pi D g (Name.Intermediate n v m, Version.Orig u).

    Lemma mem_coreResolution : forall S pi D g (q : Reduced.Package.t),
        Reduced.PackageSet.In q (coreResolution D g S pi) <-> CorePkg S pi D g q.
    Proof.
      intros S pi D g q; unfold coreResolution.
      rewrite Reduced.PackageSet.union_spec, SOptp.mem_map, SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [HpS ->]] | [[[n v] [m vs]] [HD Hh]]];
          [apply CoreGranular; exact HpS |].
        cbn beta iota in Hh; apply SOdtp.in_if_empty in Hh as [Hnv Hm].
        apply SOvtp.mem_filterMap_if in Hm; destruct Hm as [u [Hu [Hb ->]]].
        rewrite PackageSet.mem_spec in Hnv.
        rewrite Bool.andb_true_iff, PackageSet.mem_spec, ParentRel.mem_spec in Hb.
        eapply CoreIntermediate; try eassumption; tauto.
      - destruct 1 as [n v HpS | n v m vs u HD Hnv Hmu Hu Hpi];
          [left; exists (n, v); auto | right].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOdtp.in_if_empty; rewrite SOvtp.mem_filterMap_if.
        rewrite PackageSet.mem_spec; split; [exact Hnv |]; exists u.
        rewrite Bool.andb_true_iff, PackageSet.mem_spec, ParentRel.mem_spec.
        repeat split; auto.
    Qed.

    Lemma mem_coreResolution_granular : forall S pi D g n v,
        PackageSet.In (n, v) S ->
        Reduced.PackageSet.In (Name.Granular n (g v), Version.Orig v)
          (coreResolution D g S pi).
    Proof. intros; apply mem_coreResolution, CoreGranular; assumption. Qed.

    Lemma mem_coreResolution_intermediate : forall S pi D g n v m vs u,
        Source.DependencyRel.In ((n, v), (m, vs)) D -> PackageSet.In (n, v) S ->
        PackageSet.In (m, u) S -> VSet.In u vs ->
        ParentRel.In ((m, u), (n, v)) pi ->
        Reduced.PackageSet.In (Name.Intermediate n v m, Version.Orig u)
          (coreResolution D g S pi).
    Proof. intros; apply mem_coreResolution; econstructor; eassumption. Qed.

    Theorem peer_completeness :
      forall (R : PackageSet.t) (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t)
             (g : V.t -> G.t) (r : Package.t)
             (S : PackageSet.t) (pi : ParentRel.t),
        IsResolution R D Th g r S pi ->
        Reduced.IsResolution (reduceReal R D Th g) (reduceDeps D Th g)
          (Conc.Reduction.embedPkg g r) (coreResolution D g S pi).
    Proof.
      intros R D Th g r S pi Hres.
      destruct Hres as [Hconc Hpsat].
      destruct Hconc as [Hsub Hroot Hpc Hpif Hvg Hps].
      constructor.
      - intros q Hq; apply mem_reduceReal; apply mem_coreResolution in Hq.
        destruct Hq as [n v Hnv | n v m vs u HD Hnv Hmu Hu Hpi];
          [apply PkgEmbed, Hsub, Hnv | eapply PkgIntermediate; eassumption].
      - destruct r as [rn rv].
        exact (mem_coreResolution_granular S pi D g rn rv Hroot).
      - intros q Hq md vsd Hd.
        apply mem_coreResolution in Hq; apply mem_reduceDeps in Hd.
        destruct Hq as [n v Hnv | n v m vs u HD Hnv Hmu Hu Hpi].
        + inversion Hd as [n' v' m' vs' HD' | |]; subst.
          destruct (Hpc _ Hnv _ _ HD') as [u [Huv [HmuS Hpiu]]].
          exists (Version.Orig u); split.
          { unfold Conc.Reduction.embedVS; apply SOvcv.mem_map;
              exists u; split; [exact Huv | reflexivity]. }
          { exact (mem_coreResolution_intermediate S pi D g n v m' vs' u
                     HD' Hnv HmuS Huv Hpiu). }
        + inversion Hd as [| n' v' m' vs' u' HD' Hu'
                          | qn qv m' vs2 o us0 u0 ws' HD2 HD1 Hu0 HTh]; subst.
          * exists (Version.Orig u); split.
            { apply SOvcv.singleton_in; reflexivity. }
            { exact (mem_coreResolution_granular S pi D g m u Hmu). }
          * destruct (Hpc _ Hnv _ _ HD2) as [w [Hw [HmwS Hpiw]]].
            exists (Version.Orig w); split.
            { unfold Conc.Reduction.embedVS; apply SOvcv.mem_map; exists w;
                split; [| reflexivity].
              exact (Hpsat _ Hmu _ _ HTh _ Hpi _ HD2 _ Hw Hpiw). }
            { exact (mem_coreResolution_intermediate S pi D g n v m' vs2 w
                       HD2 Hnv HmwS Hw Hpiw). }
      - intros n cv1 cv2 H1 H2.
        apply mem_coreResolution in H1, H2.
        inversion H1 as [n1 v1 Hm1 | n1 v1 m1 vs1 u1 Hd1 Hnv1 Hmu1 Hu1 Hpi1];
          subst;
          inversion H2 as [n2 v2 Hm2 | n2 v2 m2 vs2 u2 Hd2 Hnv2 Hmu2 Hu2 Hpi2];
          subst.
        + destruct (V.eq_dec v1 v2) as [-> | NE]; [reflexivity | exfalso].
          apply (Hvg n1 v1 v2 Hm1 Hm2 NE); congruence.
        + rewrite (Hpif _ _ _ _ Hpi1 Hpi2); reflexivity.
    Qed.

    Lemma concurrentResolution_coreResolution : forall S pi D g,
        Conc.Reduction.concurrentResolution g (coreResolution D g S pi) = S.
    Proof.
      intros S pi D g; apply PackageSet.ext; intros [n v].
      rewrite Conc.Reduction.mem_concurrentResolution, mem_coreResolution.
      unfold Conc.Reduction.embedPkg; cbn [fst snd].
      split; [intro H; inversion H; assumption | apply CoreGranular].
    Qed.

    Lemma parents_coreResolution_iff : forall R D Th g r S pi,
        IsResolution R D Th g r S pi ->
        forall m u n v,
          ParentRel.In ((m, u), (n, v)) (parents D g (coreResolution D g S pi))
          <-> ParentRel.In ((m, u), (n, v)) pi /\
              exists vs, Source.DependencyRel.In ((n, v), (m, vs)) D /\ VSet.In u vs.
    Proof.
      intros R D Th g r S pi [[_ _ _ _ _ Hps] _] m u n v; rewrite mem_parents.
      split.
      - intros (vs & HD & Hu & _ & Hint).
        split; [| exists vs; split; assumption].
        apply mem_coreResolution in Hint; inversion Hint; assumption.
      - intros [Hpi (vs & HD & Hu)].
        destruct (Hps _ _ Hpi) as [HmS HnS].
        exists vs.
        split; [exact HD |].
        split; [exact Hu |].
        split; [exact (mem_coreResolution_granular S pi D g n v HnS) |].
        exact (mem_coreResolution_intermediate S pi D g n v m vs u
                 HD HnS HmS Hu Hpi).
    Qed.

    Theorem peer_retraction : forall R D Th g r S pi,
        IsResolution R D Th g r S pi -> Conc.ParentDependency D pi ->
        Conc.Reduction.concurrentResolution g (coreResolution D g S pi) = S /\
        parents D g (coreResolution D g S pi) = pi.
    Proof.
      intros R D Th g r S pi Hres Hdep.
      split; [apply concurrentResolution_coreResolution |].
      apply ParentRel.ext; intros [[m u] [n v]].
      rewrite (parents_coreResolution_iff _ _ _ _ _ _ _ Hres).
      split; [intros [H _]; exact H | intro H; exact (conj H (Hdep _ _ _ _ H))].
    Qed.

    Module Lookup.
      Lemma reduceDeps_mono : forall D D' Th Th' g (y : Reduced.DependencyElt.t),
          Source.DependencyRel.Subset D' D -> PeerDependencyRel.Subset Th' Th ->
          Reduced.DependencyRel.In y (reduceDeps D' Th' g) ->
          Reduced.DependencyRel.In y (reduceDeps D Th g).
      Proof.
        intros D D' Th Th' g y HD HTh; revert y.
        unfold reduceDeps, reduceDepsDepToInt, reduceDepsIntToDep,
          reduceDepsPeer.
        repeat apply SOdtd.union_subset.
        - apply SOdtd.map_mono; [exact HD | intros x; reflexivity].
        - apply SOdtd.unionMap_mono; [exact HD | intros x z Hz; exact Hz].
        - apply SOdtd.unionMap_mono; [exact HD |].
          intros [[n v] [o us]]; cbn beta iota; unfold peerEdgesOfVS.
          apply SOvtd.unionMap_mono; [intros z Hz; exact Hz |].
          intro u; unfold peerEdges.
          apply SOetd.filterMap_mono; [exact HTh |].
          intros [q [m ws]] z Hz; cbn beta iota in Hz |- *.
          destruct (Package.eq_dec q (o, u)); [| discriminate Hz].
          destruct (hasDepOnb D' (n, v) m) eqn:Hb; [| discriminate Hz].
          apply hasDepOnb_iff in Hb; destruct Hb as [ws0 Hb].
          assert (hasDepOnb D (n, v) m = true) as Hb'
            by (apply hasDepOnb_iff; exists ws0; exact (HD _ Hb)).
          rewrite Hb'; exact Hz.
      Qed.

      Module DependencyRelFibred := FibredRel Package Source.Dependee Source.DependencyElt Source.DependencyRel.
      Module PeerDependencyRelFibred := FibredRel Package Source.Dependee PeerDependencyElt PeerDependencyRel.

      Definition dependsOnb (D : Source.DependencyRel.t) (p q : Package.t) : bool :=
        Source.DependencyRel.exists_ (fun '(p0, (m0, vs)) =>
            andb (PackageEqb.eqb p0 p)
              (andb (NEqb.eqb m0 (fst q)) (VSet.mem (snd q) vs)))
          D.

      Lemma dependsOnb_iff : forall D (p : Package.t) (m : N.t) (u : V.t),
          dependsOnb D p (m, u) = true <->
          exists vs, Source.DependencyRel.In (p, (m, vs)) D /\ VSet.In u vs.
      Proof.
        intros D p m u; unfold dependsOnb; rewrite Source.DependencyRel.exists_spec'.
        split.
        - intros [[p0 [m0 vs]] [He Hb]]; cbn [fst snd] in Hb.
          rewrite !Bool.andb_true_iff, PackageEqb.eqb_true_iff,
            NEqb.eqb_true_iff, VSet.mem_spec in Hb.
          destruct Hb as [-> [-> Hu]]; eauto.
        - intros [vs [He Hu]]; exists (p, (m, vs)); split; [exact He |].
          cbn [fst snd]; rewrite PackageEqb.eqb_refl, NEqb.eqb_refl; cbn [andb].
          apply VSet.mem_spec; exact Hu.
      Qed.

      Definition peersOfDeps (D : Source.DependencyRel.t) (Th : PeerDependencyRel.t) (p : Package.t)
          (o : N.t) : PeerDependencyRel.t :=
        PeerDependencyRel.filter (fun '(q, (o', _)) =>
            andb (NEqb.eqb o' o) (dependsOnb D p q))
          Th.

      Lemma mem_peersOfDeps :
        forall D Th (p : Package.t) (m : N.t) (u : V.t) (o o' : N.t)
               (ws : VSet.t),
          PeerDependencyRel.In ((m, u), (o', ws)) (peersOfDeps D Th p o) <->
          PeerDependencyRel.In ((m, u), (o', ws)) Th /\ o' = o /\
          (exists vs, Source.DependencyRel.In (p, (m, vs)) D /\ VSet.In u vs).
      Proof.
        intros D Th p m u o o' ws; unfold peersOfDeps.
        rewrite PeerDependencyRel.filter_spec'; cbn beta iota.
        rewrite Bool.andb_true_iff, NEqb.eqb_true_iff, dependsOnb_iff.
        tauto.
      Qed.

      Theorem versions_lookupGranular :
        forall R D Th g (n : N.t) (w : G.t),
          Reduced.versions (reduceReal R D Th g) (Name.Granular n w) =
          Reduced.versions
            (reduceReal (Conc.Reduction.Lookup.granFibre g R n w)
               Source.DependencyRel.empty PeerDependencyRel.empty g)
            (Name.Granular n w).
      Proof.
        intros R D Th g n w; apply Reduced.versions_ext; intro v.
        rewrite !mem_reduceReal.
        split; intro H; inversion H as [qn qv HR | |]; subst; apply PkgEmbed.
        - apply Conc.Reduction.Lookup.mem_granFibre; auto.
        - apply Conc.Reduction.Lookup.mem_granFibre in HR; tauto.
      Qed.

      Theorem dependees_lookupGranular : forall D Th g n v,
          Reduced.dependees (reduceDeps D Th g)
            (Name.Granular n (g v), Version.Orig v) =
          Reduced.dependees
            (reduceDeps (DependencyRelFibred.tailFibre D (n, v)) PeerDependencyRel.empty g)
            (Name.Granular n (g v), Version.Orig v).
      Proof.
        intros D Th g n v; apply Reduced.dependees_ext; intros [m ws].
        split; [| intro H; exact (reduceDeps_mono _ _ _ _ _ _
                    (DependencyRelFibred.tailFibre_subset _ _)
                    (PeerDependencyRel.empty_subset _) H)].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H as [n' v' m' vs HD | |]; subst.
        apply EdgeDepToInt, DependencyRelFibred.mem_tailFibre.
        split; [exact HD | reflexivity].
      Qed.

      Theorem versions_lookupIntermediate : forall R D Th g n v o,
          Reduced.versions (reduceReal R D Th g) (Name.Intermediate n v o) =
          Reduced.versions
            (reduceReal PackageSet.empty (DependencyRelFibred.tailFibre D (n, v))
               (peersOfDeps D Th (n, v) o) g)
            (Name.Intermediate n v o).
      Proof.
        intros R D Th g n v o; apply Reduced.versions_ext; intro u'.
        rewrite !mem_reduceReal.
        split; intro H;
          inversion H as [| n' v' m' vs u HD Hu
                          | n' v' m' vs2 o' us u ws w HD2 HD Hu HTh Hw]; subst.
        - apply (PkgIntermediate _ _ _ _ n v o vs u); [| exact Hu].
          apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
        - apply (PkgPeer _ _ _ _ n v o vs2 o' us u ws w); try assumption.
          + apply DependencyRelFibred.mem_tailFibre; split; [exact HD2 | reflexivity].
          + apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
          + apply mem_peersOfDeps; split; [exact HTh |].
            split; [reflexivity | exists us; split; [exact HD | exact Hu]].
        - apply DependencyRelFibred.mem_tailFibre in HD as [HD _].
          apply (PkgIntermediate _ _ _ _ n v o vs u); assumption.
        - apply DependencyRelFibred.mem_tailFibre in HD as [HD _].
          apply DependencyRelFibred.mem_tailFibre in HD2 as [HD2 _].
          apply mem_peersOfDeps in HTh as [HTh _].
          apply (PkgPeer _ _ _ _ n v o vs2 o' us u ws w); assumption.
      Qed.

      Theorem dependees_lookupIntermediate : forall D Th g n v o u,
          Reduced.dependees (reduceDeps D Th g)
            (Name.Intermediate n v o, Version.Orig u) =
          Reduced.dependees
            (reduceDeps (DependencyRelFibred.tailFibre D (n, v))
                        (PeerDependencyRelFibred.tailFibre Th (o, u)) g)
            (Name.Intermediate n v o, Version.Orig u).
      Proof.
        intros D Th g n v o u; apply Reduced.dependees_ext; intros [m ws].
        split; [| intro H; exact (reduceDeps_mono _ _ _ _ _ _
                    (DependencyRelFibred.tailFibre_subset _ _)
                    (PeerDependencyRelFibred.tailFibre_subset _ _) H)].
        intro H; apply mem_reduceDeps in H; apply mem_reduceDeps.
        inversion H as [| n' v' m' vs' u' HD Hu
                        | qn qv m' vs2 o' us0 u0 ws' HD2 HD1 Hu0 HTh]; subst.
        - apply (EdgeIntToDep _ _ _ n v o vs' u); [| exact Hu].
          apply DependencyRelFibred.mem_tailFibre; split; [exact HD | reflexivity].
        - apply (EdgePeer _ _ _ n v m' vs2 o us0 u ws'); [| | exact Hu0 |].
          + apply DependencyRelFibred.mem_tailFibre; split; [exact HD2 | reflexivity].
          + apply DependencyRelFibred.mem_tailFibre; split; [exact HD1 | reflexivity].
          + apply PeerDependencyRelFibred.mem_tailFibre; split; [exact HTh | reflexivity].
      Qed.

      Theorem dependees_lookupIntermediateGran : forall D Th g n v o (w : G.t),
          Reduced.dependees (reduceDeps D Th g)
            (Name.Intermediate n v o, Version.Gran w) =
          Reduced.DependeeSet.empty.
      Proof.
        intros D Th g n v o w; apply Reduced.dependees_empty_iff; intros [m ws] H.
        apply mem_reduceDeps in H; inversion H.
      Qed.

    End Lookup.
  End Reduction.

End PeerDependency.
