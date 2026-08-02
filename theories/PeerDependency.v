From Stdlib Require Import MSets.
From PackageCalculus Require Import Prelude Concurrent.

Module PeerDependency (N V : UsualOrderedType) (G : UsualOrderedType).
  Module Conc := Concurrent N V G.
  Module C := Conc.C.
  Module Pkg := C.Pkg.
  Module PkgSet := C.PkgSet.
  Module VSet := C.VSet.
  Module ParentElt := Conc.ParentElt.
  Module ParentRel := Conc.ParentRel.

  Module PeerElt := PairUOT Pkg C.Dependees.
  Module PeerRel := FSetUOT PeerElt.
  Record IsResolution
      (R : PkgSet.t) (D : C.DepRel.t) (Th : PeerRel.t)
      (g : V.t -> G.t) (r : Pkg.t)
      (S : PkgSet.t) (pi : ParentRel.t) : Prop :=
    { res_concurrent : Conc.IsResolution R D g r S pi
    ; res_peer_satisfaction :
        forall p, PkgSet.In p S ->
        forall (n : N.t) (vs : VSet.t),
          PeerRel.In (p, (n, vs)) Th ->
          forall q, ParentRel.In (p, q) pi ->
          forall (us : VSet.t), C.DepRel.In (q, (n, us)) D ->
          forall v, VSet.In v us -> ParentRel.In ((n, v), q) pi ->
            VSet.In v vs }.

  Module Reduction.
    Module PkgEqb := UOTEqb Pkg.
    Module NEqb := UOTEqb N.
    Definition hasDepOnb (D : C.DepRel.t) (p : Pkg.t) (n : N.t) : bool :=
      C.DepRel.exists_ (fun '(q, (m, _)) =>
          andb (PkgEqb.eqb q p) (NEqb.eqb m n))
        D.

    Lemma hasDepOnb_iff : forall D (p : Pkg.t) (n : N.t),
        hasDepOnb D p n = true <-> exists ws, C.DepRel.In (p, (n, ws)) D.
    Proof.
      intros D p m; unfold hasDepOnb.
      rewrite C.DepRel.exists_spec'.
      split.
      - intros [e [He Hb]]; destruct e as [q [m' ws]]; cbn [fst snd] in Hb.
        apply Bool.andb_true_iff in Hb; destruct Hb as [H1 H2].
        apply PkgEqb.eqb_true_iff in H1 as ->.
        apply NEqb.eqb_true_iff in H2 as ->.
        exists ws; exact He.
      - intros [ws He]; exists (p, (m, ws)); split; [exact He |].
        cbn [fst snd]; rewrite PkgEqb.eqb_refl, NEqb.eqb_refl; reflexivity.
    Qed.

    Module T := Conc.Reduction.T.
    Module Name := Conc.Reduction.Name.
    Module Version := Conc.Reduction.Version.
    Module SOvtp := Conc.Reduction.SOvtp.

    Module SOetp := SetOps PeerElt T.Pkg PeerRel T.PkgSet.
    Definition peerReals (D : C.DepRel.t) (Th : PeerRel.t)
        (n : N.t) (v : V.t) (o : N.t) (u : V.t) : T.PkgSet.t :=
      SOetp.unionMap (fun '(q, (m, ws)) =>
          if Pkg.eq_dec q (o, u)
          then if hasDepOnb D (n, v) m
               then SOvtp.map (fun w =>
                        (Name.Intermediate n v m, Version.Orig w))
                      ws
               else T.PkgSet.empty
          else T.PkgSet.empty)
        Th.

    Definition peerRealsOfVS (D : C.DepRel.t) (Th : PeerRel.t)
        (n : N.t) (v : V.t) (o : N.t) (us : VSet.t) : T.PkgSet.t :=
      SOvtp.unionMap (peerReals D Th n v o) us.

    Module SOdtp := Conc.Reduction.SOdtp.
    Definition reduceRealIntermediate (D : C.DepRel.t) : T.PkgSet.t :=
      SOdtp.unionMap (fun '((n, v), (m, vs)) =>
          SOvtp.map (fun u => (Name.Intermediate n v m, Version.Orig u)) vs)
        D.

    Definition reduceRealPeer (D : C.DepRel.t) (Th : PeerRel.t) : T.PkgSet.t :=
      SOdtp.unionMap (fun '((n, v), (o, us)) => peerRealsOfVS D Th n v o us) D.

    Definition reduceReal (R : PkgSet.t) (D : C.DepRel.t) (Th : PeerRel.t)
        (g : V.t -> G.t) : T.PkgSet.t :=
      T.PkgSet.union (Conc.Reduction.embedSet g R)
        (T.PkgSet.union (reduceRealIntermediate D) (reduceRealPeer D Th)).

    Module SOetd := SetOps PeerElt T.DepElt PeerRel T.DepRel.
    Definition peerEdges (D : C.DepRel.t) (Th : PeerRel.t)
        (n : N.t) (v : V.t) (o : N.t) (u : V.t) : T.DepRel.t :=
      SOetd.filterMap (fun '(q, (m, ws)) =>
          if Pkg.eq_dec q (o, u)
          then if hasDepOnb D (n, v) m
               then Some ((Name.Intermediate n v o, Version.Orig u),
                          (Name.Intermediate n v m,
                           Conc.Reduction.embedVS ws))
               else None
          else None)
        Th.

    Module SOvtd := Conc.Reduction.SOvtd.
    Definition peerEdgesOfVS (D : C.DepRel.t) (Th : PeerRel.t)
        (n : N.t) (v : V.t) (o : N.t) (us : VSet.t) : T.DepRel.t :=
      SOvtd.unionMap (peerEdges D Th n v o) us.

    Module SOdtd := Conc.Reduction.SOdtd.
    Definition reduceDepsDepToInt (D : C.DepRel.t) (g : V.t -> G.t) :
        T.DepRel.t :=
      SOdtd.map (fun '((n, v), (m, vs)) =>
          ((Name.Granular n (g v), Version.Orig v),
           (Name.Intermediate n v m, Conc.Reduction.embedVS vs)))
        D.

    Definition reduceDepsIntToDep (D : C.DepRel.t) (g : V.t -> G.t) :
        T.DepRel.t :=
      SOdtd.unionMap (fun '((n, v), (m, vs)) =>
          SOvtd.map (fun u =>
              ((Name.Intermediate n v m, Version.Orig u),
               (Name.Granular m (g u), T.VSet.singleton (Version.Orig u))))
            vs)
        D.

    Definition reduceDepsPeer (D : C.DepRel.t) (Th : PeerRel.t) : T.DepRel.t :=
      SOdtd.unionMap (fun '((n, v), (o, us)) => peerEdgesOfVS D Th n v o us) D.

    Definition reduceDeps (D : C.DepRel.t) (Th : PeerRel.t) (g : V.t -> G.t) :
        T.DepRel.t :=
      T.DepRel.union (reduceDepsDepToInt D g)
        (T.DepRel.union (reduceDepsIntToDep D g) (reduceDepsPeer D Th)).

    Module SOdpp := Conc.Reduction.SOdpp.
    Module SOvpp := Conc.Reduction.SOvpp.
    Definition parents (D : C.DepRel.t) (g : V.t -> G.t) (S : T.PkgSet.t) :
        ParentRel.t :=
      SOdpp.unionMap (fun '((n, v), (m, vs)) =>
          SOvpp.filterMap (fun u =>
              if andb (T.PkgSet.mem
                         (Name.Intermediate n v m, Version.Orig u) S)
                   (T.PkgSet.mem
                      (Name.Granular n (g v), Version.Orig v) S)
              then Some ((m, u), (n, v))
              else None)
            vs)
        D.

    Lemma mem_parents : forall D g S (pair : ParentElt.t),
        ParentRel.In pair (parents D g S) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\
          T.PkgSet.In (Name.Granular n (g v), Version.Orig v) S /\
          VSet.In u vs /\
          T.PkgSet.In (Name.Intermediate n v m, Version.Orig u) S /\
          pair = ((m, u), (n, v)).
    Proof.
      intros D g S pair; unfold parents; rewrite SOdpp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        apply SOvpp.mem_filterMap in Hh; destruct Hh as [u [Hu Hc]];
          cbn beta iota in Hc.
        destruct (andb (T.PkgSet.mem
                          (Name.Intermediate n v m, Version.Orig u) S)
                    (T.PkgSet.mem
                       (Name.Granular n (g v), Version.Orig v) S)) eqn:Hb;
          [| discriminate].
        injection Hc as <-.
        apply Bool.andb_true_iff in Hb; destruct Hb as [H1 H2].
        apply T.PkgSet.mem_spec in H1, H2.
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [HvS [Hu [HuS ->]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvpp.mem_filterMap; exists u; split; [exact Hu | cbn beta iota].
        assert (andb (T.PkgSet.mem
                        (Name.Intermediate n v m, Version.Orig u) S)
                  (T.PkgSet.mem
                     (Name.Granular n (g v), Version.Orig v) S) = true) as ->
          by (apply Bool.andb_true_iff; split;
              apply T.PkgSet.mem_spec; assumption).
        reflexivity.
    Qed.

    Lemma mem_reduceRealIntermediate : forall D y,
        T.PkgSet.In y (reduceRealIntermediate D) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          y = (Name.Intermediate n v m, Version.Orig u).
    Proof.
      intros D y; unfold reduceRealIntermediate; rewrite SOdtp.mem_unionMap.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        apply SOvtp.mem_map in Hh; destruct Hh as [u [Hu ->]].
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [Hu ->]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        apply SOvtp.mem_map; exists u; split; [exact Hu | reflexivity].
    Qed.

    Lemma mem_peerReals : forall D Th n v o u y,
        T.PkgSet.In y (peerReals D Th n v o u) <->
        exists m ws w,
          PeerRel.In ((o, u), (m, ws)) Th /\ hasDepOnb D (n, v) m = true /\
          VSet.In w ws /\ y = (Name.Intermediate n v m, Version.Orig w).
    Proof.
      intros D Th n v o u y; unfold peerReals; rewrite SOetp.mem_unionMap.
      split.
      - intros [[q [m ws]] [HtTh Hh]]; cbn beta iota in Hh.
        destruct (Pkg.eq_dec q (o, u)) as [-> | NE];
          [| destruct (SOvtp.empty_in _ Hh)].
        destruct (hasDepOnb D (n, v) m) eqn:Hb;
          [| destruct (SOvtp.empty_in _ Hh)].
        apply SOvtp.mem_map in Hh; destruct Hh as [w [Hw ->]].
        exists m, ws, w; repeat split; assumption.
      - intros [m [ws [w [HTh [Hb [Hw ->]]]]]].
        exists ((o, u), (m, ws)); split; [exact HTh | cbn beta iota].
        destruct (Pkg.eq_dec (o, u) (o, u)) as [_ | NE];
          [| contradiction NE; reflexivity].
        rewrite Hb.
        apply SOvtp.mem_map; exists w; split; [exact Hw | reflexivity].
    Qed.

    Lemma mem_peerRealsOfVS : forall D Th n v o us y,
        T.PkgSet.In y (peerRealsOfVS D Th n v o us) <->
        exists u m ws w,
          VSet.In u us /\ PeerRel.In ((o, u), (m, ws)) Th /\
          hasDepOnb D (n, v) m = true /\ VSet.In w ws /\
          y = (Name.Intermediate n v m, Version.Orig w).
    Proof.
      intros D Th n v o us y; unfold peerRealsOfVS;
        rewrite SOvtp.mem_unionMap.
      split.
      - intros [u [Hu Hh]]; apply mem_peerReals in Hh.
        destruct Hh as [m [ws [w [HTh [Hb [Hw ->]]]]]].
        exists u, m, ws, w; repeat split; assumption.
      - intros [u [m [ws [w [Hu [HTh [Hb [Hw ->]]]]]]]].
        exists u; split; [exact Hu |].
        apply mem_peerReals; exists m, ws, w; repeat split; assumption.
    Qed.

    Lemma mem_reduceRealPeer : forall D Th y,
        T.PkgSet.In y (reduceRealPeer D Th) <->
        exists n v o us u m ws w,
          C.DepRel.In ((n, v), (o, us)) D /\ VSet.In u us /\
          PeerRel.In ((o, u), (m, ws)) Th /\ hasDepOnb D (n, v) m = true /\
          VSet.In w ws /\ y = (Name.Intermediate n v m, Version.Orig w).
    Proof.
      intros D Th y; unfold reduceRealPeer; rewrite SOdtp.mem_unionMap.
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
    Lemma mem_reduceReal : forall R D Th g q,
        T.PkgSet.In q (reduceReal R D Th g) <->
        (exists p, PkgSet.In p R /\ q = Conc.Reduction.embedPkg g p) \/
        ((exists n v m vs u,
             C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
             q = (Name.Intermediate n v m, Version.Orig u)) \/
         (exists n v o us u m ws w,
             C.DepRel.In ((n, v), (o, us)) D /\ VSet.In u us /\
             PeerRel.In ((o, u), (m, ws)) Th /\
             hasDepOnb D (n, v) m = true /\ VSet.In w ws /\
             q = (Name.Intermediate n v m, Version.Orig w))).
    Proof.
      intros R D Th g q; unfold reduceReal, Conc.Reduction.embedSet.
      rewrite !T.PkgSet.union_spec, SOptp.mem_map,
        mem_reduceRealIntermediate, mem_reduceRealPeer.
      reflexivity.
    Qed.

    Lemma embedPkg_mem_reduceReal : forall g (p : Pkg.t) R D Th,
        T.PkgSet.In (Conc.Reduction.embedPkg g p) (reduceReal R D Th g) ->
        PkgSet.In p R.
    Proof.
      intros g p R D Th H; apply mem_reduceReal in H.
      destruct H as [[q [HqR Hq]] | [H | H]].
      - apply Conc.Reduction.embedPkg_injective in Hq; subst q; exact HqR.
      - destruct H as [n [v [m [vs [u [_ [_ Hq]]]]]]].
        destruct p as [pn pv];
          unfold Conc.Reduction.embedPkg in Hq; simpl in Hq.
        injection Hq as Hq _; discriminate.
      - destruct H as [n [v [o [us [u [m [ws [w [_ [_ [_ [_ [_ Hq]]]]]]]]]]]]].
        destruct p as [pn pv];
          unfold Conc.Reduction.embedPkg in Hq; simpl in Hq.
        injection Hq as Hq _; discriminate.
    Qed.

    Lemma mem_reduceDepsDepToInt : forall D g y,
        T.DepRel.In y (reduceDepsDepToInt D g) <->
        exists n v m vs,
          C.DepRel.In ((n, v), (m, vs)) D /\
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
        T.DepRel.In y (reduceDepsIntToDep D g) <->
        exists n v m vs u,
          C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
          y = ((Name.Intermediate n v m, Version.Orig u),
               (Name.Granular m (g u),
                T.VSet.singleton (Version.Orig u))).
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
        T.DepRel.In y (peerEdges D Th n v o u) <->
        exists m ws,
          PeerRel.In ((o, u), (m, ws)) Th /\ hasDepOnb D (n, v) m = true /\
          y = ((Name.Intermediate n v o, Version.Orig u),
               (Name.Intermediate n v m, Conc.Reduction.embedVS ws)).
    Proof.
      intros D Th n v o u y; unfold peerEdges; rewrite SOetd.mem_filterMap.
      split.
      - intros [[q [m ws]] [HtTh Hh]]; cbn beta iota in Hh.
        destruct (Pkg.eq_dec q (o, u)) as [-> | NE]; [| discriminate].
        destruct (hasDepOnb D (n, v) m) eqn:Hb; [| discriminate].
        injection Hh as <-.
        exists m, ws; repeat split; assumption.
      - intros [m [ws [HTh [Hb ->]]]].
        exists ((o, u), (m, ws)); split; [exact HTh | cbn beta iota].
        destruct (Pkg.eq_dec (o, u) (o, u)) as [_ | NE];
          [| contradiction NE; reflexivity].
        rewrite Hb; reflexivity.
    Qed.

    Lemma mem_peerEdgesOfVS : forall D Th n v o us y,
        T.DepRel.In y (peerEdgesOfVS D Th n v o us) <->
        exists u m ws,
          VSet.In u us /\ PeerRel.In ((o, u), (m, ws)) Th /\
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
        T.DepRel.In y (reduceDepsPeer D Th) <->
        exists n v o us u m ws,
          C.DepRel.In ((n, v), (o, us)) D /\ VSet.In u us /\
          PeerRel.In ((o, u), (m, ws)) Th /\ hasDepOnb D (n, v) m = true /\
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

    Lemma mem_reduceDeps : forall D Th g y,
        T.DepRel.In y (reduceDeps D Th g) <->
        (exists n v m vs,
            C.DepRel.In ((n, v), (m, vs)) D /\
            y = ((Name.Granular n (g v), Version.Orig v),
                 (Name.Intermediate n v m, Conc.Reduction.embedVS vs))) \/
        ((exists n v m vs u,
             C.DepRel.In ((n, v), (m, vs)) D /\ VSet.In u vs /\
             y = ((Name.Intermediate n v m, Version.Orig u),
                  (Name.Granular m (g u),
                   T.VSet.singleton (Version.Orig u)))) \/
         (exists n v o us u m ws,
             C.DepRel.In ((n, v), (o, us)) D /\ VSet.In u us /\
             PeerRel.In ((o, u), (m, ws)) Th /\
             hasDepOnb D (n, v) m = true /\
             y = ((Name.Intermediate n v o, Version.Orig u),
                  (Name.Intermediate n v m, Conc.Reduction.embedVS ws)))).
    Proof.
      intros D Th g y; unfold reduceDeps.
      rewrite !T.DepRel.union_spec, mem_reduceDepsDepToInt,
        mem_reduceDepsIntToDep, mem_reduceDepsPeer.
      reflexivity.
    Qed.

    Lemma mem_reduceDeps_dep_to_int : forall D Th g n v m vs,
        C.DepRel.In ((n, v), (m, vs)) D ->
        T.DepRel.In ((Name.Granular n (g v), Version.Orig v),
                     (Name.Intermediate n v m, Conc.Reduction.embedVS vs))
          (reduceDeps D Th g).
    Proof.
      intros; apply mem_reduceDeps.
      left; exists n, v, m, vs; split; [assumption | reflexivity].
    Qed.

    Lemma mem_reduceDeps_int_to_dep : forall D Th g n v m vs u0,
        C.DepRel.In ((n, v), (m, vs)) D -> VSet.In u0 vs ->
        T.DepRel.In ((Name.Intermediate n v m, Version.Orig u0),
                     (Name.Granular m (g u0),
                      T.VSet.singleton (Version.Orig u0)))
          (reduceDeps D Th g).
    Proof.
      intros; apply mem_reduceDeps.
      right; left; exists n, v, m, vs, u0; repeat split; assumption.
    Qed.

    Lemma mem_reduceDeps_peer : forall D Th g qn qv o vs1 m' ws' ou,
        C.DepRel.In ((qn, qv), (o, vs1)) D ->
        VSet.In ou vs1 ->
        PeerRel.In ((o, ou), (m', ws')) Th ->
        (exists vs2, C.DepRel.In ((qn, qv), (m', vs2)) D) ->
        T.DepRel.In ((Name.Intermediate qn qv o, Version.Orig ou),
                     (Name.Intermediate qn qv m', Conc.Reduction.embedVS ws'))
          (reduceDeps D Th g).
    Proof.
      intros D Th g qn qv o vs1 m' ws' ou HD Hou HTh Hpar.
      apply mem_reduceDeps.
      right; right; exists qn, qv, o, vs1, ou, m', ws';
        repeat split; try assumption.
      apply hasDepOnb_iff; exact Hpar.
    Qed.

    Module SOvcv := Conc.Reduction.SOvcv.
    Theorem peer_soundness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (Th : PeerRel.t)
             (g : V.t -> G.t) (r : Pkg.t) (S : T.PkgSet.t),
        T.IsResolution (reduceReal R D Th g) (reduceDeps D Th g)
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
          exists u; split.
          { split; [exact Hu | split].
            - apply Conc.Reduction.mem_concurrentResolution; exact Hcv2S.
            - apply mem_parents.
              exists pn, pv, m, vs, u; repeat split; assumption. }
          { intros u' [Hu' [Hu'S Hpi']].
            apply mem_parents in Hpi'.
            destruct Hpi'
              as [n' [v' [m' [vs' [u'' [Hdep' [_ [_ [HiS' Heq]]]]]]]]].
            injection Heq as -> -> -> ->.
            pose proof (Huniq _ _ _ HiS' HcvS) as He.
            injection He as He; congruence. }
        + intros n v v' Hv Hv' Hne Hg.
          apply Conc.Reduction.mem_concurrentResolution in Hv, Hv';
            unfold Conc.Reduction.embedPkg in Hv, Hv';
            simpl in Hv, Hv'.
          rewrite Hg in Hv.
          pose proof (Huniq _ _ _ Hv Hv') as He.
          injection He as He; exact (Hne He).
        + intros c p0 Hcp.
          apply mem_parents in Hcp.
          destruct Hcp as [n [v [m [vs [u [HD [HvS [Hu [HiS Heq]]]]]]]]].
          injection Heq as -> ->.
          split; [| apply Conc.Reduction.mem_concurrentResolution; exact HvS].
          destruct (Hdep _ HiS _ _
              (mem_reduceDeps_int_to_dep D Th g n v m vs u HD Hu))
            as [cv [Hcv HcvS]].
          apply SOvcv.singleton_in in Hcv; subst cv.
          apply Conc.Reduction.mem_concurrentResolution; exact HcvS.
      - intros p Hp n vs HTh q Hpq us Hqus v Hv Hnvq.
        apply mem_parents in Hpq.
        destruct Hpq as [qn [qv [o [vs1 [ou [HD1 [HqS [Hou [HiS Heq]]]]]]]]].
        injection Heq as -> ->.
        apply mem_parents in Hnvq.
        destruct Hnvq
          as [qn' [qv' [n' [us' [v' [HD2 [_ [Hv' [HvS Heq2]]]]]]]]].
        injection Heq2 as -> -> -> ->.
        destruct (Hdep _ HiS _ _
            (mem_reduceDeps_peer D Th g qn' qv' o vs1 n' vs ou HD1 Hou HTh
               (ex_intro _ us Hqus)))
          as [cv [Hcv HcvS]].
        unfold Conc.Reduction.embedVS in Hcv; apply SOvcv.mem_map in Hcv;
          destruct Hcv as [w [Hw ->]].
        pose proof (Huniq _ _ _ HvS HcvS) as He.
        injection He as <-; exact Hw.
    Qed.

    Definition coreResolution (S : PkgSet.t) (pi : ParentRel.t)
        (D : C.DepRel.t) (g : V.t -> G.t) : T.PkgSet.t :=
      T.PkgSet.union (SOptp.map (Conc.Reduction.embedPkg g) S)
        (SOdtp.unionMap (fun '((n, v), (m, vs)) =>
             if PkgSet.mem (n, v) S
             then SOvtp.filterMap (fun u =>
                      if andb (PkgSet.mem (m, u) S)
                           (ParentRel.mem ((m, u), (n, v)) pi)
                      then Some (Name.Intermediate n v m, Version.Orig u)
                      else None)
                    vs
             else T.PkgSet.empty)
           D).

    Lemma mem_coreResolution : forall S pi D g (q : T.Pkg.t),
        T.PkgSet.In q (coreResolution S pi D g) <->
        (exists n v, PkgSet.In (n, v) S /\
           q = (Name.Granular n (g v), Version.Orig v)) \/
        (exists n v m vs u,
           C.DepRel.In ((n, v), (m, vs)) D /\ PkgSet.In (n, v) S /\
           PkgSet.In (m, u) S /\ VSet.In u vs /\
           ParentRel.In ((m, u), (n, v)) pi /\
           q = (Name.Intermediate n v m, Version.Orig u)).
    Proof.
      intros S pi D g q; unfold coreResolution.
      rewrite T.PkgSet.union_spec, SOptp.mem_map, SOdtp.mem_unionMap.
      assert (Hfst :
        (exists p, PkgSet.In p S /\ q = Conc.Reduction.embedPkg g p) <->
        (exists n v, PkgSet.In (n, v) S /\
           q = (Name.Granular n (g v), Version.Orig v))).
      { split.
        - intros [[n v] [HpS ->]];
            exists n, v; split; [exact HpS | reflexivity].
        - intros [n [v [HnS ->]]]; exists (n, v); auto. }
      rewrite Hfst; apply or_iff_compat_l.
      split.
      - intros [[[n v] [m vs]] [HeD Hh]]; cbn beta iota in Hh.
        destruct (PkgSet.mem (n, v) S) eqn:Hnv;
          [| destruct (SOdtp.empty_in _ Hh)].
        apply PkgSet.mem_spec in Hnv.
        apply SOvtp.mem_filterMap in Hh; destruct Hh as [u [Hu Hc]];
          cbn beta iota in Hc.
        destruct (andb (PkgSet.mem (m, u) S)
                    (ParentRel.mem ((m, u), (n, v)) pi)) eqn:Hb;
          [| discriminate].
        injection Hc as <-.
        apply Bool.andb_true_iff in Hb; destruct Hb as [Hmu Hpi].
        apply PkgSet.mem_spec in Hmu; apply ParentRel.mem_spec in Hpi.
        exists n, v, m, vs, u; repeat split; assumption.
      - intros [n [v [m [vs [u [HD [Hnv [Hmu [Hu [Hpi ->]]]]]]]]]].
        exists ((n, v), (m, vs)); split; [exact HD | cbn beta iota].
        assert (PkgSet.mem (n, v) S = true) as ->
          by (apply PkgSet.mem_spec; exact Hnv).
        apply SOvtp.mem_filterMap; exists u; split; [exact Hu | cbn beta iota].
        assert (andb (PkgSet.mem (m, u) S)
                  (ParentRel.mem ((m, u), (n, v)) pi) = true) as ->
          by (apply Bool.andb_true_iff; split;
              [apply PkgSet.mem_spec; exact Hmu
              | apply ParentRel.mem_spec; exact Hpi]).
        reflexivity.
    Qed.

    Lemma mem_coreResolution_granular : forall S pi D g n v,
        PkgSet.In (n, v) S ->
        T.PkgSet.In (Name.Granular n (g v), Version.Orig v)
          (coreResolution S pi D g).
    Proof.
      intros; apply mem_coreResolution.
      left; exists n, v; split; [assumption | reflexivity].
    Qed.

    Lemma mem_coreResolution_intermediate : forall S pi D g n v m vs u,
        C.DepRel.In ((n, v), (m, vs)) D -> PkgSet.In (n, v) S ->
        PkgSet.In (m, u) S -> VSet.In u vs ->
        ParentRel.In ((m, u), (n, v)) pi ->
        T.PkgSet.In (Name.Intermediate n v m, Version.Orig u)
          (coreResolution S pi D g).
    Proof.
      intros; apply mem_coreResolution.
      right; exists n, v, m, vs, u; repeat split; assumption.
    Qed.

    Theorem peer_completeness :
      forall (R : PkgSet.t) (D : C.DepRel.t) (Th : PeerRel.t)
             (g : V.t -> G.t) (r : Pkg.t)
             (S : PkgSet.t) (pi : ParentRel.t),
        C.FunctionalInName D ->
        IsResolution R D Th g r S pi ->
        T.IsResolution (reduceReal R D Th g) (reduceDeps D Th g)
          (Conc.Reduction.embedPkg g r) (coreResolution S pi D g).
    Proof.
      intros R D Th g r S pi Hfunc Hres.
      destruct Hres as [Hconc Hpsat].
      destruct Hconc as [Hsub Hroot Hpc Hvg Hps].
      constructor.
      - intros q Hq; apply mem_coreResolution in Hq.
        apply mem_reduceReal.
        destruct Hq as
          [[n [v [Hnv ->]]]
          | [n [v [m [vs [u [HD [Hnv [Hmu [Hu [Hpi ->]]]]]]]]]]].
        + left; exists (n, v); split; [apply Hsub; exact Hnv | reflexivity].
        + right; left; exists n, v, m, vs, u; repeat split; assumption.
      - destruct r as [rn rv].
        exact (mem_coreResolution_granular S pi D g rn rv Hroot).
      - intros q Hq md vsd Hd.
        apply mem_coreResolution in Hq.
        apply mem_reduceDeps in Hd.
        destruct Hq as
          [[n [v [Hnv ->]]]
          | [n [v [m [vs [u [HD [Hnv [Hmu [Hu [Hpi ->]]]]]]]]]]].
        + destruct Hd as [Hd | [Hd | Hd]].
          * destruct Hd as [n' [v' [m' [vs' [HD' Heq]]]]].
            injection Heq as <- Hgv <- -> ->.
            destruct (Hpc _ Hnv _ _ HD') as [u [[Huv [HmuS Hpiu]] _]].
            exists (Version.Orig u); split.
            { unfold Conc.Reduction.embedVS; apply SOvcv.mem_map;
                exists u; split; [exact Huv | reflexivity]. }
            { exact (mem_coreResolution_intermediate S pi D g n v m' vs' u
                       HD' Hnv HmuS Huv Hpiu). }
          * destruct Hd as [n' [v' [m' [vs' [u' [HD' [Hu' Heq]]]]]]].
            discriminate Heq.
          * destruct Hd as
              [n' [v' [o' [us' [u' [m' [ws' [HD' [Hu' [HTh' [Hb' Heq]]]]]]]]]]].
            discriminate Heq.
        + destruct Hd as [Hd | [Hd | Hd]].
          * destruct Hd as [n' [v' [m' [vs' [HD' Heq]]]]].
            discriminate Heq.
          * destruct Hd as [n' [v' [m' [vs' [u' [HD' [Hu' Heq]]]]]]].
            injection Heq as <- <- <- <- -> ->.
            exists (Version.Orig u); split.
            { apply SOvcv.singleton_in; reflexivity. }
            { exact (mem_coreResolution_granular S pi D g m u Hmu). }
          * destruct Hd
              as [qn [qv [o [us0 [u0 [m' [ws' [HD1 [Hu0 [HTh [Hb Heq]]]]]]]]]]].
            injection Heq as <- <- <- <- -> ->.
            apply hasDepOnb_iff in Hb; destruct Hb as [vs2 HD2].
            destruct (Hpc _ Hnv _ _ HD2) as [w [[Hw [HmwS Hpiw]] _]].
            exists (Version.Orig w); split.
            { unfold Conc.Reduction.embedVS; apply SOvcv.mem_map; exists w;
                split; [| reflexivity].
              exact (Hpsat _ Hmu _ _ HTh _ Hpi _ HD2 _ Hw Hpiw). }
            { exact (mem_coreResolution_intermediate S pi D g n v m' vs2 w
                       HD2 Hnv HmwS Hw Hpiw). }
      - intros nm cv1 cv2 H1 H2.
        apply mem_coreResolution in H1, H2.
        destruct H1 as
          [[n1 [v1 [Hm1 He1]]]
          | [n1 [v1 [m1 [vs1 [u1 [Hd1 [Hnv1 [Hmu1 [Hu1 [Hpi1 He1]]]]]]]]]]];
        destruct H2 as
          [[n2 [v2 [Hm2 He2]]]
          | [n2 [v2 [m2 [vs2 [u2 [Hd2 [Hnv2 [Hmu2 [Hu2 [Hpi2 He2]]]]]]]]]]].
        + injection He1 as -> ->; injection He2 as <- Hg ->.
          destruct (V.eq_dec v1 v2) as [-> | NE]; [reflexivity |].
          exfalso; exact (Hvg n1 v1 v2 Hm1 Hm2 NE Hg).
        + injection He1 as -> ->; discriminate He2.
        + injection He1 as -> ->; discriminate He2.
        + injection He1 as -> ->; injection He2 as <- <- <- ->.
          assert (vs2 = vs1) as -> by (exact (Hfunc _ _ _ _ Hd2 Hd1)).
          destruct (Hpc _ Hnv1 _ _ Hd1) as [w [_ Huniq1]].
          pose proof (Huniq1 u1 (conj Hu1 (conj Hmu1 Hpi1))) as E1.
          pose proof (Huniq1 u2 (conj Hu2 (conj Hmu2 Hpi2))) as E2.
          congruence.
    Qed.
  End Reduction.

End PeerDependency.
