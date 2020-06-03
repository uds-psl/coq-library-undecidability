From Undecidability.FOLC Require Import WKL Markov GenTarski GenCompleteness Stability.

(* Theorem 15 *)

Lemma completeness_iff_XM :
  completeness (fun _ _ => True) (@SM) <-> XM.
Proof.
  assert (XM <-> DN) as ->. {
    split.
    - intros xm P H. destruct (xm P); tauto.
    - intros dne P. eapply dne. tauto.
  }
  split.
  - intros H P.
    eapply sta_to_dn. red. red. intros Sigma T phi clT clphi (HdF & HdP & HeF & HeP & _).
    eapply completeness_standard_stability; eauto.
  - intros dne Sigma HdF HdP HeF HeP T clT _ phi clphi.
    eapply completeness_standard_stability; eauto.
Qed.

Lemma completeness_enum_iff_MP : 
  completeness (fun Sigma T => enumerable T) (@SM) <-> MP.
Proof.
  split.
  - intros H P.
    eapply ste_to_mp. red. red. intros Sigma T phi clT clphi (? & ? & ? & ? & ? & ?).
    eapply completeness_standard_stability; eauto.
    intros. eapply H; eauto.
    eapply enum_count; eauto.
  - intros dne Sigma HdF HdP HeF HeP T clT He phi clphi.
    eapply completeness_standard_stability; eauto.
    eapply mp_to_ste; eauto.
    exists HdF, HdP, HeF, HeP. eapply enumerable_enum; eauto.
Qed.

Lemma completeness_context_iff_MPL : 
  completeness (fun Sigma T => exists A, forall phi : form, phi ∈ T <-> phi el A) (@SM) <-> MPL.
Proof.
  split.
  - intros H P.
    eapply halt_cprv_stable.
    intros (Sigma & [[[[] []] A] phi]). cbn.
    epose proof (H Sigma d d0 e e0 (fun x => In x A) _ (ltac:(exists A; reflexivity)) phi _) as Hcomp.
    eapply completeness_standard_stability in Hcomp.
    + intros ?. destruct Hcomp.
      * intros ?. eapply H0. intros H2. eapply H1. exists A. firstorder.
      * eapply Weak. eapply H1. eapply H1.
    + admit.
    + admit.
  - intros dne Sigma HdF HdP HeF HeP T clT (A & HA) phi clphi.
    eapply completeness_standard_stability; eauto.
    enough (stable (A ⊢CE phi)).
    + intros ?. exists A. split.
      * intros ? ?. now eapply HA.
      * eapply H. intros ?. eapply H0. intros [B HB].
        eapply H1. eapply Weak. eapply HB. intros ? ? % HB. now eapply HA.
    + admit. (* eapply eapply cprv_iprv_stable. *)
    (* eapply mp_to_ste; eauto.  *)
    (* exists HdF, HdP, HeF, HeP. eapply enumerable_enum; eauto. *)
Admitted.

(* Theorem 42

  (1a)    (1b)
   ^       ^
   |       |
   v       v
  (2a) -> (2b)
   |       |
   v       v
  (3a)    (3b)
    \      /
     \    /
      \  /
       vv
       (4)
        |
        v
       (5)
        |
        v
       (2a)

*)

Lemma completeness_transport (CT : forall Sigma, @theory Sigma -> Prop) (C1 C2 : forall Sigma D, @interp Sigma D -> Prop) :
  (forall Sigma D I, C2 Sigma D I -> C1 Sigma D I) ->
  completeness CT C2 -> completeness CT C1.
Proof.
  intros HImpl Hcomp Sigma HdF HdP HeF HeP T T_closed TC phi clphi HH.
  eapply Hcomp; eauto.
  intros ? ? ? ? ?; eauto.
Qed.

Lemma modex_comp  (C : forall Sigma D, @interp Sigma D -> Prop) :
  (forall Sigma D I, C Sigma D I -> SM I) ->
  XM -> model_existence (fun _ _ => True) C -> completeness (fun _ _ => True) C.
Proof.
  intros Himpl xm modex Sigma Hdf HdP HeF HeP T T_closed TC phi phi_closed H.
  assert (dne : forall P, ~~ P -> P). { red in xm. intros. specialize (xm P). tauto. }
  eapply dne. intros Hcons. rewrite refutation_prv in Hcons. 
  assert (Hcl : closed_T (T ⋄ (¬ phi))) by (intros ? ? [] ; subst; try econstructor; eauto; econstructor).
  eapply modex in Hcl as (D & I & rho & H1 & H2); eauto.
  eapply Himpl; eauto.
  eapply (H1 (¬ phi)). now right.
  fold sat. eapply H; firstorder.
Qed.

Lemma iff_1a_2a :
  completeness (fun _ _ => True) (@OM) <->
  XM /\ model_existence (fun _ _ => True) (@OM).
Proof.
  split.
  - intros ?. 
    assert (xm : XM). {
      eapply completeness_iff_XM.
      eapply completeness_transport.
      2:eauto. intros ? ? ? ?.
      econstructor. eapply omniscient_to_classical. eapply H0. eapply H0.
    }
    split.
    + eauto.
    + eapply comp_modex; eauto.
  - intros [xm modex].
    eapply modex_comp; firstorder.
Qed.

Lemma iff_1b_2b :
  completeness (fun _ _ => True) (@DM) <->
  XM /\ model_existence (fun _ _ => True) (@DM).
Proof.
  split.
  - intros ?. 
    assert (xm : XM). {
      eapply completeness_iff_XM.
      eapply completeness_transport.
      2:eauto. intros ? ? ? ?.
      eapply H0.
    }
    split.
    + eauto.
    + eapply comp_modex; eauto.
  - intros [xm modex].
    eapply modex_comp; firstorder.
Qed.

Lemma impl_2a_2b :
  model_existence (fun _ _ => True) (@OM) -> model_existence (fun _ _ => True) (@DM).
Proof.
  eapply modex_impl_OM_DM.
Qed.

Lemma impl_2a_3a :
  model_existence (fun _ _ => True) (@OM) -> compactness (fun _ _ => True) (@OM).
Proof.
  eapply modex_compact; firstorder.
Qed.

Lemma impl_2b_3b :
  model_existence (fun _ _ => True) (@DM) -> compactness (fun _ _ => True) (@DM).
Proof.
  eapply modex_compact; firstorder.
Qed.

Lemma impl_3a_4 :
  XM -> compactness (fun _ _ => True) (@OM) -> WKL (fun _ => True).
Proof.
  eapply compact_OM_implies_WKL.
Qed.

Lemma impl_3b_4 :
  XM -> compactness (fun _ _ => True) (@DM) -> WKL (fun _ => True).
Proof.
  eapply compact_implies_WKL.
Qed.

Lemma impl_4_5 :
  XM -> WKL (fun _ => True) -> (forall X, forall p : X -> Prop, discrete X -> enumerable__T X -> decidable p).
Proof.
  intros. eapply CO_iff_EM_WKL; eauto.
Qed.

Lemma impl_5_2a :
  XM -> (forall X, forall p : X -> Prop, discrete X -> enumerable__T X -> decidable p) -> model_existence (fun _ _ => True) (@OM).
Proof.
  intros. eapply PCO_implies_modex; eauto.
  intros. eapply H0. eapply discrete_iff. econstructor. eauto.
  eapply enum_enumT. econstructor. eauto.
Qed.

(* Theorem 56 *)
