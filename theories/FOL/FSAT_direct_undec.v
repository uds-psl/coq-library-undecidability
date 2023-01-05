(** ** Trakhtenbrot's Theorem *)

From Undecidability.PCP Require Import PCP_undec.
From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts DecidabilityFacts.
From Undecidability.FOL.Semantics.FiniteTarski Require Fragment Full DoubleNegation.
From Undecidability.FOL Require Import FSAT Reductions.FSATd_to_FSATdc Reductions.PCPb_to_FSAT.

Section Full.
  Import Full.
  Theorem FSAT_undec :
    undecidable FSAT.
  Proof.
    apply (undecidability_from_reducibility dPCPb_undec).
    exists (finsat_formula). intros x. apply FSAT_reduction.
  Qed.

  Theorem FSATd_undec :
    undecidable FSATd.
  Proof. 
    apply (undecidability_from_reducibility dPCPb_undec).
    exists (finsat_formula). intros x. apply FSATd_reduction.
  Qed.

  Theorem FSATdc_undec :
    undecidable FSATdc.
  Proof.
   apply (undecidability_from_reducibility FSATd_undec).
   apply FSATd_to_FSATdc.reduction.
  Qed.
End Full.


Section Fragment.
  Import Fragment DoubleNegation.

  Theorem FSAT_undec_frag :
    undecidable FSAT.
  Proof.
    apply (undecidability_from_reducibility (FSAT_undec)).
    exists translate_form.
    intros k. split; intros (D & I & rho & (l & Hlist) & Hdec & H).
    - exists D, (full_tarski_tarski_interp I), rho; repeat split.
      + now exists l.
      + destruct I; apply Hdec.
      + rewrite <- (full_interp_inverse_1 I) in H.
        destruct (Hdec FSAT.P) as [fP HfP].
        destruct (Hdec FSAT.less) as [fL HfL].
        destruct (Hdec FSAT.equiv) as [fE HfE].
        unshelve now eapply translate_form_correct in H.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        rewrite full_interp_inverse_1. intros ff' [] v ee; cbn;
        apply DecidabilityFacts.decidable_iff'.
        1: now exists fP. 1: now exists fL. now exists fE.
    - exists D, (tarski_full_tarski_interp I), rho; repeat split.
      + now exists l.
      + destruct I; apply Hdec.
      + destruct (Hdec FSAT.P) as [fP HfP].
        destruct (Hdec FSAT.less) as [fL HfL].
        destruct (Hdec FSAT.equiv) as [fE HfE].
        unshelve now eapply translate_form_correct.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        intros ff' [] v ee; cbn;
        apply DecidabilityFacts.decidable_iff'; destruct I.
        1: now exists fP. 1: now exists fL. now exists fE.
  Qed.

  Theorem FSATd_undec_frag :
    undecidable FSATd.
  Proof.
    apply (undecidability_from_reducibility (FSATd_undec)).
    exists translate_form.
    intros k. split; intros (D & I & rho & (l & Hlist) & Hdisc & Hdec & H).
    - exists D, (full_tarski_tarski_interp I), rho; repeat split.
      + now exists l.
      + easy.
      + destruct I; apply Hdec.
      + rewrite <- (full_interp_inverse_1 I) in H.
        destruct (Hdec FSAT.P) as [fP HfP].
        destruct (Hdec FSAT.less) as [fL HfL].
        destruct (Hdec FSAT.equiv) as [fE HfE].
        unshelve now eapply translate_form_correct in H.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        rewrite full_interp_inverse_1. intros ff' [] v ee; cbn;
        apply DecidabilityFacts.decidable_iff'.
        1: now exists fP. 1: now exists fL. now exists fE.
    - exists D, (tarski_full_tarski_interp I), rho; repeat split.
      + now exists l.
      + easy.
      + destruct I; apply Hdec.
      + destruct (Hdec FSAT.P) as [fP HfP].
        destruct (Hdec FSAT.less) as [fL HfL].
        destruct (Hdec FSAT.equiv) as [fE HfE].
        unshelve now eapply translate_form_correct.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        intros ff' [] v ee; cbn;
        apply DecidabilityFacts.decidable_iff'; destruct I.
        1: now exists fP. 1: now exists fL. now exists fE.
  Qed.

  Theorem FSATdc_undec_frag :
    undecidable FSATdc.
  Proof.
    apply (undecidability_from_reducibility FSATdc_undec).
    unshelve eexists translate_form_closed. 1-2: unfold Dec.dec; repeat decide equality.
    intros [k Hclosed]. split; intros (D & I & rho & (l & Hlist) & Hdisc & Hdec & H).
    - exists D, (full_tarski_tarski_interp I), rho; repeat split.
      + now exists l.
      + easy.
      + destruct I; apply Hdec.
      + rewrite <- (full_interp_inverse_1 I) in H.
        destruct (Hdec FSAT.P) as [fP HfP].
        destruct (Hdec FSAT.less) as [fL HfL].
        destruct (Hdec FSAT.equiv) as [fE HfE].
        unshelve now eapply translate_form_correct in H.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        rewrite full_interp_inverse_1. intros ff' [] v ee; cbn;
        apply DecidabilityFacts.decidable_iff'.
        1: now exists fP. 1: now exists fL. now exists fE.
    - exists D, (tarski_full_tarski_interp I), rho; repeat split.
      + now exists l.
      + easy.
      + destruct I; apply Hdec.
      + destruct (Hdec FSAT.P) as [fP HfP].
        destruct (Hdec FSAT.less) as [fL HfL].
        destruct (Hdec FSAT.equiv) as [fE HfE].
        unshelve now eapply translate_form_correct.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        intros ff' [] v ee; cbn;
        apply DecidabilityFacts.decidable_iff'; destruct I.
        1: now exists fP. 1: now exists fL. now exists fE.
  Qed.
End Fragment.
