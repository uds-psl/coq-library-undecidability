From Undecidability.TRAKHTENBROT Require Import bpcp red_undec fo_sig.
From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts.
From Undecidability.FOL.Syntax Require Import Core.
From Undecidability.FOL.Semantics.FiniteTarski Require Fragment Full DoubleNegation.
From Undecidability.FOL.Undecidability Require Import Reductions.FSATd_to_FSATdc Reductions.TRAKHTENBROT_to_FSAT.

Section Full.
  Import Full.

  Theorem FSAT_undec :
    undecidable FSAT.
  Proof.
    apply (undecidability_from_reducibility BPCP_problem_undec).
    eapply reduces_transitive; [| apply reduction].
    apply (@FULL_TRAKHTENBROT_non_informative (Σrel 2)). left. exists tt. auto.
  Qed.

  Theorem FSATd_undec :
    undecidable FSATd.
  Proof.
    apply (undecidability_from_reducibility BPCP_problem_undec).
    eapply reduces_transitive; try apply reduction_disc.
    eapply reduces_transitive; try apply (@FULL_TRAKHTENBROT_non_informative (Σrel 2)).
    - left. exists tt. auto.
    - exists (fun phi => phi). intros phi. apply red_utils.fo_form_fin_dec_SAT_discr_equiv.
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
        destruct (Hdec tt) as [f Hf].
        unshelve now eapply translate_form_correct in H.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        rewrite full_interp_inverse_1. intros ff' [] v ee. cbn.
        apply DecidabilityFacts.decidable_iff'. now exists f.
    - exists D, (tarski_full_tarski_interp I), rho; repeat split.
      + now exists l.
      + destruct I; apply Hdec.
      + destruct (Hdec tt) as [f Hf].
        unshelve now eapply translate_form_correct.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        intros ff' [] v ee. cbn.
        apply DecidabilityFacts.decidable_iff'. destruct I. now exists f.
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
        destruct (Hdec tt) as [f Hf].
        unshelve now eapply translate_form_correct in H.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        rewrite full_interp_inverse_1. intros ff' [] v ee. cbn.
        apply DecidabilityFacts.decidable_iff'. now exists f.
    - exists D, (tarski_full_tarski_interp I), rho; repeat split.
      + now exists l.
      + easy.
      + destruct I; apply Hdec.
      + destruct (Hdec tt) as [f Hf].
        unshelve now eapply translate_form_correct.
        intros ff phi rho'. apply Full.general_decider. 1: now exists l.
        intros ff' [] v ee. cbn.
        apply DecidabilityFacts.decidable_iff'. destruct I. now exists f.
  Qed.
(* TODO 
  Theorem FSATdc_undec :
    undecidable FSATdc.
  Proof.
   apply (undecidability_from_reducibility FSATd_undec).
   apply FSATd_to_FSATdc.reduction.
  Qed. *)
End Fragment.
