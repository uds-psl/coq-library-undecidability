From Undecidability.TRAKHTENBROT Require Import bpcp red_undec fo_sig.
From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts.
From Undecidability.FOL.Syntax Require Import Core.
From Undecidability.FOL.Semantics.FiniteTarski Require Fragment Full DoubleNegation.
From Undecidability.FOL Require Import FSAT Reductions.FSATd_to_FSATdc Reductions.TRAKHTENBROT_to_FSAT.

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
