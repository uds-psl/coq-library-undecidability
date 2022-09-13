(** ** Trakhtenbrot's Theorem *)

From Undecidability.PCP Require Import PCP_undec.
From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts.
From Undecidability.FOL.Semantics.FiniteTarski Require Import Full.
From Undecidability.FOL.Undecidability Require Import Reductions.FSATd_to_FSATdc Reductions.PCPb_to_FSAT.


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
