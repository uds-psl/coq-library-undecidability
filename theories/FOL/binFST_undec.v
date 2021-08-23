Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.binFST.
Require Import Undecidability.FOL.binZF_undec.
Require Import Undecidability.FOL.Reductions.binZF_to_binFST.

Theorem undecidable_entailment_binFST :
  undecidable entailment_binFST.
Proof.
  apply (undecidability_from_reducibility undecidable_entailment_binZF).
  exists ZF_to_FST. intros phi. apply reduction_entailment.
Qed.

Theorem undecidable_deduction_binFST :
  undecidable deduction_binFST.
Proof.
  apply (undecidability_from_reducibility undecidable_deduction_binZF).
  exists ZF_to_FST. intros phi. apply reduction_deduction.
Qed.
