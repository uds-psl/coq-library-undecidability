From Undecidability.Synthetic
     Require Import Definitions Undecidability.

From Undecidability.FOL
     Require Import Sets.binFST
                    Sets.binZF
                    Sets.Models.FST_model.
Require Import Undecidability.FOL.FST.


From Undecidability.FOL
     Require Import Reductions.binZF_to_binFST FST_undec binZF_undec.


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
