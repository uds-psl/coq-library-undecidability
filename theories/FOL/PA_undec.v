Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.PA.
From Undecidability.FOL.Util Require Import FullTarski.
From Undecidability.H10 Require Import H10p H10p_undec.
From Undecidability.FOL.Reductions Require Import H10p_to_FA.



Theorem H10_entailment_FA : H10p_SAT ⪯ entailment_FA.
Proof.
  exists embed. intros E. apply H10p_to_FA_sat.
Qed.


Corollary H10_entailment_PA : H10p_SAT ⪯ entailment_PA.
Proof.
  exists embed. intros E; split.
  - intros H D I rho HPA. 
Admitted.


Theorem H10_deduction_FA : H10p_SAT ⪯ deduction_FA.
Proof.
  exists embed. intros E. apply H10p_to_FA_prv.
Qed.


Corollary H10_deduction_PA : H10p_SAT ⪯ deduction_PA.
Proof.
Admitted.



Theorem undecidable_entailment_PA :
  undecidable entailment_PA.
Proof.
  refine (undecidability_from_reducibility _ H10_entailment_PA).
  apply H10p_undec.
Qed.


Theorem undecidable_deduction_PA : undecidable deduction_PA.
Proof.
  refine (undecidability_from_reducibility _ H10_deduction_PA).
  apply H10p_undec.
Qed.


