Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.PA.
Require Import List.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts.
From Undecidability.H10 Require Import H10 H10_undec.
From Undecidability.H10.Dio Require Import dio_single.


Definition standard {I} (M : interp I) := True.

Theorem H10_entailment_FA :
  (exists I (M : interp I), extensional M /\ standard M /\ forall rho psi, In psi FA -> rho ⊨ psi) -> H10 ⪯ entailment_FA.
Proof.
Admitted.


Theorem H10_entailment_PA :
  (exists I (M : interp I), extensional M /\ standard M /\ forall rho psi, PA psi -> rho ⊨ psi) -> H10 ⪯ entailment_PA.
Proof.
Admitted.


Theorem H10_deduction_FA : H10 ⪯ deduction_FA.
Proof.
Admitted.


Theorem H10_deduction_PA : H10 ⪯ deduction_PA.
Proof.
Admitted.




Theorem undecidable_entailment_PA :
  (exists I (M : interp I), extensional M /\ standard M /\ forall rho psi, PA psi -> rho ⊨ psi) -> undecidable entailment_PA.
Proof.
  intros H. refine (undecidability_from_reducibility _ (H10_entailment_PA H)).
  apply H10_undec.
Qed.



Theorem undecidable_deduction_PA : undecidable deduction_PA.
Proof.
  refine (undecidability_from_reducibility _ H10_deduction_PA).
  apply H10_undec.
Qed.


