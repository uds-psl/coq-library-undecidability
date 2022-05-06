From Undecidability.Synthetic Require Import Definitions Undecidability.
Require Import Undecidability.FOL.PA.
From Undecidability.H10 Require Import H10p_undec.
From Undecidability.FOL.Reductions Require Import H10p_to_FA.
From Undecidability.FOL.Util Require Import Friedman.
Require Import List Lia.

Theorem undecidable_ext_entailment_PA :
  undecidable ext_entailment_PA.
Proof.
  refine (undecidability_from_reducibility _ H10_to_ext_entailment_PA).
  apply H10p_undec.
Qed.

Theorem undecidable_entailment_PA :
  undecidable entailment_PA.
Proof.
  refine (undecidability_from_reducibility _ H10_to_entailment_PA).
  apply H10p_undec.
Qed.

Theorem undecidable_deduction_PA :
  undecidable deduction_PA.
Proof.
  refine (undecidability_from_reducibility _ H10_to_deduction_PA).
  apply H10p_undec.
Qed.

Theorem undecidable_classical_deduction_FA :
  undecidable cdeduction_FA.
Proof.
  refine (undecidability_from_reducibility _ _); try apply H10p_undec.
  eapply ReducibilityFacts.reduces_transitive.
  - exists embed. apply H10p_to_class_Q.
  - exists (fun phi => phi). intros phi. split; intros H.
    + destruct H as [A [HA HA']]. now apply (FullDeduction_facts.Weak HA').
    + exists FAeq. auto.
Qed.

Theorem undecidable_classical_deduction_PA :
  undecidable cdeduction_PA.
Proof.
  refine (undecidability_from_reducibility _ _); try apply H10p_undec.
  exists embed. apply reduction_theorem.
  - intros phi H. constructor. apply H.
  - apply Fr_pres_PA.
Qed.


