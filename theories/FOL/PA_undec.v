Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.PA.
From Undecidability.FOL.Util Require Import FullTarski.
From Undecidability.H10 Require Import H10p H10p_undec.
From Undecidability.FOL.Reductions Require Import H10p_to_FA.


(* ** Reduction for the axiomatisation PA assuming extensionality of models. *)


Theorem H10_ext_entailment_PA :
  H10p_SAT ⪯ ext_entailment_PA.
Proof.
  exists embed. intros E. apply H10p_to_FA_ext_sat.
Qed.


Theorem undecidable_ext_entailment_PA :
  undecidable ext_entailment_PA.
Proof.
  refine (undecidability_from_reducibility _ H10_ext_entailment_PA).
  apply H10p_undec.
Qed.



(* ** Reductions for the axiomatisations PAeq and FAeq, which include the axioms for equatlity. *)

Theorem H10_entailment_FA : H10p_SAT ⪯ entailment_FA.
Proof.
  exists embed; intros E. apply H10p_to_FA_sat.
Qed.


Corollary H10_entailment_PA : H10p_SAT ⪯ entailment_PA.
Proof.
  exists embed; intros E. apply H10p_to_PA_sat.
Qed.


Theorem H10_deduction_FA : H10p_SAT ⪯ deduction_FA.
Proof.
  exists embed; intros E. apply H10p_to_FA_prv.
Qed.


Corollary H10_deduction_PA : H10p_SAT ⪯ deduction_PA.
Proof.
  exists embed; intros E. apply H10p_to_PA_prv.
Qed.



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


