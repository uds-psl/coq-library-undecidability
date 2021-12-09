Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.SOL.PA2.
From Undecidability.SOL.Reductions Require Import H10p_to_SOL.
From Undecidability.H10 Require Import H10p_undec.

Lemma undecidable_PA2_valid : undecidable PA2_valid.
Proof.
   apply (undecidability_from_reducibility H10p_undec).
   exists encode_problem. intros e. apply H10p_to_PA2_validity.
Qed.

Lemma undecidable_PA2_satis: undecidable PA2_satis.
Proof.
   apply (undecidability_from_reducibility H10p_undec).
   exists encode_problem. intros e. apply H10p_to_PA2_satisfiability.
Qed.
