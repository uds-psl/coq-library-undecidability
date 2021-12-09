Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.SOL.SOL.
From Undecidability.SOL.Reductions Require Import H10p_to_SOL.
From Undecidability.H10 Require Import H10p_undec.

Lemma undecidable_SOL_valid : undecidable SOL_valid.
Proof.
   apply (undecidability_from_reducibility H10p_undec).
   apply H10p_to_SOL_valid.
Qed.

Lemma undecidable_SOL_satis: undecidable SOL_satis.
Proof.
   apply (undecidability_from_reducibility H10p_undec).
   apply H10p_to_SOL_satis.
Qed.
