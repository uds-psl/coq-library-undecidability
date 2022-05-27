From Undecidability Require Import
  Synthetic.Undecidability Synthetic.ReducibilityFacts
  LambdaCalculus.Krivine_undec TM.UTM.

From Undecidability Require TM.Reductions.KrivineMclosed_HALT_to_HaltUTM.

(** ** HaltUTM is undecidable *)

Lemma HaltUTM_undec :
  undecidable HaltUTM.
Proof.
  apply (undecidability_from_reducibility KrivineMclosed_HALT_undec).
  exact KrivineMclosed_HALT_to_HaltUTM.reduction.
Qed.
