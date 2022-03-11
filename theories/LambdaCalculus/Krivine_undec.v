(*
  Undecidability Result(s):
    Krivine machine halting for closed terms (KrivineMclosed_HALT_undec)
    Krivine machine halting (KrivineM_HALT)
*)

From Undecidability.Synthetic Require Import Undecidability.

Require Import Undecidability.LambdaCalculus.Krivine.
From Undecidability.LambdaCalculus.Reductions Require
  wCBNclosed_to_KrivineMclosed_HALT.

Require Import Undecidability.LambdaCalculus.wCBN_undec.

(* Undecidability of Krivine machine halting for closed terms *)
Theorem KrivineMclosed_HALT_undec : undecidable KrivineMclosed_HALT.
Proof.
  apply (undecidability_from_reducibility wCBNclosed_undec).
  exact wCBNclosed_to_KrivineMclosed_HALT.reduction.
Qed.

Check KrivineMclosed_HALT_undec.

(* Undecidability of Krivine machine halting *)
Theorem KrivineM_HALT_undec : undecidable KrivineM_HALT.
Proof.
  apply (undecidability_from_reducibility KrivineMclosed_HALT_undec).
  exists (@proj1_sig L.term _). now intros [??].
Qed.

Check KrivineM_HALT_undec.
