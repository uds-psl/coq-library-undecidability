(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Undecidability Result(s):
    Krivine machine halting for closed terms (KrivineMclosed_HALT_undec)
    Krivine machine halting (KrivineM_HALT)
*)

From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts.

Require Import Undecidability.LambdaCalculus.Krivine.
From Undecidability.LambdaCalculus.Reductions Require
  wCBNclosed_to_KrivineMclosed_HALT
  HaltLclosed_to_wCBNclosed.
Require Undecidability.L.Reductions.HaltL_to_HaltLclosed.

Require Import Undecidability.L.L_undec.

(* Undecidability of Krivine machine halting for closed terms *)
Theorem KrivineMclosed_HALT_undec : undecidable KrivineMclosed_HALT.
Proof.
  apply (undecidability_from_reducibility HaltL_undec).
  apply (reduces_transitive HaltL_to_HaltLclosed.reduction).
  apply (reduces_transitive HaltLclosed_to_wCBNclosed.reduction).
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
