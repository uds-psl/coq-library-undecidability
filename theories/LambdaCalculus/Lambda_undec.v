(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Undecidability Result(s):
    Weak call-by-name leftmost outermost normalization for closed lambda-terms (wCBNclosed)
    Strong normalization for closed lambda-terms (SNclosed)
*)

From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts.

Require Import Undecidability.LambdaCalculus.Lambda.
From Undecidability.LambdaCalculus.Reductions Require
  HaltLclosed_to_wCBNclosed
  KrivineMclosed_HALT_to_SNclosed.
Require Undecidability.L.Reductions.HaltL_to_HaltLclosed.

Require Import Undecidability.L.L_undec.
Require Import Undecidability.LambdaCalculus.Krivine_undec.

(* Undecidability of weak call-by-name leftmost outermost normalization of closed terms *)
Theorem wCBNclosed_undec : undecidable wCBNclosed.
Proof.
  apply (undecidability_from_reducibility HaltL_undec).
  apply (reduces_transitive HaltL_to_HaltLclosed.reduction).
  exact HaltLclosed_to_wCBNclosed.reduction.
Qed.

Check wCBNclosed_undec.

(* Undecidability of strong normalization wrt. beta-reduction for closed lamda-terms *)
Theorem SNclosed_undec : undecidable SNclosed.
Proof.
  apply (undecidability_from_reducibility KrivineMclosed_HALT_undec).
  exact KrivineMclosed_HALT_to_SNclosed.reduction.
Qed.

Check SNclosed_undec.
