(*
  Undecidability Result(s):
    Weak call-by-name leftmost outermost normalization of closed terms (wCBNclosed)
    Weak call-by-name leftmost outermost normalization (wCBN)
*)

From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts.

Require Import Undecidability.LambdaCalculus.wCBN.
From Undecidability.LambdaCalculus.Reductions Require
  HaltLclosed_to_wCBNclosed wCBNclosed_to_wCBN.

Require Import Undecidability.L.L_undec.
Require Undecidability.TM.Reductions.L_to_mTM.

(* Undecidability of weak call-by-name leftmost outermost normalization of closed terms *)
Theorem wCBNclosed_undec : undecidable wCBNclosed.
Proof.
  apply (undecidability_from_reducibility HaltL_undec).
  apply (reduces_transitive L_to_mTM.HaltL_HaltLclosed).
  exact HaltLclosed_to_wCBNclosed.reduction.
Qed.

Check wCBNclosed_undec.

(* Undecidability of weak call-by-name leftmost outermost normalization *)
Theorem wCBN_undec : undecidable wCBN.
Proof.
  apply (undecidability_from_reducibility wCBNclosed_undec).
  exact wCBNclosed_to_wCBN.reduction.
Qed.

Check wCBN_undec.
