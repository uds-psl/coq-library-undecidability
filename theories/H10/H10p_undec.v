From Undecidability.H10 Require Import H10 H10_undec H10p Reductions.H10_to_H10p.
From Undecidability.Synthetic Require Import Undecidability.

Local Set Implicit Arguments.

(* Solvability of Diophantine equations without parameters is undecidable *)

Theorem H10p_undec :
  undecidable H10p.
Proof.
  apply (undecidability_from_reducibility H10_undec). exact Reductions.H10_to_H10p.reduction.
Qed.


