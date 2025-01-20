(*
  Author(s):
    Andrej Dudenhefner (TU Dortmund University, Germany)

  Undecidability Result(s):
    Higher-Order Matching wrt. beta-equivalence (HOMbeta_undec)
*)

From Undecidability.Synthetic Require Import Undecidability.

Require Import Undecidability.LambdaCalculus.HOMatching.
Require Undecidability.LambdaCalculus.Reductions.SSTS01_to_HOMbeta.
Require Import Undecidability.StringRewriting.SSTS_undec.

(* Undecidability of Higher-Order Matching wrt. beta-equivalence *)
Theorem HOMbeta_undec : undecidable HOMbeta.
Proof.
  apply (undecidability_from_reducibility SSTS01_undec).
  exact SSTS01_to_HOMbeta.reduction.
Qed.

Check HOMbeta_undec.
