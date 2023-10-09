(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* * Main undecidability results for Minsky machines *)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.StackMachines Require Import BSM BSM_undec.
From Undecidability.MinskyMachines Require Import MM MM_sss Reductions.BSM_MM.

Lemma MM_HALTS_ON_ZERO_undec : undecidable MM_HALTS_ON_ZERO.
Proof.
  apply (undecidability_from_reducibility BSM_undec).
  apply BSM_MM_HALTS_ON_ZERO.
Qed.

Lemma MM_HALTING_undec : undecidable Halt_MM.
Proof.
  apply (undecidability_from_reducibility BSM_undec).
  apply BSM_MM_HALTING.
Qed.