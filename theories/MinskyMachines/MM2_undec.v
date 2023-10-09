(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.MinskyMachines
  Require Import MMA MM2 MMA2_undec MMA2_to_MM2.

From Undecidability.MinskyMachines.Reductions
  Require MM2_HALTING_to_MM2_ZERO_HALTING.

(** ** MM2_HALTING is undecidable *)

Lemma MM2_HALTING_undec : undecidable MM2_HALTING.
Proof.
  apply (undecidability_from_reducibility MMA2_HALTING_undec).
  apply MMA2_MM2_HALTING.
Qed.

Check MM2_HALTING_undec.

Lemma MM2_ZERO_HALTING_undec : undecidable MM2_ZERO_HALTING.
Proof.
  apply (undecidability_from_reducibility MM2_HALTING_undec).
  exact MM2_HALTING_to_MM2_ZERO_HALTING.reduction.
Qed.

Check MM2_ZERO_HALTING_undec.

Lemma MM2_HALTS_ON_ZERO_undec : undecidable MM2_HALTS_ON_ZERO.
Proof.
  apply (undecidability_from_reducibility MMA2_HALTS_ON_ZERO_undec).
  apply MMA2_MM2_HALTS_ON_ZERO.
Qed.

Check MM2_HALTS_ON_ZERO_undec.
