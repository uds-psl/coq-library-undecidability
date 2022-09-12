(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.MinskyMachines 
  Require Import MMA MM2 MMA2_undec MMA2_to_MM2.

(* ** MM2_HALTING is undecidable *)

Lemma MM2_HALTING_undec : undecidable MM2_HALTING.
Proof.
  apply (undecidability_from_reducibility MMA2_HALTING_undec).
  apply MMA2_MM2_HALTING.
Qed.

Check MM2_HALTING_undec.

Lemma MM2_HALTS_ON_ZERO_undec : undecidable MM2_HALTS_ON_ZERO.
Proof.
  apply (undecidability_from_reducibility MMA2_HALTS_ON_ZERO_undec).
  apply MMA2_MM2_HALTS_ON_ZERO.
Qed.

Check MM2_HALTS_ON_ZERO_undec.
