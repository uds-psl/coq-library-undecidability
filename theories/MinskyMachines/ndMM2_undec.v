(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.MinskyMachines
  Require Import MMA MMA2_undec ndMM2 MMA2_to_ndMM2_ACCEPT.

(* Undecidability of acceptance for two counters non-deterministic
   Minsky machines with nat indexed instructions *)

Theorem ndMM2_undec : undecidable (@ndMM2_ACCEPT nat).
Proof.
  apply (undecidability_from_reducibility MMA2_HALTS_ON_ZERO_undec).
  apply MMA2_to_ndMM2_ACCEPT.reduction.
Qed.
