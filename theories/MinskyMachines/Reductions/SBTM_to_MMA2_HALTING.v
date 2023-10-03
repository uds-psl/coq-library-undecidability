(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

From Undecidability.TM Require Import SBTM.
From Undecidability.MinskyMachines Require Import MMA.

From Undecidability.TM
  Require SBTM_HALT_to_PCTM_HALT.

From Undecidability.StackMachines
  Require PCTM_HALT_to_BSM_HALTING.

From Undecidability.MinskyMachines
  Require MMA BSM_to_MMA_HALTING MMA3_to_MMA2_HALTING.

Theorem reduction : SBTM_HALT ⪯ MMA2_HALTING.
Proof.
  eapply reduces_transitive. apply SBTM_HALT_to_PCTM_HALT.reduction.
  eapply reduces_transitive. apply PCTM_HALT_to_BSM_HALTING.reduction.
  eapply reduces_transitive. apply BSM_to_MMA_HALTING.reduction.
  apply MMA3_to_MMA2_HALTING.reduction.
Qed.

