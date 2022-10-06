(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Undecidability.StackMachines Require Import bsm_defs.

From Undecidability.MinskyMachines Require Import MMA.

From Undecidability.MinskyMachines 
  Require BSM_to_MMA_HALTING MMA_to_MMA_zero.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Theorem reduction n : BSMn_HALTING n ⪯ MMA_HALTS_ON_ZERO (1+n).
Proof.
  eapply reduces_transitive. apply BSM_to_MMA_HALTING.reduction.
  apply MMA_to_MMA_zero.reduction.
Qed.




