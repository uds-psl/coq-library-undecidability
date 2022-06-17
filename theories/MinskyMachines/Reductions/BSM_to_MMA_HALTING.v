(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec sss compiler_correction.

From Undecidability.StackMachines
  Require Import bsm_defs.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils_bsm bsm_mma.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Theorem reduction n : BSMn_HALTING n ⪯ MMA_HALTING (1+n).
Proof.
  apply reduces_dependent; exists.
  intros (i,(P,v)).
  exists (gc_code (bsm_mma_compiler _) (i, P) 1, 0##vec_map stack_enc v).
  apply (compiler_t_term_equiv (bsm_mma_compiler n) (i,P) 1); simpl; split; auto.
  intros; rew vec.
Qed.

