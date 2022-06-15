(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Undecidability.Shared.Libs.DLW 
  Require Import godel_coding pos vec sss compiler_correction.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma4_mma2_compiler.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Theorem reduction : @MMA_HALTING 4 ⪯ @MMA_HALTING 2.
Proof.
  apply reduces_dependent; exists.
  intros (P,v).
  exists (gc_code mma4_mma2_compiler (1, P) 1, 0##gc_enc godel_coding_2357 v##vec_nil).
  now apply (compiler_t_term_equiv mma4_mma2_compiler).
Qed.
