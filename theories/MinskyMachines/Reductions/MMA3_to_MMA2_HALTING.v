(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.Shared.Libs.DLW 
  Require Import utils_tac pos vec subcode sss compiler_correction.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma3_mma2_compiler.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Local Notation "e #> x" := (vec_pos e x).

Theorem reduction n : @MMA_HALTING (3+n) ⪯ @MMA_HALTING (2+n).
Proof.
  apply reduces_dependent; exists.
  intros (P,v).
  set (w := 0##(combi_235 (v#>pos0) (v#>pos1) (v#>pos2))##vec_tail (vec_tail (vec_tail v))).
  exists (gc_code (mma3_mma2_compiler n) (1, P) 1, w).
  apply (compiler_t_term_equiv (mma3_mma2_compiler _)); simpl.
  msplit 2; auto.
  intro; now rewrite !vec_pos_tail.
Qed.
