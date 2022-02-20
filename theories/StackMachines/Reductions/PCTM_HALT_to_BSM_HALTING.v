(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Synthetic
  Require Import Undecidability ReducibilityFacts.

From Undecidability.Shared.Libs.DLW 
  Require Import pos vec sss compiler_correction.

From Undecidability.TM
  Require Import PCTM.

From Undecidability.StackMachines.BSM 
  Require Import bsm_defs bsm_pctm.

Set Implicit Arguments.

Set Default Proof Using "Type".

Theorem PCTM_BSM_reduction : PCTM_HALT ⪯ BSM_HALTING.
Proof.
  apply reduces_dependent; exists.
  intros (P,((l,b),r)).
  set (Q := gc_code pctm_bsm2_compiler (1,P) 1).
  set (w1 := l##(b::r)##vec_nil).
  exists (existT _ 2 (existT _ 1 (existT _ Q w1))); simpl.
  apply compiler_t_term_equiv; split; auto.
Qed.

Check PCTM_BSM_reduction.