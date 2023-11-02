(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

From Undecidability.Shared.Libs.DLW 
  Require Import pos vec sss compiler_correction.

From Undecidability.TM
  Require Import PCTM.

From Undecidability.StackMachines 
  Require Import bsm_defs bsm_pctm BSM_sss.

Set Implicit Arguments.

Theorem reduction : PCTM_HALT ⪯ BSMn_HALTING 2.
Proof.
  apply reduces_dependent; exists.
  intros (P,((l,b),r)).
  set (Q := gc_code pctm_bsm2_compiler (1,P) 1).
  set (w1 := l##(b::r)##vec_nil).
  exists (existT _ 1 (existT _ Q w1)); simpl.
  apply compiler_t_term_equiv; split; auto.
Qed.
