(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Relations Lia.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

From Undecidability.Shared.Libs.DLW Require Import utils pos vec sss subcode.
From Undecidability.MinskyMachines Require Import mma_defs mma_simul.

Set Implicit Arguments.

Theorem reduction n : MMA_HALTING (1+n) ⪯ MMA_HALTS_ON_ZERO (1+n).
Proof.
  apply reduces_dependent; exists.
  intros (P,v).
  destruct mma2_simulator with n 1 P as (Q & HQ).
  exists (Q,v); apply HQ.
Qed. 
