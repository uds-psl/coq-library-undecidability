(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.MinskyMachines
  Require Import MM2 mm2_from_zero.

From Undecidability.Shared.Libs.DLW 
  Require Import utils.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Set Implicit Arguments.

Theorem reduction : MM2_HALTING ⪯ MM2_HALTS_STARTING_ZERO.
Proof.
  apply reduces_dependent; exists.
  intros ((P,a),b).
  apply mm2_mm2_0_simulator.
Qed.
