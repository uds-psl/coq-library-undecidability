(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Import ListNotations.

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.PCP
  Require Import PCP.

From Undecidability.BinaryStackMachines
  Require Import BSM iPCPb_to_BSM_HALTING.

From Undecidability.MinskyMachines
  Require Import MM BSM_MM.

Lemma iBPCP_chain_MM : ⎩iPCPb⎭ ⪯ₗ ⎩MM_HALTS_ON_ZERO⎭ by [⎩BSM_HALTING⎭;
                                                          ⎩MM_HALTS_ON_ZERO⎭].
Proof.
  red chain step iPCPb_to_BSM_HALTING.
  red chain step BSM_MM_HALTS_ON_ZERO.
  red chain stop.
Qed.

Lemma iBPCP_to_MM : iPCPb ⪯ MM_HALTS_ON_ZERO.
Proof.
  apply reduction_chain_reduces with (1 := iBPCP_chain_MM).
Qed.
