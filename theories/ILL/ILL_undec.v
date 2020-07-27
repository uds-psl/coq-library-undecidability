(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.PCP                  Require Import PCP PCP_undec.
From Undecidability.BinaryStackMachines  Require Import BSM.
From Undecidability.MinskyMachines       Require Import MM.

From Undecidability.ILL 
  Require Import EILL ILL PCP_iBPCP iBPCP_MM MM_EILL EILL_ILL.

Theorem PCP_chain_EILL : ⎩PCP⎭ ⪯ₗ⎩EILL_PROVABILITY⎭ 
   by ⎩PCPb⎭ :: ⎩iPCPb⎭ :: ⎩BSM_HALTING⎭ 
   :: ⎩MM_HALTS_ON_ZERO⎭ :: ⎩EILL_PROVABILITY⎭ :: nil.
Proof.
  red chain app PCP_chain_iPCPb.
  red chain app iBPCP_chain_MM.
  red chain step MM_HALTS_ON_ZERO_EILL_PROVABILITY.
  red chain stop.
Qed.

(** The reduction chain from the CPP 2019 paper *)

Theorem PCP_chain_ILL : ⎩PCP⎭ ⪯ₗ⎩ILL_PROVABILITY⎭ 
   by ⎩PCPb⎭ :: ⎩iPCPb⎭ :: ⎩BSM_HALTING⎭ 
   :: ⎩MM_HALTS_ON_ZERO⎭ :: ⎩EILL_PROVABILITY⎭ 
   :: ⎩ILL_PROVABILITY⎭ :: nil.
Proof.
  red chain app PCP_chain_EILL.
  red chain step EILL_ILL_PROVABILITY.
  red chain stop.
Qed.

Check PCP_chain_ILL.

(** Undecidability results *)

Theorem EILL_undec : undecidable EILL_PROVABILITY.
Proof.
  apply (undecidability_from_reducibility PCP_undec).
  apply reduction_chain_reduces with (1 := PCP_chain_EILL).
Qed.

Theorem ILL_undec : undecidable ILL_PROVABILITY.
Proof.
  apply (undecidability_from_reducibility PCP_undec).
  apply reduction_chain_reduces with (1 := PCP_chain_ILL).
Qed.

Check ILL_undec.