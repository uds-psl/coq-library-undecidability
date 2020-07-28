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

From Undecidability.Shared.Libs.DLW
  Require Import utils.

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.PCP                  Require Import PCP PCP_undec.
From Undecidability.BinaryStackMachines  Require Import BSM.
From Undecidability.MinskyMachines       Require Import MM.

From Undecidability.ILL 
  Require Import EILL ILL PCP_iBPCP iBPCP_MM MM_EILL EILL_ILL.

Theorem PCP_chain_EILL : 
  ⎩PCP ⪯ₘ PCPb ⪯ₘ iPCPb ⪯ₘ BSM_HALTING ⪯ₘ MM_HALTS_ON_ZERO ⪯ₘ EILL_PROVABILITY ⎭.
Proof.
  msplit 4; ( apply PCP_chain_iPCPb || apply iBPCP_chain_MM || idtac).
  apply MM_HALTS_ON_ZERO_EILL_PROVABILITY.
Qed.

(** The reduction chain from the CPP 2019 paper *)

Theorem PCP_chain_ILL : 
  ⎩PCP ⪯ₘ PCPb ⪯ₘ iPCPb ⪯ₘ BSM_HALTING ⪯ₘ MM_HALTS_ON_ZERO ⪯ₘ EILL_PROVABILITY ⪯ₘ ILL_PROVABILITY ⎭.
Proof.
  msplit 5; try apply PCP_chain_EILL.
  apply EILL_ILL_PROVABILITY.
Qed.

Check PCP_chain_ILL.

(** Undecidability results *)

Theorem EILL_undec : undecidable EILL_PROVABILITY.
Proof.
  apply (undecidability_from_reducibility PCP_undec).
  reduce with chain PCP_chain_EILL.
Qed.

Theorem ILL_undec : undecidable ILL_PROVABILITY.
Proof.
  apply (undecidability_from_reducibility PCP_undec).
  reduce with chain PCP_chain_ILL.
Qed.

Check ILL_undec.