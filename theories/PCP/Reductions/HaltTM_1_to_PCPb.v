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

(* Direct reductions from Halting of 1-TM to binary PCP *)

Require Import List.

From Undecidability.Shared.Libs.DLW
  Require Import utils.

Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.

From Undecidability.StringRewriting
  Require Import SR.

From Undecidability.PCP
  Require Import PCP.

From Undecidability.TM
  Require Import SBTM2.

From Undecidability.TM.Reductions
  Require HaltTM_1_to_SBTM2_HALT.

From Undecidability.StringRewriting.Reductions
  Require SBTM2_HALT_to_SR.

From Undecidability.PCP.Reductions
  Require SR_to_MPCP MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb.

Import ReductionChainNotations UndecidabilityNotations.

Lemma HaltTM_1_chain_iPCPb : 
  ⎩ HaltTM 1 ⪯ₘ SBTM2_HALT ⪯ₘ SR ⪯ₘ MPCP ⪯ₘ PCP ⪯ₘ PCPb ⪯ₘ iPCPb ⎭.
Proof.
  msplit 5.
  + apply HaltTM_1_to_SBTM2_HALT.reduction.
  + apply SBTM2_HALT_to_SR.reduction.
  + apply SR_to_MPCP.reduction.
  + apply MPCP_to_PCP.reduction.
  + apply PCP_to_PCPb.reduction.
  + apply PCPb_iff_iPCPb.reductionLR.
Qed.

Lemma HaltTM_1_to_PCP : HaltTM 1 ⪯ PCP.      Proof. reduce with chain HaltTM_1_chain_iPCPb. Qed.
Lemma HaltTM_1_to_PCPb : HaltTM 1 ⪯ PCPb.    Proof. reduce with chain HaltTM_1_chain_iPCPb. Qed.
Lemma HaltTM_1_to_iPCPb : HaltTM 1 ⪯ iPCPb.  Proof. reduce with chain HaltTM_1_chain_iPCPb. Qed.

Lemma PCP_chain_iPCPb : ⎩PCP ⪯ₘ PCPb ⪯ₘ iPCPb⎭.  Proof. split; apply HaltTM_1_chain_iPCPb. Qed.
Lemma PCP_chain_PCPb : ⎩PCP ⪯ₘ PCPb⎭.            Proof. apply PCP_chain_iPCPb. Qed.
Lemma PCPb_chain_iPCPb : ⎩PCPb ⪯ₘiPCPb⎭.         Proof. apply PCP_chain_iPCPb. Qed.
