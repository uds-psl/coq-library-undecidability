(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Direct reductions from Halting of 1-TM to binary PCP *)

From Stdlib Require Import List.

From Undecidability.Shared.Libs.DLW
  Require Import utils.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.

From Undecidability.StringRewriting
  Require Import SR.

From Undecidability.PCP
  Require Import PCP.

From Undecidability.TM
  Require Import SBTM.

From Undecidability.TM.Reductions
  Require HaltTM_1_to_SBTM_HALT.

From Undecidability.StringRewriting.Reductions
  Require SBTM_HALT_to_SR.

From Undecidability.PCP.Reductions
  Require SR_to_MPCP MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb.

Import ReductionChainNotations.

Lemma HaltTM_1_chain_iPCPb : 
  HaltTM 1 ⪯ SBTM_HALT /\
  SBTM_HALT ⪯ SR /\
  SR ⪯ MPCP /\
  MPCP ⪯ PCP /\
  PCP ⪯ PCPb /\
  PCPb ⪯ iPCPb.
Proof.
  repeat eapply conj.
  + apply HaltTM_1_to_SBTM_HALT.reduction.
  + apply SBTM_HALT_to_SR.reduction.
  + apply SR_to_MPCP.reduction.
  + apply MPCP_to_PCP.reduction.
  + apply PCP_to_PCPb.reduction.
  + apply PCPb_iff_iPCPb.reductionLR.
Qed.

Lemma HaltTM_1_to_PCP : HaltTM 1 ⪯ PCP.      
Proof.
  repeat (eapply reduces_transitive; [eapply HaltTM_1_chain_iPCPb | try now eapply reduces_reflexive]).
Qed.

Lemma HaltTM_1_to_PCPb : HaltTM 1 ⪯ PCPb.
Proof.
  repeat (eapply reduces_transitive; [eapply HaltTM_1_chain_iPCPb | try now eapply reduces_reflexive]).
Qed.  

Lemma HaltTM_1_to_iPCPb : HaltTM 1 ⪯ iPCPb.
Proof.
  repeat (eapply reduces_transitive; [eapply HaltTM_1_chain_iPCPb | try now eapply reduces_reflexive]).
Qed.
