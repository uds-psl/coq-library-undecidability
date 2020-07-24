(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Direct reductions from Halting of 1-TM to binary PCP *)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.TM.Halting.

From Undecidability.StringRewriting.Reductions
  Require Import TM_to_SRH SRH_to_SR.

From Undecidability.PCP
  Require Import PCP.

From Undecidability.PCP.Reductions
  Require Import SR_to_MPCP MPCP_to_PCP PCP_to_PCPb.

Lemma HALT_TM1_to_PCP : HaltTM 1 ⪯ PCP.
Proof.
  eapply reduces_transitive. exact singleTM.TM_conv.
  eapply reduces_transitive. exact Halt_SRH.
  eapply reduces_transitive. exact SRH_to_SR.reduction.
  eapply reduces_transitive. exact SR_to_MPCP.reduction.
  exact MPCP_to_PCP.reduction.
Qed.

Lemma HALT_TM1_to_PCPb : HaltTM 1 ⪯ PCPb.
Proof.
  eapply reduces_transitive. exact HALT_TM1_to_PCP.
  exact PCP_to_PCPb.reduction.
Qed.
