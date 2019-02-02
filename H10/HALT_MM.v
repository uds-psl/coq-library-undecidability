(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import ILL.Definitions.

Require Import utils_tac pos vec mm_defs.

Require Import UNDEC.

From Undecidability.PCP Require Import singleTM TM_SRH SRH_SR SR_MPCP MPCP_PCP.

Set Implicit Arguments.

Corollary MM_HALTING_undec : Halt ⪯ MM_HALTING.
Proof.
  eapply reduces_transitive. exact TM_SRH.Halt_SRH.
  eapply reduces_transitive. exact SRH_SR.reduction.
  eapply reduces_transitive. exact SR_MPCP.reduction.
  eapply reduces_transitive. exact MPCP_PCP.reduction.
  exact PCP_MM_HALTING.
Qed.

