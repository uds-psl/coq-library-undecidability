(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** HALT reduces to Binary PCP *)

From Undecidability.ILL Require Import Definitions PCP_BPCP.

From Undecidability.Problems Require Import TM.

From Undecidability.PCP Require Import singleTM TM_SRH SRH_SR SR_MPCP MPCP_PCP.

Set Implicit Arguments.

Corollary HaltTM_BPCP : HaltTM 1 ⪯ BPCP.
Proof.
  eapply reduces_transitive. exact singleTM.TM_conv.
  eapply reduces_transitive. exact TM_SRH.Halt_SRH.
  eapply reduces_transitive. exact SRH_SR.reduction.
  eapply reduces_transitive. exact SR_MPCP.reduction.
  eapply reduces_transitive. exact MPCP_PCP.reduction.
  exact PCP_BPCP.
Qed.
