(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** * Main undecidability results and DPRM theorem *)
(** ** HALT reduces to MM *)

From Undecidability Require Import ILL.Definitions.

From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac.
From Undecidability.ILL.Mm Require Import mm_defs.

From Undecidability.ILL Require Import UNDEC.

From Undecidability.SR Require Import Util.singleTM Reductions.TM_to_SRH Reductions.SRH_to_SR.
From Undecidability.PCP Require Import Reductions.SR_to_MPCP Reductions.MPCP_to_PCP.

Set Implicit Arguments.

Corollary Halt_PCP : Halt ⪯ PCP.
Proof.
  eapply reduces_transitive. exact TM_to_SRH.Halt_SRH.
  eapply reduces_transitive. exact SRH_to_SR.reduction.
  eapply reduces_transitive. exact SR_to_MPCP.reduction.
  exact MPCP_to_PCP.reduction.
Qed.

Corollary MM_HALTING_undec : Halt ⪯ MM_HALTING.
Proof.
  eapply reduces_transitive. exact Halt_PCP.
  exact PCP_MM_HALTING.
Qed.

