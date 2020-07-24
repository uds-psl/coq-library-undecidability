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
From Undecidability.MinskyMachines Require Import mm_defs.

(* From Undecidability.ILL Require Import UNDEC. *)

Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.Halting.
Require Import Undecidability.PCP.Reductions.HALT_TM1_to_PCPb.

Set Implicit Arguments.

Lemma BSM_MM_HALT

Corollary MM_HALTING_undec : undecidable MM_HALTING.
Proof.
  apply (undecidability_from_reducibility BSM_undec).
  eapply reduces_transitive. exact Halt_PCP.
  exact PCP_MM_HALTING.
Qed.

