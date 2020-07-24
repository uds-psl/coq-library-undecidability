(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import Utils.list_bool Vec.pos Vec.vec Code.sss.

From Undecidability.BinaryStackMachines 
  Require Import BSM Reductions.iBPCP_BSM.

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.PCP
  Require Import PCP PCP_undec.

Theorem BSM_undec : undecidable (BSM_HALTING).
Proof.
  apply (undecidability_from_reducibility iPCPb_undec).
  apply iBPCP_BSM_HALTING.
Qed.
