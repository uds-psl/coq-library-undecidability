(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.PCP
  Require Import PCP PCP_undec.

From Undecidability.StackMachines 
  Require Import BSM iPCPb_to_BSM_HALTING.

Theorem BSM_undec : undecidable (BSM_HALTING).
Proof.
  apply (undecidability_from_reducibility iPCPb_undec).
  apply iPCPb_to_BSM_HALTING.
Qed.
