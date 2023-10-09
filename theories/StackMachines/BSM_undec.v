(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.PCP
  Require Import PCP PCP_undec.

From Undecidability.StackMachines 
  Require Import BSM iPCPb_to_BSM_HALTING BSM_sss.

(** ** BSM_HALTING is undecidable *)

Theorem BSM_undec : undecidable Halt_BSM.
Proof.
  apply (undecidability_from_reducibility iPCPb_undec).
  apply iPCPb_to_BSM_HALTING.
Qed.
