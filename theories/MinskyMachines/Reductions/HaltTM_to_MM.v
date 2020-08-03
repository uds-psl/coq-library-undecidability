(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.TM.TM.
From Undecidability.PCP                  Require Import PCP HALT_TM1_to_PCPb.
From Undecidability.MinskyMachines       Require Import MM PCPb_to_MM.
 
Theorem HaltTM_to_MM_HALTS_ON_ZERO : HaltTM 1 ⪯ MM_HALTS_ON_ZERO.
Proof.
  eapply reduces_transitive. exact HALT_TM1_to_PCPb.
  apply PCPb_MM_HALTS_ON_ZERO.
Qed.

Theorem HaltTM_to_MM_HALTING : HaltTM 1 ⪯ MM_HALTING.
Proof.
  eapply reduces_transitive. exact HALT_TM1_to_PCPb.
  apply PCPb_MM_HALTING.
Qed.
