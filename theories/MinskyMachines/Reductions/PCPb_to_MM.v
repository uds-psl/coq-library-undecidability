(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Undecidability.Synthetic 
  Require Import Definitions ReducibilityFacts.

From Undecidability.PCP              Require Import PCP PCPb_iff_iPCPb.
From Undecidability.StackMachines    Require Import BSM iPCPb_to_BSM_HALTING.
From Undecidability.MinskyMachines   Require Import MM MM_sss BSM_MM.
 
Theorem PCPb_MM_HALTS_ON_ZERO : PCPb ⪯ MM_HALTS_ON_ZERO.
Proof.
  eapply reduces_transitive. exact PCPb_iff_iPCPb.reductionLR.
  eapply reduces_transitive. exact iPCPb_to_BSM_HALTING.
  apply BSM_MM_HALTS_ON_ZERO.
Qed.

Theorem PCPb_MM_HALTING : PCPb ⪯ Halt_MM.
Proof.
  eapply reduces_transitive. exact PCPb_iff_iPCPb.reductionLR.
  eapply reduces_transitive. exact iPCPb_to_BSM_HALTING.
  apply BSM_MM_HALTING.
Qed.
