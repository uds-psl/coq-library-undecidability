(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Undecidability.Synthetic.Definitions.

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec subcode sss.

From Undecidability.StackMachines
  Require Import bsm_defs.

From Undecidability.MinskyMachines.MM
  Require Import mm_defs mm_utils mm_comp. 

Local Notation "P '/BSM/' s ↓" := (sss_terminates (@bsm_sss _) P s) (at level 70, no associativity).
Local Notation "P '/MM/' s ~~> t" := (sss_output (@mm_sss _) P s t) (at level 70, no associativity).

Section BSM_MM_HALTS_ON_ZERO.

  Let f : BSM_PROBLEM -> MM_PROBLEM.
  Proof.
    intros (n & i & P & v).
    destruct (bsm_mm_compiler_2 i P) as (Q & _).
    exists (2+n), Q.
    exact (bsm_state_enc v).
  Defined.

  Theorem BSM_MM_HALTS_ON_ZERO : Halt_BSM ⪯ MM_HALTS_ON_ZERO.
  Proof.
    exists f. red.
    setoid_rewrite Halt_BSM_iff.
    intros (n & i & P & v); simpl.
    destruct (bsm_mm_compiler_2 i P) as (Q & H); simpl; auto.
  Qed.

End BSM_MM_HALTS_ON_ZERO.

Section BSM_MM_HALTING.

  Let f : BSM_PROBLEM -> MM_PROBLEM.
  Proof.
    intros (n & i & P & v).
    destruct (bsm_mm_compiler_1 i P) as (Q & _).
    exists (2+n), Q.
    exact (bsm_state_enc v).
  Defined.

  Theorem BSM_MM_HALTING : Halt_BSM ⪯ Halt_MM.
  Proof.
    exists f. red.
    setoid_rewrite Halt_BSM_iff.
    setoid_rewrite Halt_MM_iff.
    intros (n & i & P & v); simpl.
    destruct (bsm_mm_compiler_1 i P) as (Q & H); simpl; auto.
  Qed.

End BSM_MM_HALTING.
