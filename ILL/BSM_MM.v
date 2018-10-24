(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import Definitions.

Require Import utils pos vec. 
Require Import subcode sss. 
Require Import list_bool bsm_defs mm_defs mm_utils mm_comp.

Local Notation "P '/BSM/' s ->> t" := (sss_compute (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s ->> t" := (sss_compute (@mm_sss _) P s t) (at level 70, no associativity).

Section BSM_MM_HALTING.

  Let f : BSM_PROBLEM -> MM_PROBLEM.
  Proof.
    intros (n & i & P & v).
    exists (2+n), (bsm_mm i P).
    exact (0##0##vec_map stack_enc v).
  Defined.

  Theorem BSM_MM_HALTING : BSM_HALTING ⪯ MM_HALTING.
  Proof.
    exists f.
    intros (n & i & P & v); simpl.
    apply bsm_mm_spec.
  Qed.

End BSM_MM_HALTING.

  
