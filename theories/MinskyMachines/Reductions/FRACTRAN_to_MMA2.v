(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* A Coq computable reduction from n-registers MM termination
    to 2-registers MMA termination. Beware that the semantics
    of MMA is a bit different than the semantics of MM: 

       the DEC instruction jumps when not zero instead of when zero 

    Compare mm_sss  (MinskyMachines/mm_defs.v)
    and     mma_sss (MinskyMachines/mma_defs.v)                   

    The reduction goes via regular FRACTRAN termination *)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.Shared.Libs.DLW Require Import pos vec sss.

From Undecidability.FRACTRAN Require Import FRACTRAN.
From Undecidability.MinskyMachines Require Import mma_defs fractran_mma.

Set Implicit Arguments.

Set Default Proof Using "Type".

Local Notation "P //ₐ s ↓" := (sss_terminates (@mma_sss 2) P s) (at level 70, no associativity).

Section FRACTRAN_REG_MMA2_and_ON_ZERO.

  Let f : FRACTRAN_REG_PROBLEM -> MMA2_PROBLEM.
  Proof.
    intros (Q & x & _).
    exact (fractran_reg_mma Q,x##0##vec_nil).
  Defined.

  Theorem FRACTRAN_REG_MMA2_HALTING : FRACTRAN_REG_HALTING ⪯ MMA2_HALTING.
  Proof.
    exists f; intros (? & ? & ?); simpl.
    now apply fractran_reg_mma_reductions.
  Qed.

  Theorem FRACTRAN_REG_MMA2_HALTS_ON_ZERO : FRACTRAN_REG_HALTING ⪯ MMA2_HALTS_ON_ZERO.
  Proof.
    exists f; intros (? & ? & ?); simpl.
    now apply fractran_reg_mma_reductions.
  Qed.

End FRACTRAN_REG_MMA2_and_ON_ZERO.

Check FRACTRAN_REG_MMA2_HALTING.
Check FRACTRAN_REG_MMA2_HALTS_ON_ZERO.
