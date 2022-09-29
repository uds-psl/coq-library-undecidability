(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Undecidability.Shared.Libs.DLW 
  Require Import pos vec sss.

From Undecidability.MinskyMachines
  Require Import mma_defs.

From Undecidability.FRACTRAN
  Require Import FRACTRAN fractran_utils mma_fractran prime_seq FRACTRAN_sss FRACTRAN_FRACTRAN.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Set Implicit Arguments.

Section MMA_HALTING_FRACTRAN_REG_HALTING.

  Variable n : nat.

  Let f : MMA_PROBLEM n -> FRACTRAN_REG_PROBLEM.
  Proof.
    intros (P & v); red.
    destruct (mma_fractran_n P) as (l & H1 & _).
    exists l, (ps 1 * exp 0 v); assumption.
  Defined. 
 
  Theorem MMA_FRACTRAN_REG_HALTING : MMA_HALTING n ⪯ FRACTRAN_REG_HALTING.
  Proof.
    exists f; intros (P & v); simpl.
    destruct (mma_fractran_n P) as (l & H1 & H2); simpl; auto.
    apply H2.
  Qed.

End MMA_HALTING_FRACTRAN_REG_HALTING.

Corollary MMA_FRACTRAN_HALTING n : MMA_HALTING n ⪯ Halt_FRACTRAN.
Proof.
  eapply reduces_transitive. apply MMA_FRACTRAN_REG_HALTING.
  apply FRACTRAN_REG_FRACTRAN_HALTING.
Qed.

Check MMA_FRACTRAN_HALTING.

