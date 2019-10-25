(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** A Coq computable reduction from n-registers MM termination
    to 2-registers MMA termination. Beware that the semantics
    of MMA is a bit different than the semantics of MM: 

       the DEC instruction jumps when not zero instead of when zero 

    Compare mm_sss  (ILL/Mm/mm_defs.v)
    and     mma_sss (MM/mma_defs.v)                   

    The reduction goes via regular FRACTRAN termination *)

Require Import Undecidability.ILL.Definitions.

From Undecidability.Shared.Libs.DLW Require Import Utils.utils Vec.pos Vec.vec Utils.utils_tac.
From Undecidability.ILL.Code Require Import sss.
From Undecidability.ILL.Mm Require Import mm_defs.
From Undecidability.H10.Fractran Require Import fractran_defs prime_seq mm_fractran.
From Undecidability.MM Require Import mma_defs fractran_mma.

Set Implicit Arguments.

Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity). 
Local Notation "P /MMA/ s ↓" := (sss_terminates (@mma_sss 2) P s) (at level 70, no associativity). 

Theorem mm_mma2 n (P : list (mm_instr (pos n))) : 
               {   Q : list (mm_instr (pos 2)) 
               & { f : vec nat n -> vec nat 2 
                 | forall v, (1,P) /MM/ (1,v) ↓ <-> (1,Q) /MMA/ (1,f v) ↓ } }.
Proof.
  destruct (mm_fractran_not_zero P) as (l & H1 & H2).
  exists (fractran_mma l), (fun v => ps 1 * exp 1 v ## 0 ## vec_nil).
  intros v; rewrite H2.
  apply fractran_mma_reduction; trivial.
Qed.

Section MM_MMA2.

  Let f : MM_PROBLEM -> MMA2_PROBLEM.
  Proof.
    intros (n & P & v).
    destruct (mm_mma2 P) as (Q & f & H).
    exact (Q, f v).
  Defined.

  Theorem MM_MMA2_HALTING : MM_HALTING ⪯ MMA2_HALTING.
  Proof.
    exists f. 
    intros (n & P & v); simpl; unfold MMA2_HALTING.
    destruct (mm_mma2 P) as (Q & g & H); simpl; auto.
  Qed.

End MM_MMA2.

Check MM_MMA2_HALTING.
Print Assumptions MM_MMA2_HALTING.
