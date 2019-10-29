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
From Undecidability.H10 Require Import MM_FRACTRAN.
From Undecidability.MM Require Import mma_defs fractran_mma.

Set Implicit Arguments.

Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity). 
Local Notation "P /MMA/ s ↓" := (sss_terminates (@mma_sss 2) P s) (at level 70, no associativity). 

Theorem mm_fractran_reg n (P : list (mm_instr (pos n))) : 
        { l : list (nat*nat) & { f |  Forall (fun c => snd c <> 0) l
                                   /\ forall v, (1,P) /MM/ (1,v) ↓ <-> l /F/ f v ↓ } }.
Proof.
  destruct (mm_fractran_not_zero P) as (l & H1 & H2).
  exists l, (fun v => ps 1 * exp 1 v); split; auto.
  revert H1; apply Forall_impl; tauto.
Qed.

Section MM_FRACTRAN_REG.

  Let f : MM_PROBLEM -> FRACTRAN_REG_PROBLEM.
  Proof.
    intros (n & P & v).
    destruct (mm_fractran_reg P) as (l & f & H1 & H2).
    exists l, (f v); assumption.
  Defined.

  Theorem MM_FRACTRAN_REG_HALTING : MM_HALTING ⪯ FRACTRAN_REG_HALTING.
  Proof.
    exists f. 
    intros (n & P & v); simpl.
    destruct (mm_fractran_reg P) as (l & g & H1 & H2); simpl; auto.
  Qed.

End MM_FRACTRAN_REG.

Check MM_FRACTRAN_REG_HALTING.
Print Assumptions MM_FRACTRAN_REG_HALTING.

Theorem fractran_reg_mma2 l : 
          Forall (fun c => snd c <> 0) l
       ->   { Q : list (mm_instr (pos 2)) 
            | forall x, l /F/ x ↓ <-> (1,Q) /MMA/ (1,x##0##vec_nil) ↓ }.
Proof.
  intros Hl.
  exists (fractran_reg_mma l).
  apply fractran_reg_mma_reduction; auto.
Qed.

Section FRACTRAN_REG_MMA2.

  Let f : FRACTRAN_REG_PROBLEM -> MMA2_PROBLEM.
  Proof.
    intros (l & x & Hl).
    destruct (fractran_reg_mma2 Hl) as (Q & HQ).
    exact (Q, (x##0##vec_nil)).
  Defined.

  Theorem FRACTRAN_REG_MMA2_HALTING : FRACTRAN_REG_HALTING ⪯ MMA2_HALTING.
  Proof.
    exists f. 
    intros (l & x & Hl); simpl.
    destruct (fractran_reg_mma2 Hl) as (Q & HQ); apply HQ.
  Qed.

End FRACTRAN_REG_MMA2.

Check FRACTRAN_REG_MMA2_HALTING.
Print Assumptions FRACTRAN_REG_MMA2_HALTING.

Corollary MM_MMA2_HALTING : MM_HALTING ⪯ MMA2_HALTING.
Proof.
  eapply reduces_transitive. exact MM_FRACTRAN_REG_HALTING.
  exact FRACTRAN_REG_MMA2_HALTING.
Qed.

Check MM_MMA2_HALTING.
Print Assumptions MM_MMA2_HALTING.

(** This is somewhat for direct proof that does not involve
    testing for (0,_) in the intermediate Fractran program *)

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
