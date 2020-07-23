(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega Max.
Require Import Undecidability.Shared.Prelim.
From Undecidability Require Import ILL.Definitions.

From Undecidability.Shared.Libs.DLW Require Import Utils.utils Vec.pos Vec.vec Code.sss.
From Undecidability.MinskyMachines Require Import mm_defs.
From Undecidability.FRACTRAN Require Import fractran_defs mm_fractran prime_seq.
From Undecidability.H10 Require Import MM_FRACTRAN.

Require Import Undecidability.PCP.Util.PCP_facts.


Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity). 

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


Check FRACTRAN_REG_FRACTRAN_HALTING.


