(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** A Coq computable reduction from n-registers MM termination
    to 2-registers MM2 termination. Beware that the semantics
    of MM2 is a bit different than the semantics of MM: 

       the DEC instruction jumps when not zero instead of when zero 

    Compare mm_sss  (ILL/Mm/mm_defs.v)
    and     mm2_sss (./mm2_defs.v)                   *)

Require Import ILL.Definitions.

Require Import utils_tac pos vec.
Require Import sss mm_defs.
Require Import fractran_defs prime_seq mm_fractran. 
Require Import mm2_defs fractran_mm2.

Set Implicit Arguments.

Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity). 
Local Notation "P /MM2/ s ↓" := (sss_terminates (@mm2_sss 2) P s) (at level 70, no associativity). 

Theorem mm_mm2 n (P : list (mm_instr n)) : 
              {   Q : list (mm_instr 2) 
              & { f : vec nat n -> vec nat 2 
                | forall v, (1,P) /MM/ (1,v) ↓ <-> (1,Q) /MM2/ (1,f v) ↓ } }.
Proof.
  destruct (mm_fractran_not_zero P) as (l & H1 & H2).
  exists (fractran_mm2 l), (fun v => ps 1 * exp 1 v ## 0 ## vec_nil).
  intros v; rewrite H2.
  apply fractran_mm2_reduction; trivial.
Qed.

Definition MM2_PROBLEM := (list (mm_instr 2) * vec nat 2)%type.
Definition MM2_HALTING (P : MM2_PROBLEM) := (1,fst P) /MM2/ (1,snd P) ↓.

Section MM_MM2.

  Let f : MM_PROBLEM -> MM2_PROBLEM.
  Proof.
    intros (n & P & v).
    destruct (mm_mm2 P) as (Q & f & H).
    exact (Q, f v).
  Defined.

  Theorem MM_MM2_HALTING : MM_HALTING ⪯ MM2_HALTING.
  Proof.
    exists f. 
    intros (n & P & v); simpl; unfold MM2_HALTING.
    destruct (mm_mm2 P) as (Q & g & H); simpl; auto.
  Qed.

End MM_MM2.

Check MM_MM2_HALTING.
Print Assumptions MM_MM2_HALTING.
