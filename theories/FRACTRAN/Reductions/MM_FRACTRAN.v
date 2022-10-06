(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Undecidability.Shared.Libs.DLW 
  Require Import pos vec sss.

From Undecidability.MinskyMachines
  Require Import mm_defs.

From Undecidability.FRACTRAN
  Require Import FRACTRAN fractran_utils mm_fractran prime_seq FRACTRAN_sss FRACTRAN_FRACTRAN.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Set Implicit Arguments.

Section MM_HALTING_FRACTRAN_ALT_HALTING.

  Let f : MM_PROBLEM -> FRACTRAN_ALT_PROBLEM.
  Proof.
    intros (n & P & v); red.
    destruct (mm_fractran_n P) as (l & H1 & _).
    split. 
    + exact l. 
    + exists n; exact v.
  Defined.

  Theorem MM_FRACTRAN_ALT_HALTING : Halt_MM ⪯ FRACTRAN_ALT_HALTING.
  Proof.
    exists f; intros (n & P & v).
    setoid_rewrite Halt_MM_iff. simpl.
    destruct (mm_fractran_n P) as (l & H1 & H2); simpl; auto.
  Qed.

End MM_HALTING_FRACTRAN_ALT_HALTING.

Corollary MM_FRACTRAN_HALTING : Halt_MM ⪯ Halt_FRACTRAN.
Proof.
  eapply reduces_transitive. apply MM_FRACTRAN_ALT_HALTING.
  exact FRACTRAN_ALT_HALTING_HALTING.
Qed.

Section MM_HALTING_FRACTRAN_REG_HALTING.

  Let f : MM_PROBLEM -> FRACTRAN_REG_PROBLEM.
  Proof.
    intros (n & P & v); red.
    destruct (mm_fractran_n P) as (l & H1 & _).
    exists l, (ps 1 * exp 1 v); assumption.
  Defined. 
 
  Theorem MM_FRACTRAN_REG_HALTING : Halt_MM ⪯ FRACTRAN_REG_HALTING.
  Proof.
    exists f; intros (n & P & v).
    setoid_rewrite Halt_MM_iff. simpl.
    destruct (mm_fractran_n P) as (l & H1 & H2); simpl; auto.
  Qed.

End MM_HALTING_FRACTRAN_REG_HALTING.

Check MM_FRACTRAN_REG_HALTING.

