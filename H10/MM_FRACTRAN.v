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

Require Import List Arith Omega.

Require Import ILL.Definitions.

Require Import pos vec.
Require Import sss subcode mm_defs.
Require Import fractran_defs prime_seq mm_fractran.

Set Implicit Arguments.

(** Given a regular FRACTRAN program and a starting state, does it terminate *)

Definition FRACTRAN_REG_PROBLEM := { l : list (nat*nat) & { _ : nat | fractran_regular l } }%type.

Definition FRACTRAN_REG_HALTING (P : FRACTRAN_REG_PROBLEM) : Prop.
Proof.
  destruct P as (l & x & _).
  exact (l /F/ x ↓).
Defined.

(** Given a regular FRACTRAN program and a starting vector [v1,...,vn],
    does the program terminate starting from p1 * q1^v1 * ... qn^vn *)

Definition FRACTRAN_ALT_PROBLEM := { n : nat & 
                                   { l :list (nat*nat) & 
                                   { _ : vec nat n | fractran_regular l } } }%type.

Definition FRACTRAN_ALT_HALTING (P : FRACTRAN_ALT_PROBLEM) : Prop.
Proof.
  destruct P as (n & l & v & _).
  exact (l /F/ ps 1 * exp 1 v ↓).
Defined.

Section MM_HALTING_FRACTRAN_ALT_HALTING.

  Let f : MM_PROBLEM -> FRACTRAN_ALT_PROBLEM.
  Proof.
    intros (n & P & v); red.
    destruct (mm_fractran_n P) as (l & H1 & _).
    exists n, l, v; apply H1.
  Defined.

  Theorem MM_FRACTRAN_ALT_HALTING : MM_HALTING ⪯ FRACTRAN_ALT_HALTING.
  Proof.
    exists f; intros (n & P & v); simpl.
    destruct (mm_fractran_n P) as (l & H1 & H2); simpl; auto.
  Qed.

End MM_HALTING_FRACTRAN_ALT_HALTING.

Section FRACTRAN_ALT_HALTING_REG_HALTING.

  Let f : FRACTRAN_ALT_PROBLEM -> FRACTRAN_REG_PROBLEM.
  Proof.
    intros (n & l & v & H).
    exists l, (ps 1 * exp 1 v); apply H.
  Defined.

  Theorem FRACTRAN_ALT_HALTING_REG_HALTING : FRACTRAN_ALT_HALTING ⪯ FRACTRAN_REG_HALTING.
  Proof. 
    exists f; intros (n & P & v & H); simpl; tauto.
  Qed.

End FRACTRAN_ALT_HALTING_REG_HALTING.

Corollary MM_FRACTRAN_REG_HALTING : MM_HALTING ⪯ FRACTRAN_REG_HALTING.
Proof.
  eapply reduces_transitive. apply MM_FRACTRAN_ALT_HALTING.
  exact FRACTRAN_ALT_HALTING_REG_HALTING.
Qed.

Check MM_FRACTRAN_REG_HALTING.
Print Assumptions MM_FRACTRAN_REG_HALTING.
   