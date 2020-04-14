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

(** ** MM reduces to FRACTRAN *)

Require Import List Arith Omega.

From Undecidability Require Import ILL.Definitions.

From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.ILL.Code Require Import sss subcode.
From Undecidability.ILL.Mm   Require Import mm_defs.
From Undecidability.H10.Fractran Require Import fractran_defs mm_fractran prime_seq.

Set Implicit Arguments.

(** Given a FRACTRAN program and a starting state, does it terminate *)

Definition FRACTRAN_PROBLEM := (list (nat*nat) * nat)%type.
Definition FRACTRAN_REG_PROBLEM := 
  { l : list (nat*nat) & { _ : nat | Forall (fun c => snd c <> 0) l } }.

Definition FRACTRAN_HALTING (P : FRACTRAN_PROBLEM) : Prop.
Proof.
  destruct P as (l & x).
  exact (l /F/ x ↓).
Defined.

Definition FRACTRAN_REG_HALTING (P : FRACTRAN_REG_PROBLEM) : Prop.
Proof.
  destruct P as (l & x & _).
  exact (l /F/ x ↓).
Defined.

(** Given a FRACTRAN program and a starting vector [v1,...,vn],
    does the program terminate starting from p1 * q1^v1 * ... qn^vn *)

Definition FRACTRAN_ALT_PROBLEM := (list (nat*nat) * { n : nat & vec nat n })%type.

Definition FRACTRAN_ALT_HALTING : FRACTRAN_ALT_PROBLEM -> Prop.
Proof.
  intros (l & n & v).
  exact (l /F/ ps 1 * exp 1 v ↓).
Defined.

Section MM_HALTING_FRACTRAN_ALT_HALTING.

  Let f : MM_PROBLEM -> FRACTRAN_ALT_PROBLEM.
  Proof.
    intros (n & P & v); red.
    destruct (mm_fractran_n P) as (l & H1 & _).
    split. 
    + exact l. 
    + exists n; exact v.
  Defined.

  Theorem MM_FRACTRAN_ALT_HALTING : MM_HALTING ⪯ FRACTRAN_ALT_HALTING.
  Proof.
    exists f; intros (n & P & v); simpl.
    destruct (mm_fractran_n P) as (l & H1 & H2); simpl; auto.
  Qed.

End MM_HALTING_FRACTRAN_ALT_HALTING.

Section FRACTRAN_ALT_HALTING_HALTING.

  Let f : FRACTRAN_ALT_PROBLEM -> FRACTRAN_PROBLEM.
  Proof.
    intros (l & n & v).
    exact (l,(ps 1 * exp 1 v)).
  Defined.

  Theorem FRACTRAN_ALT_HALTING_HALTING : FRACTRAN_ALT_HALTING ⪯ FRACTRAN_HALTING.
  Proof. 
    exists f; intros (n & P & v); simpl; tauto.
  Qed.

End FRACTRAN_ALT_HALTING_HALTING.

Corollary MM_FRACTRAN_HALTING : MM_HALTING ⪯ FRACTRAN_HALTING.
Proof.
  eapply reduces_transitive. apply MM_FRACTRAN_ALT_HALTING.
  exact FRACTRAN_ALT_HALTING_HALTING.
Qed.

Check MM_FRACTRAN_HALTING.


Section MM_HALTING_FRACTRAN_REG_HALTING.

  Let f : MM_PROBLEM -> FRACTRAN_REG_PROBLEM.
  Proof.
    intros (n & P & v); red.
    destruct (mm_fractran_n P) as (l & H1 & _).
    exists l, (ps 1 * exp 1 v); assumption.
  Defined. 
 
  Theorem MM_FRACTRAN_REG_HALTING : MM_HALTING ⪯ FRACTRAN_REG_HALTING.
  Proof.
    exists f; intros (n & P & v); simpl.
    destruct (mm_fractran_n P) as (l & H1 & H2); simpl; auto.
  Qed.

End MM_HALTING_FRACTRAN_REG_HALTING.

Check MM_FRACTRAN_REG_HALTING.


Section FRACTRAN_REG_FRACTRAN_HALTING.

  Let f : FRACTRAN_REG_PROBLEM -> FRACTRAN_PROBLEM.
  Proof.
    intros (l & v & _); exact (l,v).
  Defined.

  Theorem FRACTRAN_REG_FRACTRAN_HALTING : FRACTRAN_REG_HALTING ⪯ FRACTRAN_HALTING.
  Proof.
    exists f; intros (n & P & v); simpl; tauto.
  Qed.

End FRACTRAN_REG_FRACTRAN_HALTING.

Check FRACTRAN_REG_FRACTRAN_HALTING.


