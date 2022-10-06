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

From Undecidability.FRACTRAN
  Require Import FRACTRAN FRACTRAN_sss prime_seq.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Set Implicit Arguments.

Section FRACTRAN_ALT_HALTING_HALTING.

  Let f : FRACTRAN_ALT_PROBLEM -> FRACTRAN_PROBLEM.
  Proof.
    intros (l & n & v).
    exact (l,(ps 1 * exp 1 v)).
  Defined.

  Theorem FRACTRAN_ALT_HALTING_HALTING : FRACTRAN_ALT_HALTING ⪯ Halt_FRACTRAN.
  Proof. 
    exists f; intros (n & P & v).
    rewrite Halt_FRACTRAN_iff. simpl. firstorder.
  Qed.

End FRACTRAN_ALT_HALTING_HALTING.

Check FRACTRAN_ALT_HALTING_HALTING.

Section FRACTRAN_REG_FRACTRAN_HALTING.

  Let f : FRACTRAN_REG_PROBLEM -> FRACTRAN_PROBLEM.
  Proof.
    intros (l & v & _); exact (l,v).
  Defined.

  Theorem FRACTRAN_REG_FRACTRAN_HALTING : FRACTRAN_REG_HALTING ⪯ Halt_FRACTRAN.
  Proof.
    exists f; intros (n & P & v). rewrite Halt_FRACTRAN_iff. tauto.
  Qed.

End FRACTRAN_REG_FRACTRAN_HALTING.

Check FRACTRAN_REG_FRACTRAN_HALTING.
