(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import vec.

From Undecidability.MuRec 
  Require Import recalg ra_univ ra_univ_andrej.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(* We build a primitive µ-recursive algorithm

     ra_pr_univ : recalg 2

   with two argument (n##k##ø)
     - n encodes a finitary valuation nat -> nat
     - k encodes a finite list of H10C constraints
   
   1) ra_pr_univ always terminates (it is primitive recursive)
   2) ra_pr_univ outputs 0 iff the valuation n solves the equations k

*)

Definition ra_pr_univ := ra_h10c_eval.

Theorem ra_pr_univ_pr : prim_rec ra_pr_univ.
Proof. apply ra_h10c_eval_pr. Qed.

Definition PRIMEREC_UNIV_PROBLEM := nat.
Definition PRIMEREC_UNIV_MEETS_ZERO (n : PRIMEREC_UNIV_PROBLEM) := exists k, ⟦ra_pr_univ⟧ (k##n##vec_nil) 0.

(* We build a universal µ-recusive algorithm of size 8708

      ra_univ : recalg 1

    which is just a particular µ-recursive algorithm. It is
    universal w.r.t. elementary Diophantine constraints 
    as established in Reductions/H10C_SAT_to_RA_UNIV_HALT.v

    Basically, its termination predicate RA_UNIV_HALT 
    can simulate the solvability of any list of elementary 
    Diophantine constraints, making it undecidable *)

Definition ra_univ := ra_min_univ ra_pr_univ.

Definition RA_UNIV_PROBLEM := nat.
Definition RA_UNIV_HALT (n : RA_UNIV_PROBLEM) : Prop := ex (⟦ra_univ⟧ (n##vec_nil)).
Definition RA_UNIV_AD_HALT (n : RA_UNIV_PROBLEM) : Prop := ex (⟦ra_univ_ad⟧ (n##vec_nil)).

(* Check ra_size ra_univ. *)
(* Eval compute in ra_size ra_univ. *)
(* Check ra_size ra_univ_ad. *)
(* Eval compute in ra_size ra_univ_ad. *)

Definition PRIMESEQ_PROBLEM := { f : recalg 1 | prim_rec f }.
Definition PRIMESEQ_MEETS_ZERO (P : PRIMESEQ_PROBLEM) := exists n, ⟦proj1_sig P⟧ (n##vec_nil) 0.

Definition NATSEQ_PROBLEM := nat -> nat.
Definition NATSEQ_MEETS_ZERO (f : NATSEQ_PROBLEM) : Prop := exists n, f n = 0.

Definition BOOLSEQ_PROBLEM := nat -> bool.
Definition BOOLSEQ_MEETS_TRUE (f : BOOLSEQ_PROBLEM) : Prop := exists n, f n = true.