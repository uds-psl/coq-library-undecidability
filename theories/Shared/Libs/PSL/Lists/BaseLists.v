From Undecidability.Shared.Libs.PSL Require Export Prelim EqDec.

Export List.ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).

(* DLW it is not possible to put this one at level 0 because
   the | token while conflict with its use as a separator
   in eg match ... with ... end expressions *)

#[warning="-closed-notation-not-level-0"]
  Notation "| A |" := (length A) (at level 65).

(* ** Lists *)

Create HintDb list.

(* *** Decisions for lists *)

#[global] Instance list_in_dec X (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Qed.
