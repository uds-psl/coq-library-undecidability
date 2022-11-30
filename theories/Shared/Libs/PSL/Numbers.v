Require Import Undecidability.Shared.Libs.PSL.Prelim.
Require Import Lia.

(* ** Numbers **)

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> 
  forall x, p x.
Proof.
  intros D x. apply D. revert x.
  enough (forall n y, f y < n -> p y) by eauto.
  intros n. induction n; intros y E. 
  - exfalso; lia.
  - apply D. intros x F. apply IHn. lia.
Qed.

Lemma complete_induction (p : nat -> Prop) (x : nat) :
  (forall x, (forall y, y<x -> p y) -> p x) -> p x.
Proof. intros H. apply (@size_induction nat id p H x). Qed.

Section Iteration.
  Variable (X: Type) (f: X -> X).

  Fixpoint it (n : nat) (x : X) : X := 
    match n with
      | 0 => x
      | S n' => f (it n' x)
    end.

End Iteration.
