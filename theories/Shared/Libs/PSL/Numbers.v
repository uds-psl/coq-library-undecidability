From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import EqDec.

(* ** Numbers **)

Lemma complete_induction (p : nat -> Prop) (x : nat) :
(forall x, (forall y, y<x -> p y) -> p x) -> p x.

Proof. intros A. apply A. induction x ; intros y B.
exfalso ; lia.
apply A. intros z C. apply IHx. lia. Qed.

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> 
  forall x, p x.

Proof. 
  intros IH x. apply IH. 
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. lia.
    - intros y B. apply IH. intros z C. apply IHn. lia. }
  apply G.
Qed.

Lemma size_induction_dep L (X : L -> Type) (f : forall l, X l -> nat) (p : forall l, X l -> Type) :
  (forall l x, (forall l' y, f l' y < f l x -> p l' y) -> p l x) -> 
  forall l x, p l x.
Proof. 
  intros IH l x. apply IH. intros l'.
  assert (G: forall n l' y, f l' y < n -> p l' y).
  { intros n. induction n; intros l'' y.
    - intros B. exfalso. lia.
    - intros B. apply IH. intros ll z C. eapply IHn. lia. }
  apply G.
Qed.

#[global]
Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  Compare_dec.le_dec x y.

Lemma size_recursion (X : Type) (sigma : X -> nat) (p : X -> Type) :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) -> 
  forall x, p x.
Proof.
  intros D x. apply D. revert x.
  enough (forall n y, sigma y < n -> p y) by eauto.
  intros n. induction n; intros y E. 
  - exfalso; lia.
  - apply D. intros x F.  apply IHn. lia.
Qed.

Arguments size_recursion {X} sigma {p} _ _.

Section Iteration.
  Variables (X: Type) (f: X -> X).

  Fixpoint it (n : nat) (x : X) : X := 
    match n with
      | 0 => x
      | S n' => f (it n' x)
    end.

  Lemma it_ind (p : X -> Prop) x n :
    p x -> (forall z, p z -> p (f z)) -> p (it n x).
  Proof.
    intros A B. induction n; cbn; auto.
  Qed.
End Iteration.
