(* Running Example: Commutativity of Addition *)

Lemma add_comm (x y : nat) :
  x + y = y + x.
Proof.
  induction x.
  - cbn. rewrite <- plus_n_O. reflexivity.
  - cbn. rewrite IHx, plus_n_Sm. reflexivity.
Qed.


(* Defining commutativity as first-order formula *)
(* Variant 1: de Bruijn formula *)

From Undecidability.FOL Require Import Syntax PA.
Import FullSyntax.

Definition add_comm_fol : form :=
  ∀ ∀ $1 ⊕ $0 == $0 ⊕ $1.

(* Variant 2: HOAS formula *)

From Undecidability.FOL Require Import Hoas.
Require Import Vector.
Import VectorNotations.

Notation "x '⊕' y" := (bFunc Plus ([x; y])) (at level 39) : hoas_scope.
Notation "x '==' y" := (bAtom Eq ([x; y])) (at level 40) : hoas_scope.

Definition add_comm_hoas : form :=
  << ∀' x y, x ⊕ y == y ⊕ x.

Print add_comm_hoas.





