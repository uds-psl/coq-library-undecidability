(* * Addendum for Vectors ([Vector.t]) *)
(* Author: Maximilian Wuttke *)

Require Import Undecidability.Shared.Libs.PSL.EqDec.
From Coq.Vectors Require Import Fin Vector.

Delimit Scope vector_scope with vector.
Local Open Scope vector.

Module VectorNotations2.

Notation "[ | | ]" := (nil _) (format "[ |  | ]"): vector_scope.
Notation "h ':::' t" := (cons _ h _ t) (at level 60, right associativity) : vector_scope.

Notation "[ | x | ]" := (x ::: [| |]) : vector_scope.
Notation "[ | x ; y ; .. ; z | ] " := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..))
   (format "[ | x ;  y ;  .. ;  z | ] ") : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.

End VectorNotations2.

Import VectorNotations2.

Lemma destruct_vector_single {X : Type} (v : Vector.t X 1) :
  v = [| Vector.hd v |].
Proof. rewrite (Vector.eta v). generalize (Vector.tl v). now apply Vector.case0. Qed.

#[global] Instance Vector_eq_dec n A: eq_dec A -> eq_dec (Vector.t A n).
Proof.
  intros H x y. eapply VectorEq.eq_dec with (A_beq := fun x y => proj1_sig (Sumbool.bool_of_sumbool (H x y))).
  intros ? ?. destruct (Sumbool.bool_of_sumbool).
  cbn. destruct x1; intuition easy.
Defined.

#[global] Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
  intros; hnf.
  destruct (Fin.eqb x y) eqn:E.
  - left. now eapply Fin.eqb_eq.
  - right. intros H. eapply Fin.eqb_eq in H. congruence.
Defined.

Arguments Vector.eqb {_}  _ {_ _}.
