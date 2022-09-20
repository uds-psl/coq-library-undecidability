From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.

Notation vector_to_list := Vector.to_list.

Lemma vector_to_list_eta (X : Type) (n : nat) (v : Vector.t X (S n)) :
  Vector.hd v :: vector_to_list (Vector.tl v) = vector_to_list v.
Proof. destruct_vector. cbn. reflexivity. Qed.

(* Technical compatibility lemma: Coq's standard library is soo inconsistent... *)
Lemma fold_left_vector_to_list (X Y : Type) (n : nat) (f : Y -> X -> Y) (v : Vector.t X n) (a : Y) :
  Vector.fold_left f a v = fold_left f (vector_to_list v) a.
Proof. revert a. induction v as [ | x n v IH]; intros; cbn in *; f_equal; auto. Qed.
