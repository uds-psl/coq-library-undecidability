From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.

(*For compability:  A more cbn-friendly version of Vector.to_list *)
(* TODO: rework such that every lemma is in terms of Vector.to_list and we can use vector_to_list_correct to transfer? *)

Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X :=
  match v with
  | Vector.nil _ => List.nil
  | Vector.cons _ x n v' => x :: vector_to_list v'
  end.

Lemma vector_to_list_correct (X : Type) (n : nat) (v : Vector.t X n) :
  vector_to_list v = Vector.to_list v.
Proof.
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.

Lemma vector_to_list_length (X : Type) (n : nat) (v : Vector.t X n) :
  length (vector_to_list v) = n.
Proof.
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.

Lemma vector_to_list_eta (X : Type) (n : nat) (v : Vector.t X (S n)) :
  Vector.hd v :: vector_to_list (Vector.tl v) = vector_to_list v.
Proof. destruct_vector. cbn. reflexivity. Qed.
