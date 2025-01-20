(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

From Stdlib Require Import ssreflect ssrbool ssrfun.
From Stdlib Require Import PeanoNat Lia Permutation List.
Import ListNotations.

Set Default Goal Selector "!".

(* misc facts *)

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest {A B C: Prop} : A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Lemma count_occ_cons {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A a c} :
  count_occ D (a :: A) c = count_occ D (locked [a]) c + count_occ D A c.
Proof.
  rewrite /count_occ /is_left -lock. by case: (D a c).
Qed.

Lemma seq_last start length : seq start (S length) = (seq start length) ++ [start + length].
Proof.
  by rewrite -/(1 + length) (Nat.add_comm 1 length) seq_app.
Qed.

(* Permutation facts *)
Ltac Permutation_trivial :=
  apply /(Permutation_count_occ Nat.eq_dec) => ?; rewrite ?(count_occ_app, count_occ_cons); lia.

Lemma Permutation_refl' {X : Type} (l l' : list X) : l = l' -> Permutation l l'.
Proof. by move=> ->. Qed.

Lemma Permutation_map_lt_nil {A f} :
  (forall n, n < f n) -> Permutation (map f A) A -> A = [].
Proof.
  move=> Hf /Permutation_sym /(@Permutation_in nat).
  move: A => [|a A]; first done.
  move: (a :: A) (in_eq a A) => {}A + HA.
  elim /(Nat.measure_induction _ id): a.
  move=> a IH /HA /in_map_iff [b] [?]. subst a.
  by apply: (IH b (Hf b)).
Qed.
