(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

Require Import ssreflect ssrbool ssrfun.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.FMsetC.

Notation "t ⊍ u" := (mset_term_plus t u) (at level 40).
Notation "'h' t" := (mset_term_h t) (at level 38).
Notation "•0" := mset_term_zero.

Coercion mset_term_var : nat >-> mset_term.

Definition mset_sat (φ : nat -> list nat) (l : FMsetC_PROBLEM) := 
  Forall (fun '(A, B) => (mset_sem φ A) ≡ (mset_sem φ B)) l.

Lemma mset_satP {φ l} : mset_sat φ l <-> (forall (A B : mset_term), In (A, B) l -> (mset_sem φ A) ≡ (mset_sem φ B)).
Proof.
  rewrite /mset_sat Forall_forall. constructor.
  - move=> H A B. apply /H.
  - move=> H [A B]. apply /H.
Qed.
