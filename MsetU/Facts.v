Require Import ssreflect ssrbool ssrfun.

Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  apply : well_founded_ind.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
Qed.
Arguments measure_ind {X}.


(*transforms a goal (A -> B) -> C into goals A and B -> C*)
Lemma unnest : forall (A B C : Prop), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

(*duplicates argument*)
Lemma copy {A : Prop} : A -> A * A.
Proof. done. Qed.

(*swaps first two arguments*)
Lemma swap (P Q R : Prop) : (P -> Q -> R) -> (Q -> P -> R).
Proof. by auto. Qed.
