Require Import Arith Lia.

From Coq Require Import ssreflect ssrbool ssrfun.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
  Proof.
  apply : well_founded_ind.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
  Qed.
Arguments measure_ind {X}.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  apply : well_founded_induction_type.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
Qed.
Arguments measure_rect {X}.

(* duplicates argument *)
Lemma copy {A : Prop} : A -> A * A.
Proof. done. Qed.

Lemma unnest (X Y Z: Type): X -> (Y -> Z) -> (X -> Y) -> Z.
Proof. by auto. Qed.
