Require Import Lia.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* induction/recursion principle wrt. a decreasing measure f *)
(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

(* duplicates argument *)
Lemma copy {A : Prop} : A -> A * A.
Proof. done. Qed.

Lemma unnest (X Y Z: Type): X -> (Y -> Z) -> (X -> Y) -> Z.
Proof. by auto. Qed.
