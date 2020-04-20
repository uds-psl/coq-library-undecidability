Definition compl {X} (p : X -> Prop) := fun x : X => ~ p x.
Definition reflects (b : bool) (P : Prop) := P <-> b = true.

Definition decider {X} (f : X -> bool) (P : X -> Prop) : Prop :=
  forall x, reflects (f x) (P x).
Definition decidable {X} (P : X -> Prop) : Prop :=
  exists f : X -> bool, decider f P.
Definition inf_decidable {X} (P : X -> Prop) : Type :=
  { f : X -> bool | decider f P}.

Definition enumerator{X} (f : nat -> option X) (p : X -> Prop) : Prop :=
  forall x, p x <-> exists n, f n = Some x.
Definition enumerable {X} (p : X -> Prop) : Prop :=
  exists f : nat -> option X, enumerator f p.
Definition inf_enumerable {X} (p : X -> Prop) : Type :=
  { f : nat -> option X | enumerator f p}.

Definition semi_decider {X} (f : X -> nat -> bool) (p : X -> Prop) : Prop :=
  forall x, p x <-> exists n, f x n = true.
Definition semi_decidable {X} (p : X -> Prop) : Prop :=
  exists f : X -> nat -> bool, semi_decider f p.
Definition inf_semi_decidable {X} (p : X -> Prop) : Type :=
  { f : X -> nat -> bool | semi_decider f p}.

Definition reduction {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) :=
  forall x, P x <-> Q (f x).
Definition reduces {X Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists f : X -> Y, reduction f P Q.
Definition inf_reduces {X Y} (P : X -> Prop) (Q : Y -> Prop) :=
  { f : X -> Y | reduction f P Q}.
Notation "P ⪯ Q" := (reduces P Q) (at level 70).
