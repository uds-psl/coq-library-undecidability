Require Import Undecidability.Synthetic.Definitions.

(* informative counterparts of (semi-)decidability, enumerability, and many-one reducibility *)

Definition inf_decidable {X} (P : X -> Prop) : Type :=
  { f : X -> bool | decider f P}.

Definition inf_enumerable {X} (P : X -> Prop) : Type :=
  { f : nat -> option X | enumerator f P}.

Definition inf_semi_decidable {X} (P : X -> Prop) : Type :=
  { f : X -> nat -> bool | semi_decider f P}.

Definition inf_reduces {X Y} (P : X -> Prop) (Q : Y -> Prop) :=
  { f : X -> Y | reduction f P Q}.
Infix "⪯ᵢ" := inf_reduces (at level 70).
