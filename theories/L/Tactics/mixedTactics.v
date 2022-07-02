Require Import Undecidability.Shared.Libs.PSL.Base Lia Ring. 

Tactic Notation "destruct" "_":= 
  match goal with
    | [ |- context[match ?X with _ => _ end] ] => destruct X
  end.

Tactic Notation "destruct" "_" "eqn" ":" ident(E)   :=
  match goal with
    | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:E
  end.

Tactic Notation "destruct" "*" :=
  repeat destruct _.

Ltac dec :=
  match goal with
    | [ |- context[Dec ?X] ] => decide X
  end.

Ltac trace :=
  match goal with
    |- ?G => idtac "Trace:";idtac G
  end.

Require Export ZArith. 
Ltac leq_crossout :=
       try zify;try apply Zle_0_minus_le; ring_simplify;
       repeat eapply Z.add_nonneg_nonneg;try now (repeat eapply Z.mul_nonneg_nonneg;easy).

Tactic Notation (at level 3) "repeat'" tactic3(t) :=
  let rec loop := (once t);try loop in loop.
