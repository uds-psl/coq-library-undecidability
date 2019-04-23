Require Import PslBase.Base.

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
