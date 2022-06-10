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

Tactic Notation (at level 3) "repeat'" tactic3(t) :=
  let rec loop := (once t);try loop in loop.
