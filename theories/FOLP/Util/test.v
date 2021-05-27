Require Import List.
Import ListNotations.

Notation "x '[' y ']'" := (Nat.add x y) (at level 7, left associativity, format "x '/' [ y ]", only printing) : subst_scope.

Open Scope subst_scope.

Section FullFOL.
  Context {Sigma : Signature}.

  Lemma var_subst phi :
    phi +[var_term] = phi.