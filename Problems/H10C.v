Require Import List.

Inductive h10c : Set :=
  | h10c_one : nat -> h10c
  | h10c_plus : nat -> nat -> nat -> h10c
  | h10c_mult : nat -> nat -> nat -> h10c.

Definition h10c_sem c φ :=
  match c with
    | h10c_one x      => φ x = 1
    | h10c_plus x y z => φ x + φ y = φ z
    | h10c_mult x y z => φ x * φ y = φ z
  end.

Local Notation "〚 c 〛" := (h10c_sem c).

Definition H10C_PROBLEM := list h10c.
Definition H10C_SAT (l : H10C_PROBLEM) := exists φ, forall c, In c l ->〚c〛φ.





