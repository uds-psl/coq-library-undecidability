Require Import List.

(* uniform h10 constraints have the shape 1 + x + y * y = z *)
Definition h10uc: Set := nat * nat * nat.
Definition h10uc_sem (φ: nat -> nat) '(x, y, z) :=
  1 + (φ x) + (φ y) * (φ y) = φ z.


Definition H10UC_PROBLEM := list h10uc.
(* given a list l of uniform h10 constraints, 
  is there a valuation φ satisfying each constraint? *)
Definition H10UC_SAT (l : H10UC_PROBLEM) := exists φ, forall c, In c l -> h10uc_sem φ c.
