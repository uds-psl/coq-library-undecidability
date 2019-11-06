(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Problem:
    Uniform Diophantine constraint satisfiability (H10UC)

  A uniform Diophantine constraint has the shape 
    1 + x + y * y ≐ z
  and is represented by a triple (x, y, z).

  H10UC:
    Given a list (x₁, y₁, z₁),...,(xₙ, yₙ, zₙ) of constraints,
    is there a valuation φ : nat -> nat such that
    1 + φ(xᵢ) + φ(yᵢ) * φ(yᵢ) = φ(zᵢ) for i = 1...n?
*)

Require Import List.

(* uniform constraint representation *)
Definition h10uc : Set := nat * nat * nat.
Definition h10uc_sem (φ: nat -> nat) '(x, y, z) : Prop :=
  1 + (φ x) + (φ y) * (φ y) = φ z.

(* list of uniform constraint representations *)
Definition H10UC_PROBLEM := list h10uc.

(* given a list l of uniform h10 constraints, 
  is there a valuation φ satisfying each constraint? *)
Definition H10UC_SAT (l : H10UC_PROBLEM) := exists φ, forall c, In c l -> h10uc_sem φ c.
