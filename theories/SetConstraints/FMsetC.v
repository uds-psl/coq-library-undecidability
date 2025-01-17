(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(** * Solvability of finite multiset constraints FMsetC_SAT  *)

(* 
  Problem:
    Finite Multiset Constraint Solvability (FMsetC_SAT)

  Finite multisets with one constant 0 and one unary constructor h.
  A finite multiset A is represented by a list of its elements.
  The element (h^n 0) is represented by the natural number n.

  Constraints are of shape:
    x ≐ [0]
    x ≐ y ⊍ z
    x ≐ h (y) 

  Constraint semantics:
    φ(y ⊍ z) = φ(y) ++ φ(z)
    φ(h (y)) = map h (φ(y))

  FMsetC:
    Given a list of constraints,
    is there a valuation φ : nat -> list nat such that
    for each constraint c we have
      if c is x ≐ [0], then φ(x) ≡ [0]
      if c is x ≐ y ⊍ z, then φ(x) ≡ φ(y) ++ φ(z)
      if c is x ≐ h (y), then φ(x) ≡ map S (φ(y))
    where ≡ is equality up to permutation?
  
  References:
    [1] Paliath Narendran: Solving Linear Equations over Polynomial Semirings.
      LICS 1996: 466-472, doi: 10.1109/LICS.1996.561463
*)

From Stdlib Require Import PeanoNat List.
Import ListNotations.

(* list equality up to permutation *)
Definition mset_eq (A B: list nat) : Prop := 
  forall c, count_occ Nat.eq_dec A c = count_occ Nat.eq_dec B c.
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).

(* constraints *)
Inductive msetc : Set :=
  | msetc_zero : nat -> msetc
  | msetc_sum : nat -> nat -> nat -> msetc
  | msetc_h : nat -> nat -> msetc.

(* constraint semantics *)
Definition msetc_sem (φ: nat -> list nat) (c: msetc) :=
  match c with
    | msetc_zero x => φ x ≡ [0]
    | msetc_sum x y z => φ x ≡ (φ y) ++ (φ z)
    | msetc_h x y => φ x ≡ map S (φ y)
  end.

(* given a list l of constraints, 
  is there a valuation φ satisfying each constraint? *)
Definition FMsetC_SAT (l : list msetc) := exists φ, forall c, In c l -> msetc_sem φ c.
