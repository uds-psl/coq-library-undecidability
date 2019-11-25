(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Problem:
    Finite multiset term constraint solvability (FMsetTC)

  Finite multisets with one constant 0 and one unary constructor h
  A finite multiset A is represented by a list of its elements.
  The element (h^n 0) is represented by the natural number n.

  Terms t, u:
    t, u ::= zero | t ⊍ u | h (t) | x : nat
    where x ranges over multiset variables
  
  Constraints:
    t ≐ u 

  Term Interpretation:
    φ(zero) = [0]
    φ(t ⊍ u) = φ(t) ++ φ(u)
    φ(h (t)) = map h (φ(t))

  FMsetTC:
    Given a list (t₁ ≐ u₁),...,(tₙ ≐ uₙ) of constraints,
    is there a valuation φ : nat -> list nat such that
    φ(t₁) ≡ φ(u₁),..., φ(tₙ) ≡ φ(uₙ),
    where ≡ is equality up to permutation?
  
  References:
    [1] Paliath Narendran: Solving Linear Equations over Polynomial Semirings.
      LICS 1996: 466-472, doi: 10.1109/LICS.1996.561463
*)

Require Import PeanoNat.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.FMsetC.

(* terms *)
Inductive mset_term : Set :=
  | mset_term_zero : mset_term
  | mset_term_var : nat -> mset_term
  | mset_term_plus : mset_term -> mset_term -> mset_term
  | mset_term_h : mset_term -> mset_term.

(* evaluate an mset wrt. a valuation φ *)
Fixpoint mset_sem (φ : nat -> list nat) (A : mset_term) : list nat :=
  match A with
    | mset_term_zero => [0]
    | mset_term_var x => φ x
    | mset_term_plus A B => (mset_sem φ A) ++ (mset_sem φ B)
    | mset_term_h A => map S (mset_sem φ A)
  end.

(* list of constraints *)
Definition FMsetTC_PROBLEM := list (mset_term * mset_term).

(* is there a valuation φ that satisfies all contraints *)
Definition FMsetTC_SAT (l : FMsetTC_PROBLEM) := 
  exists (φ : nat -> list nat), forall (A B : mset_term), In (A, B) l -> (mset_sem φ A) ≡ (mset_sem φ B).
