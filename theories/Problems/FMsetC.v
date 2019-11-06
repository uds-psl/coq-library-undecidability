(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Problem:
    Finite multiset constraint solvability (FMsetC)

  Finite multisets with one constant 0 and one unary constructor h
  A finite multiset A is represented by a list of its elements.
  The element (h^n 0) is represented by the natural number n.

  Terms t, u:
    t, u ::= n : list nat | x : nat | t ⊍ u | t ⩀ u | h (t)
    where x ranges over multiset variables
  
  Constraints:
    t ≐ u 

  FMsetC:
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

(* terms *)
Inductive mset_term : Set :=
  | mset_term_const : list nat -> mset_term
  | mset_term_var : nat -> mset_term
  | mset_term_plus : mset_term -> mset_term -> mset_term
  | mset_term_cap : mset_term -> mset_term -> mset_term
  | mset_term_h : mset_term -> mset_term.

(* list equality up to permutation *)
Definition mset_eq (A B : list nat) : Prop := 
  forall c, count_occ Nat.eq_dec A c = count_occ Nat.eq_dec B c.
Notation "A ≡ B" := (mset_eq A B) (at level 65).

(* removes the first occurrence of n in A, fails otherwise *)
Fixpoint mset_try_remove (n : nat) (A : list nat) : option (list nat) :=
  match A with
  | [] => None
  | (m :: A) => if Nat.eqb n m then Some A else option_map (cons m) (mset_try_remove n A)
  end.

(* multiset intersection *)
Fixpoint mset_intersect (A B : list nat) : list nat :=
  match A with
  | [] => []
  | (n :: A) => 
    match mset_try_remove n B with
    | None => mset_intersect A B
    | Some(B) => n :: (mset_intersect A B)
    end
  end.

(* evaluate an mset wrt. a valuation φ *)
Fixpoint mset_sem (φ : nat -> list nat) (A : mset_term) : list nat :=
  match A with
    | mset_term_const l => l
    | mset_term_var x => φ x
    | mset_term_plus A B => (mset_sem φ A) ++ (mset_sem φ B)
    | mset_term_cap A B => mset_intersect (mset_sem φ A) (mset_sem φ B)
    | mset_term_h A => map S (mset_sem φ A)
  end.

(* list of constraints *)
Definition FMsetC_PROBLEM := list (mset_term * mset_term).

(* is there a valuation φ that satisfies all contraints *)
Definition FMsetC_SAT (l : FMsetC_PROBLEM) := 
  exists (φ : nat -> list nat), forall (A B : mset_term), In (A, B) l -> (mset_sem φ A) ≡ (mset_sem φ B).
