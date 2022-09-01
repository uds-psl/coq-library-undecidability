(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Simple Semi-unification (SSemiU)
    Semi-unification (SemiU)
    Right-uniform Two-Inequality Semi-unification (RU2SemiU)
    Left-uniform Two-Inequality Semi-unification (LU2SemiU)
*)

(*
  Literature:
  [1] Andrej Dudenhefner. "Undecidability of Semi-Unification on a Napkin"
      5th International Conference on Formal Structures for Computation and Deduction (FSCD 2020): 9:1-9:16
      https://drops.dagstuhl.de/opus/volltexte/2020/12331
*)

Require Import List.

(* terms are built up from atoms and a binary term constructor arr *)
Inductive term : Set :=
  | atom : nat -> term
  | arr : term -> term -> term.

Definition valuation : Set := nat -> term.

(* substitute atoms n of a term t by (f n) *)
Fixpoint substitute (f: valuation) (t: term) : term :=
  match t with
  | atom n => f n
  | arr s t => arr (substitute f s) (substitute f t)
  end.

(* Simple Semi-unification Definition *)

(* simple semi unification constraint
  ((a, x), (y, b)) mechanizes the constraint (a|x|ϵ ≐ ϵ|y|b) *)
Definition constraint : Set := ((bool * nat) * (nat * bool)).

(* constraint semantics, 
  (φ, ψ0, ψ1) models a|x|ϵ ≐ ϵ|y|b if ψa (φ (x)) = πb (φ (y)) *)
Definition models (φ ψ0 ψ1: valuation) : constraint -> Prop :=
  fun '((a, x), (y, b)) => 
    match φ y with
    | atom _ => False
    | arr s t => (if b then t else s) = substitute (if a then ψ1 else ψ0) (φ x)
    end.

(* Simple Semi-unification *)
(* are there substitutions (φ, ψ0, ψ1) that model each constraint? *)
Definition SSemiU (p : list constraint) := 
  exists (φ ψ0 ψ1: valuation), forall (c : constraint), In c p -> models φ ψ0 ψ1 c.


(* Semi-unification Definition *)

(* inequality: s ≤ t *)
Definition inequality : Set := (term * term).

(* φ solves s ≤ t, if there is ψ such that ψ (φ (s)) = φ (s) *)
Definition solution (φ : valuation) : inequality -> Prop := 
  fun '(s, t) => exists (ψ : valuation), substitute ψ (substitute φ s) = substitute φ t.

(* Semi-unification *)
(* is there a substitution φ that solves all inequalities? *)
Definition SemiU (p: list inequality) := 
  exists (φ: valuation), forall (c: inequality), In c p -> solution φ c.

(* Right-uniform Two-Inequality Semi-unification *)
(* All right-hand sides of inequalities are identical, there are exactly two inequlities *)
Definition RU2SemiU : term * term * term -> Prop := 
  fun '(s0, s1, t) => exists (φ ψ0 ψ1: valuation), 
    substitute ψ0 (substitute φ s0) = substitute φ t /\ substitute ψ1 (substitute φ s1) = substitute φ t.

(* Left-uniform Two-Inequality Semi-unification *)
(* All right-hand sides of inequalities are identical, there are exactly two inequlities *)
Definition LU2SemiU : term * term * term -> Prop := 
  fun '(s, t0, t1) => exists (φ ψ0 ψ1: valuation), 
    substitute ψ0 (substitute φ s) = substitute φ t0 /\ substitute ψ1 (substitute φ s) = substitute φ t1.
