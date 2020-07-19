(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Simple Semi-unification (SSemiU)
    Semi-unification (SemiU)
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

(* are there substitutions (φ, ψ0, ψ1) that model each constraint? *)
Definition SSemiU (p : list constraint) := 
  exists (φ ψ0 ψ1: valuation), forall (c : constraint), In c p -> models φ ψ0 ψ1 c.


(* Semi-unification Definition *)

(* inequality: s ≤ t *)
Definition inequality : Set := (term * term).

(* φ solves s ≤ t, if there is ψ such that ψ (φ (s)) = φ (s) *)
Definition solution (φ : valuation) : inequality -> Prop := 
  fun '(s, t) => exists (ψ : valuation), substitute ψ (substitute φ s) = substitute φ t.

(* is there a substitution φ that solves all inequalities? *)
Definition SemiU (p: list inequality) := 
  exists (φ: valuation), forall (c: inequality), In c p -> solution φ c.
