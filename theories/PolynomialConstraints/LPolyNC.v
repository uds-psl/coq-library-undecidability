(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem:
    Linear Polynomial (over N) Constraint Solvability (LPolyNC_SAT)

  A linear polynomial constraint has one of the following shapes
    x ≐ 1
    x ≐ y + z
    x ≐ X * y (where X is the polynomial indeterminate)

  A polynomial is mechanized by a list of its coefficients.

  LPolyNC_SAT:
    Given a list of constraints,
    is there a valuation φ : nat -> list nat such that
    for each constraint c we have
      if c is x ≐ 1, then φ(x) ≃ [1]
      if c is x ≐ y + z, then φ(x) ≃ poly_add (φ(y)) (φ(z))
      if c is x ≐ X * y, then φ(x) ≃ poly_mult [0; 1] (φ(y))
    where ≃ is equality up to trailing zeroes?
*)

Require Import List.
Import ListNotations.

Definition poly : Set := list nat.

(* constraint representation *)
Inductive polyc : Set :=
  | polyc_one : nat -> polyc
  | polyc_sum : nat -> nat -> nat -> polyc
  | polyc_prod : nat -> nat -> polyc.

(* test whether all coefficients are equal, default to 0 *)
Definition poly_eq (p q: poly) : Prop :=
  forall i, nth i p 0 = nth i q 0.

Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

(* polynomial addition *)
Fixpoint poly_add (p q: poly) : poly :=
  match p, q with
  | [], q => q
  | p, [] => p
  | (c :: p), (d :: q) => (c + d) :: poly_add p q
  end.

(* polynomial multiplication *)
Fixpoint poly_mult (p q: poly) : poly :=
  match p with
  | [] => []
  | (c :: p) => poly_add (map (fun a => c * a) q) (0 :: (poly_mult p q))
  end.

Definition polyc_sem (φ: nat -> poly) (c: polyc) :=
  match c with
    | polyc_one x => φ x ≃ [1]
    | polyc_sum x y z => φ x ≃ poly_add (φ y) (φ z)
    | polyc_prod x y => φ x ≃ poly_mult [0; 1] (φ y)
  end.

(* given a list l of constraints, 
  is there a valuation φ satisfying each constraint? *)
Definition LPolyNC_SAT (l : list polyc) := exists φ, forall c, In c l -> polyc_sem φ c.
