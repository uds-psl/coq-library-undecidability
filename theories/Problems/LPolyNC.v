(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Problem:
    Linear Polynomial[N] constraint solvability (LPolyNC)

  A uniform Diophantine constraint has the shape 
    1 + x + y * y ≐ z
  and is represented by a triple (x, y, z).

  H10UC:
    Given a list of constraints,
    is there a valuation φ : nat -> nat such that
    1 + φ(xᵢ) + φ(yᵢ) * φ(yᵢ) = φ(zᵢ) for i = 1...n?
*)

Require Import List.
Import ListNotations.

(* uniform constraint representation *)
Definition poly : Set := list nat.

Inductive polyc : Set :=
  | polyc_one : nat -> polyc
  | polyc_sum : nat -> nat -> nat -> polyc
  | polyc_prod : nat -> poly -> nat -> polyc.

(* test whether all coefficients are equal, default to 0 *)
Definition poly_eq (p q: poly) : Prop :=
  forall i, nth i p 0 = nth i q 0.

Notation "p ≃ q" := (poly_eq p q) (at level 65).

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
    | polyc_prod x p y => φ x ≃ poly_mult p (φ y)
  end.

(* list of uniform constraint representations *)
Definition LPolyNC_PROBLEM := list polyc.

(* given a list l of constraints, 
  is there a valuation φ satisfying each constraint? *)
Definition LPolyNC_SAT (l : LPolyNC_PROBLEM) := exists φ, forall c, In c l -> polyc_sem φ c.
