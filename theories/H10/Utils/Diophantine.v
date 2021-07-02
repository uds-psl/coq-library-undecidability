From Undecidability.H10 Require Import H10.
From Undecidability.H10.Dio Require Import dio_single.

From Coq Require Import List Vector Nat.
Import ListNotations Vector.VectorNotations.

Definition Diophantine {k} (R : Vector.t nat k -> Prop) := 
  exists k', exists P1 P2 : dio_polynomial (Fin.t k') (Fin.t k),
   forall v : Vector.t nat k,
   let ρ := (fun i => Vector.nth v i) in
     R v <-> exists ν, dp_eval ν ρ P1 = dp_eval ν ρ P2.

Definition Diophantine' {k} (R : Vector.t nat k -> nat -> Prop) : Prop :=
  Diophantine (fun v : Vector.t nat (S k) =>
   match v with cons _ m n v => fun R : Vector.t nat n -> nat -> Prop =>
     R v m
   end R).

Definition functional {X Y} (R : X -> Y -> Prop) :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.
  