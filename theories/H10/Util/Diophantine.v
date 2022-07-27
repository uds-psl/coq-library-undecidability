From Undecidability.H10 Require Export H10.
From Undecidability.H10.Dio Require Import dio_single.

From Coq Require Import List Vector Nat.
Import ListNotations Vector.VectorNotations.

Definition Diophantine' {k} (R : Vector.t nat k -> nat -> Prop) : Prop :=
  Diophantine (fun v : Vector.t nat (S k) =>
   match v with cons _ m n v => fun R : Vector.t nat n -> nat -> Prop =>
     R v m
   end R).

Definition functional {X Y} (R : X -> Y -> Prop) :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.
