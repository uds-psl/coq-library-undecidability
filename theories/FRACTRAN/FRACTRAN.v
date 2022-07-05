(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** * Halting problem for FRACTRAN programs FRACTRAN_HALTING *)

Require Import Vector List Arith.

From Undecidability.Shared.Libs.DLW 
  Require Import gcd rel_iter pos vec.

Reserved Notation "l '/F/' x ≻ y" (at level 70, no associativity).

Implicit Type l : list (nat*nat).

Definition fractran_regular (l : list (nat * nat)) := Forall (fun c => snd c <> 0) l.

Inductive fractran_step : list (nat*nat) -> nat -> nat -> Prop :=
  | in_fractran_0 : forall p q l n m, q*m = p*n -> (p,q)::l /F/ n ≻ m
  | in_fractran_1 : forall p q l n m', ~ (exists m, (p*n) = m * q) -> l /F/ n ≻ m' -> (p,q)::l /F/ n ≻ m'
where "l /F/ x ≻ y" := (fractran_step l x y).

Reserved Notation "l '/F/' x ▹ y" (at level 70, no associativity).

Inductive fractran_eval : list (nat*nat) -> nat -> nat -> Prop :=
| fractran_eval_stop P n : ~ (exists m, P /F/ n ≻ m) -> P /F/ n ▹ n
| fractran_eval_step P n m m' : P /F/ n ≻ m -> P /F/ m ▹ m' -> P /F/ n ▹ m'
where "l /F/ x ▹ y" := (fractran_eval l x y).

Definition Halt_FRACTRAN '(P, n) :=
  exists m, P /F/ n ▹ m.

Import Vector.VectorNotations.
From Undecidability.FRACTRAN Require Import prime_seq.

Fixpoint enc {k} i (v : Vector.t nat k) : nat := 
  match v with
  | @Vector.nil _ => 1
  | x :: v => (qs i) ^ x * enc (S i) v
  end.

Definition FRACTRAN_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists P : list (nat * nat), fractran_regular P /\
    forall v : Vector.t nat k,
      (forall m, R v m <-> exists j, fractran_eval P (ps 1 * enc 2 v) (j * (qs 1)^m) /\ ~ divides (qs 1) j).
