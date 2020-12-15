(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Simple Semi-Thue System 01 Rewriting (SSTS01)
*)

(*
  Literature:
  [1] Dudenhefner, Andrej, and Jakob Rehof. 
      "Undecidability of Intersection Type Inhabitation at Rank 3 and its Formalization." 
      Fundamenta Informaticae 170.1-3 (2019): 93-110.
*)

Require Import List Relation_Operators.

(* A simple semi-Thue system consists of rules "ab -> cd" where a, b, c, d : nat *)
Definition Ssts := list ((nat * nat) * (nat * nat)).

(* one-step rewriting relation 
   if (ab -> cd) in ssts, then uabv -> ucdv where u, v : list nat *)
Inductive step (ssts: Ssts) : list nat -> list nat -> Prop := 
  | step_intro {u v: list nat} {a b c d: nat} : 
      In ((a, b), (c, d)) ssts -> step ssts (u ++ a :: b :: v) (u ++ c :: d :: v).

(* reflexive, transitive closure of one-step rewriting *)
Definition multi_step (ssts: Ssts) : list nat -> list nat -> Prop := 
  clos_refl_trans (list nat) (step ssts).

(* simple semi-Thue system 01 rewriting, that is
   for given a simple semi-Thue system, does 0^(1+n) ->> 1^(1+n) hold for some n? *)
Definition SSTS01 : Ssts -> Prop :=
  fun ssts => exists n, multi_step ssts (repeat 0 (1+n)) (repeat 1 (1+n)).
  