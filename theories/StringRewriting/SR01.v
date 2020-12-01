Require Import List Relation_Operators.

Definition Symbol : Set := nat * option nat.

(* rules ab -> cd *)
Definition Srs := list ((Symbol * Symbol) * (Symbol * Symbol)).

Inductive step (srs: Srs) : list Symbol -> list Symbol -> Prop := 
  | step_intro {u v a b c d} : 
      In ((a, b), (c, d)) srs -> step srs (u ++ a :: b :: v) (u ++ c :: d :: v).

(*  *)
Definition reachable (srs: Srs) : list Symbol -> list Symbol -> Prop := 
  clos_refl_trans (list Symbol) (step srs).

(*
given a 2-2-srs and symbols a, b is there an n such that a^n rewrites to b^n?
*)
Definition SR2ab : Srs * Symbol * Symbol -> Prop :=
  fun '(srs, a, b) => exists n, reachable srs (repeat a n) (repeat b n).