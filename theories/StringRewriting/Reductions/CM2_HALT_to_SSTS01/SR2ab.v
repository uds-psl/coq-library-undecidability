Require Import List Relation_Operators.

Definition Symbol : Set := nat * option nat.

(* rules ab -> cd *)
Definition Srs := list ((Symbol * Symbol) * (Symbol * Symbol)).

Inductive step (srs: Srs) : list Symbol -> list Symbol -> Prop := 
  | step_intro {u v a b c d} : 
      In ((a, b), (c, d)) srs -> step srs (u ++ a :: b :: v) (u ++ c :: d :: v).

Definition multi_step (srs: Srs) : list Symbol -> list Symbol -> Prop := 
  clos_refl_trans (list Symbol) (step srs).

Definition SR2ab : Srs * Symbol * Symbol -> Prop :=
  fun '(srs, a, b) => exists n, multi_step srs (repeat a (1+n)) (repeat b (1+n)).
