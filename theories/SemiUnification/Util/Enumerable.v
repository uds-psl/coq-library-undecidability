(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import Undecidability.Synthetic.EnumerabilityFacts.

From Stdlib Require Import List Lia.
From Stdlib Require Cantor.
From Stdlib Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* Enumerable X allows injection into nat *)
Class Enumerable (X: Type) :=
  {
    to_nat : X -> nat;
    of_nat : nat -> X;
    enumP {x: X} : of_nat (to_nat x) = x
  }.

#[export] Instance nat_Enumerable : Enumerable nat.
Proof. by exists id id. Qed.

#[export] Instance bool_Enumerable : Enumerable bool.
Proof.
  exists (fun b => if b then 1 else 0) (fun n => if n is 0 then false else true).
  by case.
Qed.

#[export] Instance prod_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X * Y).
Proof.
  exists 
    (fun '(x, y) => Cantor.to_nat (to_nat x, to_nat y))
    (fun n => match Cantor.of_nat n with | (n1, n2) => (of_nat n1, of_nat n2) end).
  move=> [x y]. by rewrite Cantor.cancel_of_to !enumP.
Qed.

#[export] Instance sum_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X + Y).
Proof.
  exists 
    (fun t => match t with | inl x => to_nat (0, to_nat x) | inr y => to_nat (1, to_nat y) end)
    (fun n => match of_nat n with | (0, n) => inl (of_nat n) | (1, n) => inr (of_nat n) | _ => inl (of_nat n) end).
  by case => ?; rewrite ?enumP.
Qed.

Opaque RoseTree.of_nat RoseTree.to_nat.

#[export] Instance list_Enumerable {X: Type} {enumX: Enumerable X} : Enumerable (list X).
Proof.
  exists
    (fun l => RoseTree.to_nat (RoseTree.mk (map (fun x => RoseTree.mk (repeat (RoseTree.mk nil) (to_nat x))) l)))
    (fun n => match (RoseTree.of_nat n) with RoseTree.mk rs => map (fun '(RoseTree.mk r's) => of_nat (length r's)) rs end).
  move=> l /=. rewrite RoseTree.cancel_of_to map_map -[RHS]map_id.
  apply: map_ext => ?. by rewrite repeat_length enumP.
Qed.
