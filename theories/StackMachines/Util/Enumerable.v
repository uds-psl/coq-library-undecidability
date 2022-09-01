(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Cantor.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* Enumerable X allows injection into nat *)
Class Enumerable (X: Type) :=
  {
    to_nat : X -> nat;
    of_nat : nat -> X;
    enumP {x: X} : of_nat (to_nat x) = x
  }.

(* to_nat is injective *)
Lemma to_nat_inj {X: Type} {enumX: Enumerable X} {x y: X}: 
  to_nat x = to_nat y <-> x = y.
Proof.
  constructor; last by move->.
  move /(f_equal of_nat). by rewrite ?enumP.
Qed.

Lemma enumerableI {X Y: Type} {enum: Enumerable X} (to_X: Y -> X) (of_X: X -> Y) : 
  (forall (y: Y), of_X (to_X y) = y) -> Enumerable Y.
Proof.
  move=> cancel. exists (fun y => to_nat (to_X y)) (fun x => of_X (of_nat x)).
  move=> y. by rewrite enumP cancel.
Qed.

#[export] Instance nat_Enumerable : Enumerable nat.
Proof. by exists id id. Qed.

#[export] Instance bool_Enumerable : Enumerable bool.
Proof.
  exists (fun b => if b then 1 else 0) (fun n => if n is 0 then false else true).
  by case.
Qed.

#[export] Instance nat2_Enumerable : Enumerable (nat * nat).
Proof.
  exists Cantor.to_nat Cantor.of_nat.
  exact: Cantor.cancel_of_to.
Qed.

#[export] Instance prod_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X * Y).
Proof.
  exists 
    (fun '(x, y) => to_nat (to_nat x, to_nat y))
    (fun n => match of_nat n with | (n1, n2) => (of_nat n1, of_nat n2) end).
  move=> [x y]. by rewrite ?enumP.
Qed.

#[export] Instance sum_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X + Y).
Proof.
  exists 
    (fun t => match t with | inl x => to_nat (0, to_nat x) | inr y => to_nat (1, to_nat y) end)
    (fun n => match of_nat n with | (0, n) => inl (of_nat n) | (1, n) => inr (of_nat n) | _ => inl (of_nat n) end).
  by case => ?; rewrite ?enumP.
Qed.
