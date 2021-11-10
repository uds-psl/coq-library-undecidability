(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import Lia.
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

Module list_Enumerable.
Opaque Cantor.of_nat Cantor.to_nat.

Fixpoint encode {X: Type} {enumX: Enumerable X} (L: list X) : nat :=
  if L is cons x L then S (Cantor.to_nat (to_nat x, encode L)) else 0.

Fixpoint decode {X: Type} {enumX: Enumerable X} (i: nat) (n: nat) : list X :=
  if i is S i then (if n is S n then
    (let '(x, m) := Cantor.of_nat n in cons (of_nat x) (decode i m)) else nil) else nil.

Lemma decode_encode {X: Type} {enumX: Enumerable X} {L: list X} :
  decode (encode L) (encode L) = L.
Proof.
  suff: forall i, @encode X enumX L <= i -> @decode X enumX i (@encode X enumX L) = L by (apply; lia).
  move=> i. elim: i L.
  - move=> [|? ?] /= ?; [done|lia].
  - move=> i IH [|x L]; first done.
    move=> /= H. rewrite Cantor.cancel_of_to enumP. congr cons. apply: IH.
    have := Cantor.to_nat_non_decreasing (@to_nat X enumX x) (@encode X enumX L). lia.
Qed.
End list_Enumerable.

#[export] Instance list_Enumerable {X: Type} {enumX: Enumerable X} : Enumerable (list X).
Proof.
  exists (@list_Enumerable.encode X enumX) (fun n => @list_Enumerable.decode X enumX n n).
  move=> ?. by apply: list_Enumerable.decode_encode.
Qed.
