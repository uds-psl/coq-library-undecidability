Require Import ssreflect ssrbool ssrfun.
Require Import Psatz.

Definition big_sum (n : nat) : nat := 
  nat_rect (fun _ => nat) 0 (fun i m => m + (S i)) n.

Lemma big_sum_0 {n} : big_sum n = 0 -> n = 0.
Proof.
  case: n => //=. move => n ?. by lia.
Qed.

(* bijection from nat * nat to nat *)
Definition nat2_to_nat (a : nat * nat) : nat :=
  match a with
  | (x, y) => (big_sum (x+y)) + y
  end.

Definition next_nat2 (a : nat * nat) : nat * nat :=
  match a with
  | (0, y) => (S y, 0)
  | (S x, y) => (x, S y)
  end.

(* bijection from nat to nat * nat *)
Definition nat_to_nat2 (n : nat) : nat * nat :=
  Nat.iter n next_nat2 (0, 0).

Lemma add_x_0 {x}: x + 0 = x.
Proof. by lia. Qed.

Lemma add_x_S {x y}: x + (S y) = (S x) + y.
Proof. by lia. Qed.

Lemma add_x_y_0 {x y}: x + y = 0 -> x = 0 /\ y = 0.
Proof. by lia. Qed.


Lemma nat_nat2_cancel : cancel nat2_to_nat nat_to_nat2.
Proof.
  move=> a.
  move Hn: (nat2_to_nat a) => n.
  elim: n a Hn.
    move=> [? ?] /add_x_y_0 [/big_sum_0 ? ?] /=.
    f_equal; by lia.

  move=> n IH [x y]. case: y => [| y] /=. case: x => [| x] //=.
  all: rewrite ? (add_x_0, add_x_S); case.
    rewrite -/(nat2_to_nat (0, x)). by move /IH ->.
  rewrite -/(nat2_to_nat (S x, y)). by move /IH ->.
Qed.


Lemma nat2_nat_cancel : cancel nat_to_nat2 nat2_to_nat.
Proof.
  elim => //=.
  move => n. move : (nat_to_nat2 n) => [+ ?].
  case => /= => [|?]; rewrite ? (add_x_0, add_x_S) => /=; by lia.
Qed.
