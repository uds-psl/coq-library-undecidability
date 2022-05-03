Require Import PeanoNat Lia.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : 
  Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof. by rewrite Nat.add_comm /Nat.iter nat_rect_plus. Qed.

Lemma pow_3_mod_2 (n: nat) : 3 ^ n mod 2 = 1.
Proof.
  elim: n; first by (cbv; lia).
  move=> n IH. rewrite Nat.pow_succ_r' Nat.mul_mod ?IH; first by lia.
  by cbv; lia.
Qed.

Lemma pow_5_mod_2 (n: nat) : 5 ^ n mod 2 = 1.
Proof.
  elim: n; first by (cbv; lia).
  move=> n IH. rewrite Nat.pow_succ_r' Nat.mul_mod ?IH; first by lia.
  by cbv; lia.
Qed.

Lemma pow_2_mod_3 (n: nat) : 2 ^ n mod 3 = 1 \/ 2 ^ n mod 3 = 2.
Proof.
  elim: n; first by (cbv; lia).
  move=> n IH. rewrite Nat.pow_succ_r' Nat.mul_mod; first by lia.
  move: IH => [->|->]; cbv; by lia.
Qed.

Lemma pow_5_mod_3 (n: nat) : 5 ^ n mod 3 = 1 \/ 5 ^ n mod 3 = 2.
Proof.
  elim: n; first by (cbv; lia).
  move=> n IH. rewrite Nat.pow_succ_r' Nat.mul_mod; first by lia.
  move: IH => [->|->]; cbv; by lia.
Qed.

Lemma mod_frac_lt {n m: nat} : (S m) mod (n + 1) = 0 -> S m < (S m * (n + 2)) / (n + 1).
Proof.
  have ->: S m * (n + 2) = S m + S m * (n + 1) by lia.
  have := Nat.div_mod_eq (S m) (n + 1).
  rewrite Nat.div_add; lia.
Qed.
