Require Import Arith Lia.

Require Import ssreflect ssrbool ssrfun.

Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : 
  Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof. by rewrite Nat.add_comm /Nat.iter nat_rect_plus. Qed.

Lemma mod_frac_lt {n m: nat} : (S m) mod (n + 1) = 0 -> S m < (S m * (n + 2)) / (n + 1).
Proof.
  move /Nat.mod_divide => /(_ ltac:(lia)).
  move /Nat.divide_div_mul_exact => /(_ _ ltac:(lia)) => H.
  have -> : (S m * (n + 2)) = ((1 + (n + 1)) * S m) by lia.
  rewrite H /=. rewrite -(H (n+1)).
  have -> : (n + 1) * S m = S m * (n + 1) by lia.
  rewrite Nat.div_mul; first by lia.
  suff: S m <> S m / (n + 1) + S m by lia.
  move /(f_equal (fun x => (n+1) * x)). 
  rewrite Nat.mul_add_distr_l -(H (n+1)).
  have -> : (n + 1) * S m = S m * (n + 1) by lia.
  rewrite Nat.div_mul; first by lia.
  by lia.
Qed.

Lemma mod_frac_neq {n m: nat} : S m mod (n + 1) = 0 -> (S m * (n + 2)) / (n + 1) <> S m.
Proof. move /mod_frac_lt. by lia. Qed.

Lemma div_mod_pos {n m: nat} : S m / (1 + n) + S m mod (1 + n) <> 0.
Proof.
  move=> ?. 
  have /Nat.div_small_iff : S m / (1 + n) = 0 by lia. move /(_ ltac:(lia)).
  have /Nat.div_exact : S m mod (1 + n) = 0 by lia. move /(_ ltac:(lia)).
  by lia.
Qed.

Lemma divides_frac_diff {m n} : m mod (n + 1) = 0 -> (m * (n + 2) / (n + 1) - m) * (1 + n) = m.
Proof.
  rewrite Nat.mul_sub_distr_r.
  move=> /Nat.div_exact => /(_ ltac:(lia)) ?.
  have -> : m * (n + 2) = ((n+2) * (m / (n + 1))) * (n + 1) by lia.
  by rewrite Nat.div_mul; lia.
Qed.

Lemma div_mul_le m n : n <> 0 -> (m / n) * n <= m.
Proof. move=> ?. have := Nat.div_mod m n ltac:(lia). by lia. Qed.

Lemma transition_le_gt (f: nat -> nat) (x n1 n2: nat): 
  n1 <= n2 -> f n1 <= x -> x < f n2 -> exists n, n < n2 /\ f n <= x /\ x < f (1+n).
Proof.
  move Hk: (n2 - n1) => k. elim: k n1 n2 Hk.
    move=> n1 n2 ? ?. have -> : n1 = n2 by lia. by lia.
  move=> k IH n1 [|n2] ? ?; first by lia.
  have : f n2 <= x \/ x < f n2 by lia. case.
    move=> *. exists n2. by constructor.
  move=> ? ? _. have [n [? ?]] := (IH n1 n2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  exists n. by constructor; [lia |].
Qed.
