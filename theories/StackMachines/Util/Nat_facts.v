Require Import Arith Lia.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : 
  Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof. by rewrite Nat.add_comm /Nat.iter nat_rect_plus. Qed.

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

Lemma div_mul_le m n : (m / n) * n <= m.
Proof. have := Nat.div_mod_eq m n. by lia. Qed.

Lemma transition_le_gt (f: nat -> nat) (x n1 n2: nat): 
  n1 <= n2 -> f n1 <= x -> x < f n2 -> exists n, n < n2 /\ f n <= x /\ x < f (1+n).
Proof.
  move=> H Hfn1 Hfn2. have : n1 < n2.
  { suff : n1 <> n2 by lia. by move=> ?; subst; lia. }
  clear H. elim: n2 Hfn2; first by lia.
  move=> n2 IH ??.
  have [?|?] : f n2 <= x \/ x < f n2 by lia.
  - exists n2 => /=. lia.
  - have ? : n1 <> n2 by (move=> ?; subst; lia).
    have [n ?] := IH ltac:(lia) ltac:(lia).
    exists n. lia.
Qed.
