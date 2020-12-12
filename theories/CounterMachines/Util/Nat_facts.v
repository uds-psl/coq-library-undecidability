Require Import PeanoNat Lia.

Require Import ssreflect ssrbool ssrfun.

(* duplicates argument *)
Lemma copy {A : Prop} : A -> A * A.
Proof. done. Qed.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  apply : well_founded_ind.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
Qed.
Arguments measure_ind {X}.

Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

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
