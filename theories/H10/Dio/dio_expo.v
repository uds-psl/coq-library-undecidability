(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Object-level encoding of exponential *)

Require Import Arith Nat Omega List.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac sums rel_iter binomial gcd.

From Undecidability.H10.Matija 
  Require Import alpha expo_diophantine.

From Undecidability.H10.Dio 
  Require Import dio_logic.

Set Implicit Arguments.

Local Notation power := (mscal mult 1).
Local Notation expo := (mscal mult 1).

Local Notation "phi ↑ k" := (env_lift phi k) (at level 1, format "phi ↑ k", left associativity).
Local Notation "phi ↓"   := (fun n => phi (S n)) (at level 1, format "phi ↓", no associativity).

Theorem dio_rel_alpha a b c : 𝔻P a -> 𝔻P b -> 𝔻P c
                           -> 𝔻R (fun ν => 3 < b ν /\ a ν = alpha_nat (b ν) (c ν)).
Proof.
  intros.
  apply dio_rel_equiv with (1 := fun v => alpha_diophantine (a v) (b v) (c v)).
  unfold alpha_conditions; dio auto.
Defined.

Hint Resolve dio_rel_alpha : dio_rel_db.

Local Fact dio_rel_alpha_example : 𝔻R (fun ν => 3 < ν 1 /\ ν 0 = alpha_nat (ν 1) (ν 2)).
Proof. dio auto. Defined.

(* Eval compute in df_size_Z (proj1_sig dio_rel_alpha_example). *)

Fact dio_rel_alpha_size : df_size_Z (proj1_sig dio_rel_alpha_example) = 6562%Z.
Proof. reflexivity. Qed.

Theorem dio_expr_expo q r : 𝔻P q -> 𝔻P r -> 𝔻P (fun ν => expo (r ν) (q ν)).
Proof.
  intros.
  apply dio_rel_equiv with (1 := fun v => expo_diophantine (v 0) (q v↓) (r v↓)).
  unfold expo_conditions; dio auto. 
Defined.

Hint Resolve dio_expr_expo : dio_expr_db.

Local Fact dio_expr_expo_example : 𝔻P (fun ν => expo (ν 0) (ν 1)).
Proof. dio auto. Defined.

(* Eval compute in df_size_Z (proj1_sig dio_expr_expo_example). *)

Fact dio_expr_expo_size : df_size_Z (proj1_sig dio_expr_expo_example) = 22878%Z.
Proof. reflexivity. Qed.

Section df_digit.

  Let is_digit_eq c q i y : is_digit c q i y 
                        <-> y < q
                        /\ exists a b p, c = (a*q+y)*p+b 
                                      /\ b < p
                                      /\ p = power i q.
  Proof.
    split; intros (H1 & a & b & H2).
    + split; auto; exists a, b, (power i q); repeat split; tauto.
    + destruct H2 as (p & H2 & H3 & H4).
      split; auto; exists a, b; subst; auto.
  Qed.

  Lemma dio_rel_is_digit c q i y : 𝔻P c -> 𝔻P q -> 𝔻P i -> 𝔻P y
                                -> 𝔻R (fun ν => is_digit (c ν) (q ν) (i ν) (y ν)).
  Proof.
    intros H1 H2 H3 H4.
    apply dio_rel_equiv with (1 := fun ν => is_digit_eq (c ν) (q ν) (i ν) (y ν)).
    dio auto.
  Defined.

End df_digit.

Hint Resolve dio_rel_is_digit : dio_rel_db.

Local Fact dio_rel_is_digit_example : 𝔻R (fun ν => is_digit (ν 0) (ν 1) (ν 2) (ν 3)).
Proof. dio auto. Defined.

Check dio_rel_is_digit_example.
Eval compute in df_size_Z (proj1_sig dio_rel_is_digit_example).

Section df_binomial.

  Notation "∑" := (msum plus 0).

  Let plus_cancel_l : forall a b c, a + b = a + c -> b = c.
  Proof. intros; omega. Qed.

  Hint Resolve Nat.mul_add_distr_r.

  Let is_binomial_eq b n k :  b = binomial n k
                          <-> exists q c, q = power (1+n) 2
                                       /\ c = power n (1+q) 
                                       /\ is_digit c q k b.
  Proof.
    split.
    + intros ?; subst.
      set (q := power (1+n) 2).
      assert (Hq : q <> 0).
      { unfold q; generalize (@power_ge_1 (S n) 2); intros; simpl; omega. }
      set (c := power n (1+q)).
      exists q, c; split; auto.
      split; auto.
      split. 
      * apply binomial_lt_power.
      * destruct (le_lt_dec k n) as [ Hk | Hk ].
        - exists (∑ (n-k) (fun i => binomial n (S k+i) * power i q)),
                 (∑ k (fun i => binomial n i * power i q)); split; auto.
          2: { apply sum_power_lt; auto; intros; apply binomial_lt_power. }
          rewrite Nat.mul_add_distr_r, <- mult_assoc, <- power_S.
          rewrite <- sum_0n_distr_r with (1 := Nat_plus_monoid) (3 := Nat_mult_monoid); auto.
          rewrite <- plus_assoc, (plus_comm _ (∑ _ _)).
          rewrite <- msum_plus1 with (f := fun i => binomial n i * power i q); auto.
          rewrite plus_comm.
          unfold c.
          rewrite Newton_nat_S.
          replace (S n) with (S k + (n-k)) by omega.
          rewrite msum_plus; auto; f_equal; apply msum_ext.
          intros; rewrite power_plus; ring.
        - exists 0, c.
          rewrite binomial_gt; auto.
          rewrite Nat.mul_0_l; split; auto.
          unfold c.
          apply lt_le_trans with (power (S n) q).
          ++ rewrite Newton_nat_S.
             apply sum_power_lt; auto.
             intros; apply binomial_lt_power.
          ++ apply power_mono; omega.
    + intros (q & c & H1 & H2 & H3).
      assert (Hq : q <> 0).
      { rewrite H1; generalize (@power_ge_1 (S n) 2); intros; simpl; omega. }
      rewrite Newton_nat_S in H2.
      apply is_digit_fun with (1 := H3).
      destruct (le_lt_dec k n) as [ Hk | Hk ].
      * red; split.
        - subst; apply binomial_lt_power.
        - exists (∑ (n-k) (fun i => binomial n (S k+i) * power i q)),
                 (∑ k (fun i => binomial n i * power i q)); split.
          2: {  apply sum_power_lt; auto; intros; subst; apply binomial_lt_power. }
          rewrite Nat.mul_add_distr_r, <- mult_assoc, <- power_S.
          rewrite <- sum_0n_distr_r with (1 := Nat_plus_monoid) (3 := Nat_mult_monoid); auto.
          rewrite <- plus_assoc, (plus_comm _ (∑ _ _)).
          rewrite <- msum_plus1 with (f := fun i => binomial n i * power i q); auto.
          rewrite plus_comm, H2.
          replace (S n) with (S k + (n-k)) by omega.
          rewrite msum_plus; auto; f_equal.
          apply msum_ext.
          intros; rewrite power_plus; ring.
      * rewrite binomial_gt; auto.
        split; try omega. 
        exists 0, c.
        rewrite Nat.mul_0_l; split; auto.
        rewrite H2.
        apply lt_le_trans with (power (S n) q).
        - apply sum_power_lt; auto.
          subst; intros; apply binomial_lt_power.
        - apply power_mono; omega.
  Qed.

  Lemma dio_expr_binomial n k : 𝔻P n -> 𝔻P k -> 𝔻P (fun ν => binomial (n ν) (k ν)).
  Proof.
    intros H2 H3.
    apply dio_rel_equiv with (1 := fun ν => is_binomial_eq (ν 0) (n ν↓) (k ν↓)).
    dio auto.
  Defined.

End df_binomial.

Hint Resolve dio_expr_binomial : dio_expr_db.

Local Fact dio_expr_binomial_example : 𝔻P (fun ν => binomial (ν 0) (ν 1)).
Proof. dio auto. Defined.

Check dio_expr_binomial_example.
Eval compute in df_size_Z (proj1_sig dio_expr_binomial_example).
