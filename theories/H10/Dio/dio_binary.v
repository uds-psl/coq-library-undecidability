(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* ** Object-level encoding of bounded universal quantification I *)

Require Import Arith Lia List Bool Setoid.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac gcd prime binomial sums bool_nat rel_iter.

From Undecidability.H10.ArithLibs 
  Require Import luca.

From Undecidability.H10.Matija 
  Require Import cipher.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_expo.

Set Implicit Arguments.

Local Infix "≲" := binary_le (at level 70, no associativity).
Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Local Infix "⇣" := nat_meet (at level 40, left associativity).
Local Infix "⇡" := nat_join (at level 50, left associativity).

(* This the Diophantine encoding of binomial coefficents *)

Section dio_fun_binomial.

  Let plus_cancel_l : forall a b c, a + b = a + c -> b = c.
  Proof. intros; lia. Qed.

  Hint Resolve Nat.mul_add_distr_r : core.

  (* We use this characterization with Newton's devel

      (1+q)^n = ∑ binomial(n,i).q^i   when q > 2^n

    *)

  Let is_binomial_eq b n k :  
         b = binomial n k
     <-> exists q, q = power (1+n) 2
                /\ is_digit (power n (1+q)) q k b.
  Proof.
    split.
    + intros ?; subst.
      set (q := power (1+n) 2).
      assert (Hq : q <> 0).
      { unfold q; generalize (@power_ge_1 (S n) 2); intros; simpl; lia. }
      set (c := power n (1+q)).
      exists q; split; auto; split. 
      * apply binomial_lt_power.
      * fold c.
        destruct (le_lt_dec k n) as [ Hk | Hk ].
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
          replace (S n) with (S k + (n-k)) by lia.
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
          ++ apply power_mono; lia.
    + intros (q & H1 & H3).
      assert (Hq : q <> 0).
      { rewrite H1; generalize (@power_ge_1 (S n) 2); intros; simpl; lia. }
      rewrite Newton_nat_S in H3.
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
          rewrite plus_comm.
          replace (S n) with (S k + (n-k)) by lia.
          rewrite msum_plus; auto; f_equal.
          apply msum_ext.
          intros; rewrite power_plus; ring.
      * rewrite binomial_gt; auto.
        rewrite <- Newton_nat_S.
        split; try lia.
        exists 0, (power n (1+q)); split; auto.
        apply lt_le_trans with (power (S n) q).
        - rewrite Newton_nat_S.
          apply sum_power_lt; auto.
          subst; intros; apply binomial_lt_power.
        - apply power_mono; lia.
  Qed.

  Lemma dio_fun_binomial n k : 𝔻F n -> 𝔻F k -> 𝔻F (fun ν => binomial (n ν) (k ν)).
  Proof.
    dio by lemma (fun ν => is_binomial_eq (ν 0) (n ν⭳) (k ν⭳)).
  Defined.

End dio_fun_binomial.

Hint Resolve dio_fun_binomial : dio_fun_db.

Local Fact dio_fun_binomial_example : 𝔻F (fun ν => binomial (ν 0) (ν 1)).
Proof. dio auto. Defined.

(* Check dio_fun_binomial_example. *)
(* Eval compute in df_size_Z (proj1_sig dio_fun_binomial_example). *)

(* This result comes from Lucas' theorem *)

Theorem binary_le_binomial n m : n ≲ m <-> rem (binomial m n) 2 = 1.
Proof.
  split.
  + induction 1 as [ n | n m H1 H2 IH2 ].
    * rewrite binomial_n0, rem_lt; lia.
    * rewrite lucas_lemma with (1 := prime_2) (2 := div_rem_spec1 m 2) (4 := div_rem_spec1 n 2);
        try (apply div_rem_spec2; lia).
      rewrite mult_comm, <- rem_mult_rem, IH2, Nat.mul_1_r.
      revert H1.
      generalize (rem_2_is_0_or_1 m) (rem_2_is_0_or_1 n).
      intros [ G1 | G1 ] [ G2 | G2 ]; rewrite G1, G2; intros; try lia.
      ++ rewrite binomial_n0, rem_lt; lia.
      ++ rewrite binomial_n0, rem_lt; lia.
      ++ rewrite binomial_n1, rem_lt; lia.
  + induction on n m as IH with measure m.
    destruct (eq_nat_dec m 0) as [ Hm | Hm ].
    * destruct n; try (intros; constructor; fail). 
      subst; rewrite binomial_gt, rem_lt; lia.
    * generalize (div_rem_spec1 m 2) (div_rem_spec1 n 2); intros H1 H2.
      rewrite lucas_lemma with (1 := prime_2) (2 := H1) (4 := H2); auto;
        try (apply div_rem_spec2; lia).
      rewrite rem_2_mult; intros (H3 & H4).
      apply IH in H3; try lia.
      constructor 2; auto.
      revert H4.
      generalize (rem_2_is_0_or_1 m) (rem_2_is_0_or_1 n).
      intros [ G1 | G1 ] [ G2 | G2 ]; rewrite G1, G2; intros; try lia.
      rewrite binomial_gt, rem_lt in H4; lia.
Qed.

Theorem dio_rel_binary_le x y : 𝔻F x -> 𝔻F y -> 𝔻R (fun v => x v ≲ y v).
Proof.
  dio by lemma (fun v => binary_le_binomial (x v) (y v)). 
Defined.

Hint Resolve dio_rel_binary_le : dio_rel_db.

Theorem dio_fun_nat_meet a b : 𝔻F a -> 𝔻F b -> 𝔻F (fun ν => a ν ⇣ b ν).
Proof.
  dio by lemma (fun v => nat_meet_dio (v 0) (a v⭳) (b v⭳)).
Defined.

Hint Resolve dio_fun_nat_meet : dio_fun_db.
