(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Euclidian division and Bezout's identity *)

Require Import List Arith Omega Permutation Extraction.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list gcd
                 prime binomial.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.

Set Implicit Arguments.

Section Informative_CRT.

  Fact divides_is_gcd a b c : divides a b -> is_gcd b c 1 -> is_gcd a c 1.
  Proof.
    intros H1 H2; msplit 2; try apply divides_1.
    intros k H3 H4.
    apply H2; auto.
    apply divides_trans with a; auto.
  Qed.

  Fact rel_prime_mult a b c : is_gcd a c 1 -> is_gcd b c 1 -> is_gcd (a*b) c 1.
  Proof.
    intros H1 H2; msplit 2; try apply divides_1.
    intros k H3 H4.
    apply H2; auto.
    apply is_rel_prime_div with (2 := H3).
    apply is_gcd_sym in H1.
    revert H1; apply divides_is_gcd; auto.
  Qed.

  Fact divides_rem_rem p q a : divides p q -> rem (rem a q) p = rem a p.
  Proof.
    destruct (eq_nat_dec p 0) as [ Hp | Hp ].
    { intros (k & ->); subst; rewrite mult_0_r.
      repeat rewrite rem_0; auto. }
    intros H.
    generalize (div_rem_spec1 a q); intros H1.
    destruct H as (k & ->).
    rewrite H1 at 2.
    rewrite plus_comm.
    apply rem_plus_div; auto.
    do 2 apply divides_mult.
    apply divides_refl.
  Qed.
 
  Fact divides_rem_congr p q a b : divides p q -> rem a q = rem b q -> rem a p = rem b p.
  Proof.
    intros H1 H2.
    rewrite <- (divides_rem_rem a H1),
            <- (divides_rem_rem b H1).
    f_equal; auto.
  Qed.

  Theorem CRT_informative n (m v : vec nat n) : 
              (forall p, vec_pos m p <> 0)
           -> (forall p q, p <> q -> is_gcd (vec_pos m p) (vec_pos m q) 1)
           -> { w | forall p, rem w (vec_pos m p) = rem (vec_pos v p) (vec_pos m p) }.
  Proof.
    (** The case n = 0 is special, induction starts at 1 *)
    destruct n as [ | n ]; [ exists 0; intros p; invert pos p | ].
    revert m v.
    induction n as [ | n IHn ]; intros m v H1 H2.
    + exists (vec_pos v pos0); intros p; invert pos p; auto.
      invert pos p.
    + revert H1 H2. 
      vec split m with m1.
      vec split m with m2.
      vec split v with v1.
      vec split v with v2.
      intros H1 H2.
      generalize (H1 pos0) (H1 pos1) (H2 pos0 pos1); intros Hm1 Hm2 H12; simpl in Hm1, Hm2, H12.
      destruct (@CRT_bin_informative m1 m2 v1 v2) as (w0 & H3 & H4 & _); auto.
      { apply H12; discriminate. }
      destruct (IHn (m1*m2 ## m) (w0 ## v)) as (w & Hw).
      * intros p; invert pos p.
        - assert (0 < m1 * m2); try omega.
          apply Nat.mul_pos_pos; omega.
        - apply H1 with (p := pos_nxt (pos_nxt p)).
      * intros p q; invert pos p; invert pos q; intros H; try (destruct H; auto; fail).
        2: apply is_gcd_sym.
        1,2: 
          apply rel_prime_mult;
          [ apply (H2 pos0 (pos_nxt (pos_nxt _)))
          | apply (H2 pos1 (pos_nxt (pos_nxt _))) ]; discriminate.
        apply (H2 (pos_nxt (pos_nxt _)) (pos_nxt (pos_nxt _))).
        contradict H; apply pos_nxt_inj in H; auto.
      * exists w.
        intros p; repeat invert pos p.
        - rewrite <- H3.
          generalize (Hw pos0); simpl.
          apply divides_rem_congr, divides_mult_r, divides_refl.
        - rewrite <- H4.
          generalize (Hw pos0); simpl.
          apply divides_rem_congr, divides_mult, divides_refl.
        - apply Hw with (p := pos_nxt _).
  Qed.

End Informative_CRT.

Section sequence_of_coprimes.

  Fact divides_n_fact_n n : 0 < n -> divides n (fact n).
  Proof.
    destruct n as [ | n ]; try omega; intros _.
    apply divides_mult_r, divides_refl.
  Qed.

  Fact divides_fact_S n : divides (fact n) (fact (S n)).
  Proof. apply divides_mult, divides_refl. Qed.

  Fact divides_fact n i : 0 < i <= n -> divides i (fact n).
  Proof.
    intros (H1 & H2); revert H2.
    induction 1 as [ | n H2 IH2 ].
    + apply divides_n_fact_n; auto.
    + apply divides_trans with (1 := IH2), divides_fact_S.
  Qed.   

  Theorem seq_of_coprimes n i j : i < j <= n -> is_gcd (1+i*fact n) (1+j*fact n) 1.
  Proof.
    intros (H1 & H2).
    apply no_common_prime_is_coprime; try discriminate.
    intros p Hp H3 H4.
    assert (divides p ((j-i)*fact n)) as H5.
    { replace ((j-i)*fact n) with (1+j*fact n - (1+i*fact n)).
      + apply divides_minus; auto.
      + rewrite Nat.mul_sub_distr_r; omega. }
    assert (~ divides p (fact n)) as H6.
    { intros H6.
      rewrite plus_comm in H3.
      apply divides_plus_inv in H3.
      + apply divides_1_inv, Hp in H3; trivial. 
      + apply divides_mult; trivial. }
    apply prime_div_mult with (1 := Hp) in H5.
    destruct H5 as [ H5 | H5 ]; try tauto.
    apply H6, divides_fact.
    assert (p <> 0) as H7.
    { apply prime_ge_2 in Hp; omega. }
    split; try omega.
    apply divides_le in H5; omega.
  Qed.

End sequence_of_coprimes.

