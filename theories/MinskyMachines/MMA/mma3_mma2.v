(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Utf8.

From Undecidability.Shared.Libs.DLW 
  Require Import utils gcd prime pos vec subcode sss.

From Undecidability.FRACTRAN
  Require Import prime_seq.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils.

Local Definition combi_235 a b c := 2^a*(3^b*5^c).

#[local] Notation "⦉ x , y , z ⦊ " := (combi_235 x y z) (at level 1, format "⦉ x , y , z ⦊ ").

Section combi_235.

  Local Fact prime_2 : prime 2.     Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_3 : prime 3.     Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_5 : prime 5.     Proof. apply prime_bool_spec; trivial. Qed.

  Hint Resolve prime_2 prime_3 prime_5 : core.

  Local Fact not_divides_2_3 x : ~ divides 2 (3^x).
  Proof.
    intros H.
    apply divides_pow in H; auto.
    now apply prime_divides in H; auto.
  Qed.

  Local Fact not_divides_2_5 x : ~ divides 2 (5^x).
  Proof.
    intros H.
    apply divides_pow in H; auto.
    now apply prime_divides in H; auto.
  Qed.

  Local Fact not_divides_2_35 x y : ~ divides 2 (3^x*5^y).
  Proof.
    intros H.  
    apply prime_div_mult in H as [ H | H ]; auto; revert H.
    + apply not_divides_2_3.
    + apply not_divides_2_5.
  Qed.

  Local Fact not_divides_3_5 x : ~ divides 3 (5^x).
  Proof.
    intros H.
    apply divides_pow in H; auto.
    now apply prime_divides in H; auto.
  Qed.

  Local Fact not_divides_5_1 : ~ divides 5 1.
  Proof. intros []; lia. Qed.

  Hint Resolve not_divides_2_35 not_divides_3_5 not_divides_5_1 : core.

  Fact combi_235_inj a₁ b₁ c₁ a₂ b₂ c₂ : ⦉a₁,b₁,c₁⦊ = ⦉a₂,b₂,c₂⦊ -> a₁ = a₂ /\ b₁ = b₂ /\ c₁ = c₂.
  Proof.
    intros H.
    apply power_factor_uniq in H as (<- & H); try easy; split; trivial.
    apply power_factor_uniq in H as (<- & H); try easy; split; trivial.
    replace (5^c₁) with (5^c₁*1) in H by lia. 
    replace (5^c₂) with (5^c₂*1) in H by lia.
    now apply power_factor_uniq in H as [].
  Qed.

  Fact combi_235_mult2 a b c : 2*⦉a,b,c⦊ = ⦉1+a,b,c⦊ .
  Proof. unfold combi_235; rewrite Nat.pow_succ_r'; ring. Qed.

  Fact combi_235_mult3 a b c : 3*⦉a,b,c⦊ = ⦉a,1+b,c⦊ .
  Proof. unfold combi_235; rewrite Nat.pow_succ_r'; ring. Qed.

  Fact combi_235_mult5 a b c : 5*⦉a,b,c⦊ = ⦉a,b,1+c⦊ .
  Proof. unfold combi_235; rewrite Nat.pow_succ_r'; ring. Qed.

End combi_235.

Check combi_235_inj.

