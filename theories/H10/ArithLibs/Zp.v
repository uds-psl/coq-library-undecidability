(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* * Arithmetic libraries for Matiyasevich's theorems *)
(* ** Modular arithmetic *)

Require Import Arith Lia ZArith List Permutation Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list gcd prime binomial sums php.

From Undecidability.H10.ArithLibs 
  Require Import matrix.

Set Implicit Arguments.

Set Default Proof Using "Type".

Section le_pirr.

  (* a dependent induction principle for le *)
  
  Scheme le_indd := Induction for le Sort Prop.

  Fact le_pirr : forall x y (H1 H2 : x <= y), H1 = H2.
  Proof.
    simpl; intros n ? H1.
    induction H1 as [ | m H1 IH ] using le_indd; intro H2.

    change (le_n n) with (eq_rect _ (fun n0 => n <= n0) (le_n n) _ eq_refl).
    generalize (eq_refl n).
    pattern n at 2 4 6 10, H2. 
    case H2; [intro E | intros m l E].
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
    contradiction (le_Sn_n m); subst; auto.
    
    change (le_S n m H1) with (eq_rect _ (fun n0 => n <= n0) (le_S n m H1) _ eq_refl).
    generalize (eq_refl (S m)).
    pattern (S m) at 1 3 4 6, H2.
    case H2; [intro E | intros p H3 E].
    contradiction (le_Sn_n m); subst; auto.
    injection E; intro; subst.
    rewrite (IH H3).
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
  Qed.

End le_pirr.

Fact lt_pirr x y (H1 H2 : x < y) : H1 = H2.
Proof. apply le_pirr. Qed.

Fact Zring : ring_theory 0%Z 1%Z Zplus Zmult Zminus Z.opp eq.
Proof. exists; intros; ring. Qed.

#[export] Hint Resolve Zring Zplus_monoid Zmult_monoid : core.

Section Z_coprime.

  Open Scope Z_scope.

  Definition Z_pos_or_neg u : { 0 <= u } + { u < 0 }.
  Proof.
    destruct (Ztrichotomy_inf u 0) as [ [|] | ]; try (left; lia); tauto.
  Qed.

  Fact Z_coprime u v : (exists a b, a * Z.of_nat u + b*Z.of_nat v = 1) -> is_gcd u v 1%nat.
  Proof.
    intros (a & b & H).
    destruct (Z_pos_or_neg a) as [ Ha | Ha ];
    destruct (Z_pos_or_neg b) as [ Hb | Hb ].
    + apply bezout_sc with (a:= Z.to_nat a) (b := Z.to_nat b) (m := 0%nat).
      2: left; apply divides_0.
      apply Nat2Z.inj.
      rewrite Nat2Z.inj_add.
      repeat rewrite Nat2Z.inj_mul.
      repeat rewrite Z2Nat.id; auto.
    + apply bezout_sc with (a:= Z.to_nat a) (b := 0%nat) (m := (Z.to_nat (-b)*v)%nat).
      2: right; apply divides_mult, divides_refl.
      apply Nat2Z.inj.
      repeat rewrite Nat2Z.inj_add.
      repeat rewrite Nat2Z.inj_mul.
      repeat rewrite Z2Nat.id; auto; lia.
    + apply bezout_sc with (b:= Z.to_nat b) (a := 0%nat) (m := (Z.to_nat (-a)*u)%nat).
      2: left; apply divides_mult, divides_refl.
      apply Nat2Z.inj.
      repeat rewrite Nat2Z.inj_add.
      repeat rewrite Nat2Z.inj_mul.
      repeat rewrite Z2Nat.id; auto; lia.
    + apply Z.lt_le_incl in Ha.
      apply Z.lt_le_incl in Hb.
      exfalso; revert H.
      generalize (Z.mul_nonpos_nonneg _ _ Ha (Nat2Z.is_nonneg u)).
      generalize (Z.mul_nonpos_nonneg _ _ Hb (Nat2Z.is_nonneg v)).
      intros; lia.
  Qed.

End Z_coprime.

Section Zp.

  Variable (p : nat) (Hp : p <> 0).
 
  Definition Z_Zp := { x | x < p }.

  Implicit Type x y : Z_Zp.

  Fact Zp_inj : forall x y, proj1_sig x = proj1_sig y -> x = y.
  Proof. intros (x & H1) (y & H2); simpl; intros; subst; f_equal; apply lt_pirr. Qed.

  Definition Zp_plus : Z_Zp -> Z_Zp -> Z_Zp.
  Proof using Hp.
    intros (x & Hx) (y & Hy).
    exists (rem (x+y) p).
    apply div_rem_spec2; trivial.
  Defined.

  (* ⊕  ⊗  ∸    ⊞ ⊠ ⊟ *)

  Infix "⊕" := Zp_plus (at level 50, left associativity).
  
  Definition Zp_zero : Z_Zp.
  Proof using Hp.
    exists 0; lia.
  Defined.

  Definition Zp_opp : Z_Zp -> Z_Zp.
  Proof using Hp.
    intros (x & Hx). 
    exists (rem (p - x) p). 
    apply div_rem_spec2; trivial.
  Defined.

  Notation "∸" := Zp_opp.

  Definition Zp_mult : Z_Zp -> Z_Zp -> Z_Zp.
  Proof using Hp.
    intros (x & Hx) (y & Hy).
    exists (rem (x*y) p).
    apply div_rem_spec2; trivial.
  Defined.

  Infix "⊗" := Zp_mult (at level 40, left associativity).

  Definition Zp_one : Z_Zp.
  Proof using Hp.
    exists (rem 1 p); apply div_rem_spec2; trivial.
  Defined.

(*

  Infix "+p" := Zp_plus (at level 50, left associativity).
  Infix "*p" := Zp_mult (at level 40, left associativity).
  Notation "-p" := Zp_opp.

*)

  Notation Zp := Zp_zero.
  Notation Op := Zp_one.

  Fact Zp_plus_zero : forall x, Zp ⊕ x = x.
  Proof.
    intros (x & Hx); apply Zp_inj; simpl.
    apply rem_prop with 0; simpl; auto.
  Qed.

  Fact Zp_plus_comm : forall x y,  x ⊕ y = y ⊕ x.
  Proof.
    intros (x & ?) (y & ?); apply Zp_inj; simpl.
    f_equal; lia.
  Qed.

  Fact Zp_plus_assoc : forall x y z, x ⊕ (y ⊕ z) = x ⊕ y ⊕ z.
  Proof.
    intros (x & ?) (y & ?) (z & ?); apply Zp_inj; simpl.
    rewrite (plus_comm (rem _ _) z), rem_plus_rem, rem_plus_rem.
    f_equal; ring.
  Qed.

  Fact Zp_minus : forall x, x ⊕ ∸ x = Zp.
  Proof.
    intros ([ | x ] & Hx); apply Zp_inj; simpl.
    + rewrite Nat.sub_0_r, rem_diag, rem_lt; auto.
    + rewrite rem_lt with (a := _ - _); try lia.
      replace (S (x+(p - S x))) with p by lia.
      apply rem_diag; auto.
  Qed.

  Fact Zp_mult_one : forall x, Op ⊗ x = x.
  Proof.
    intros (x & ?); apply Zp_inj; simpl proj1_sig.
    destruct p as [ | [ | q ] ].
    + destruct Hp; auto.
    + rewrite rem_diag; simpl; auto.
      rewrite rem_lt; lia.
    + rewrite rem_lt with (a := 1); try lia.
      rewrite Nat.mul_1_l, rem_lt; lia.
  Qed.

  Fact Zp_mult_comm : forall x y, x ⊗ y = y ⊗ x.
  Proof.
    intros (x & ?) (y & ?); apply Zp_inj; simpl.
    f_equal; ring.
  Qed.

  Fact Zp_mult_one_r x : x ⊗ Op = x.
  Proof. rewrite Zp_mult_comm, Zp_mult_one; auto. Qed.

  Fact Zp_mult_assoc : forall x y z, x ⊗ (y ⊗ z) = x ⊗ y ⊗ z.
  Proof.
    intros (x & ?) (y & ?) (z & ?); apply Zp_inj; simpl.
    rewrite (mult_comm (rem _ _) z), rem_mult_rem, rem_mult_rem.
    f_equal; ring.
  Qed.

  Fact Zp_mult_plus_distr_l : forall x y z, x ⊗ (y ⊕ z) = x ⊗ y ⊕ x ⊗ z.
  Proof.
    intros (x & ?) (y & ?) (z & ?); apply Zp_inj; simpl.
    rewrite <- rem_plus, <- rem_scal; f_equal; ring.
  Qed.

  Fact Zp_mult_plus_distr_r x y z : (y ⊕ z) ⊗ x = y ⊗ x ⊕ z ⊗ x.
  Proof. do 3 rewrite (Zp_mult_comm _ x); apply Zp_mult_plus_distr_l. Qed.

  (* Define a ring structureon Zp *)

  Definition Zp_is_ring : @ring_theory _ Zp Op Zp_plus Zp_mult (fun x y => x ⊕ ∸ y) Zp_opp eq.
  Proof.
    exists.
    + apply Zp_plus_zero.
    + apply Zp_plus_comm.
    + apply Zp_plus_assoc.
    + apply Zp_mult_one.
    + apply Zp_mult_comm.
    + apply Zp_mult_assoc.
    + intros; apply Zp_mult_plus_distr_r.
    + auto.
    + apply Zp_minus.
  Qed.

  (* Invertible elements are some which are relatively prime to x *)

  Fact Zp_mult_invert : forall x, is_gcd p (proj1_sig x) 1 -> { i | i ⊗ x = Op }.
  Proof.
    intros  (x & Hx); simpl; intros H.
    destruct (bezout_generalized p x) as (u & v & g & l & H1 & H2 & H3 & _).
    generalize (is_gcd_fun H H2); intro; subst g.
    exists (exist _ (rem v p) (@div_rem_spec2 v p Hp)).
    apply Zp_inj; simpl.
    rewrite mult_comm, <- rem_scal.
    destruct H3 as (k & H3).
    rewrite mult_comm.
    rewrite <- rem_erase with (n := u) (1 := eq_refl).
    rewrite <- rem_erase with (n := k) (r := 1) (1 := eq_refl).
    f_equal.
    rewrite H1,H3; ring.
  Qed.

  Fact Zp_mult_revert : forall x i, i ⊗ x = Op -> is_gcd p (proj1_sig x) 1.
  Proof.
    intros (x & Hx) (i & Hi) H; simpl.
    apply f_equal with (f := @proj1_sig _ _) in H; simpl in H.
    destruct (le_lt_dec p 1) as [ H' | H'].
    + replace p with 1 by lia.
      apply is_gcd_1l.
    + rewrite rem_lt with (a := 1) in H; try lia.
      generalize (div_rem_spec1 (i*x) p).
      rewrite H.
      generalize (div (i*x) p); clear H Hi; intros u Hu.
      apply bezout_sc with 1 i ((1+u)* p).
      * rewrite Hu; ring.
      * left; apply divides_mult, divides_refl.
  Qed.

  Definition Zp_invertible x := exists i, i ⊗ x = Op.

  Fact Zp_invertible_spec x : Zp_invertible x <-> is_gcd p (proj1_sig x) 1.
  Proof.
    split.
    + intros (i & Hi); revert Hi; apply Zp_mult_revert.
    + intros H; destruct (Zp_mult_invert _ H) as (i & ?); exists i; auto.
  Qed.

  Fact Zp_prime_invert : prime p -> forall x, x <> Zp -> { i | i ⊗ x = Op }.
  Proof.
    intros Hp' x Hx.
    apply Zp_mult_invert.
    destruct x; simpl in *.
    destruct (prime_gcd x Hp') as [ | H ]; auto.
    exfalso; apply Hx, Zp_inj; simpl.
    destruct H as ([ | k ] & Hk); simpl in Hk; auto.
    revert Hk; generalize (k* p); intros; lia.
  Qed.

  (* So we have the commutative ring structure and the field structure for p prime 

     These follow form (non-commutative) ring axioms

   *)

  Add Ring Zp_ring : Zp_is_ring.

  Fact Zp_plus_monoid : monoid_theory Zp_plus Zp_zero.
  Proof. exists; intros; ring. Qed.

  Fact Zp_mult_monoid : monoid_theory Zp_mult Zp_one.
  Proof. exists; intros; ring. Qed.

  Fact Zp_one_invertible : Zp_invertible Op.
  Proof. exists Op; ring. Qed.

  Fact Zp_opp_invertible x : Zp_invertible x <-> Zp_invertible (∸ x).
  Proof. split; intros (i & Hi); exists (∸ i); rewrite <- Hi; ring. Qed. 

  Fact Zp_mult_invertible x y : Zp_invertible x -> Zp_invertible y -> Zp_invertible (x ⊗ y).
  Proof. 
    intros (u & H1) (v & H2); exists (u⊗v); rewrite <- (Zp_mult_one Op).
    rewrite <- H1 at 1.
    rewrite <- H2; ring.
  Qed.

  Hint Resolve Zp_one_invertible Zp_opp_invertible Zp_mult_invertible : core.

  Fact Zp_expo_invertible n x : Zp_invertible x -> Zp_invertible (mscal Zp_mult Op n x).
  Proof. intros; induction n; [ rewrite mscal_0 | rewrite mscal_S ]; auto. Qed.

  Fact Zp_invertible_cancel_l x y z : Zp_invertible x -> x⊗y = x⊗z -> y = z.
  Proof. 
    intros (i & Hi) H.
    rewrite <- (Zp_mult_one y), <- Hi, <- Zp_mult_assoc,
            H, Zp_mult_assoc, Hi, Zp_mult_one; auto.
  Qed.

  (* ⊕  ⊗  ∸ *)

  Fact Zp_opp_zero : ∸ Zp = Zp.
  Proof. ring. Qed.

  Fact Zp_plus_inj_l x y z : x ⊕ y = x ⊕ z -> y = z.
  Proof.
    intros H.
    apply f_equal with (f := fun a => ∸ x ⊕ a) in H.
    do 2 rewrite Zp_plus_assoc in H.
    rewrite (Zp_plus_comm _ x), Zp_minus in H.
    do 2 rewrite Zp_plus_zero in H; auto.
  Qed.

  Fact Zp_plus_zero_r x : x ⊕ Zp = x.
  Proof. ring. Qed.

  Fact Zp_opp_inv x : ∸ (∸ x) = x.
  Proof. ring. Qed.

  Fact Zp_opp_inj x y : ∸ x = ∸ y -> x = y.
  Proof. intros H; rewrite <- (Zp_opp_inv x), H; ring. Qed.

  Fact Zp_opp_plus x y : ∸ (x ⊕ y) = ∸ x ⊕ ∸ y.
  Proof. ring. Qed.
 
  Fact Zp_opp_plus_eq x y z : x ⊕ y = z <-> x = z ⊕ ∸ y.
  Proof. split; intros; subst; ring. Qed.

  Fact Zp_mult_zero x : Zp ⊗ x = Zp.
  Proof. ring. Qed.

  Fact Zp_mult_minus_one x : (∸ Op) ⊗ x = ∸ x.
  Proof. ring. Qed.

  Fact Zp_opp_mult x y : (∸ x) ⊗ y = ∸ (x ⊗ y).
  Proof. ring. Qed.

  Fact Zp_invertible_eq_zero x y : Zp_invertible x -> x ⊗ y = Zp -> y = Zp.
  Proof.
    intros (i & Hi) H1.
    rewrite <- (Zp_mult_one y), <- Hi at 1.
    rewrite <- Zp_mult_assoc, H1; ring.
  Qed.

  Fact Zp_zero_is_one : Zp = Op <-> p = 1.
  Proof.
    split.
    + intros H; apply f_equal with (f := @proj1_sig _ _) in H; simpl in H.
      symmetry in H.
      apply divides_rem_eq, divides_1_inv in H; auto.
    + intros; apply Zp_inj; simpl; subst; rewrite rem_diag; auto.
  Qed.

  Fact Zp_eq_dec : forall x y : Z_Zp, { x = y } + { x <> y }.
  Proof.
    intros (x & Hx) (y & Hy).
    destruct (eq_nat_dec x y) as [ | H ].
    + left; apply Zp_inj; auto.
    + right; contradict H.
      apply f_equal with (f := @proj1_sig _ _) in H; auto.
  Qed.

  (* We define a morphism for nat to Z_Zp *)

  Section nat2Zp.

    Definition nat2Zp (u : nat) : Z_Zp.
    Proof using Hp.
      exists (rem u p); apply div_rem_spec2; trivial.
    Defined.

    Arguments nat2Zp u /.

    Notation "〚 x 〛" := (nat2Zp x).

    Fact nat2Zp_zero : 〚0〛= Zp.
    Proof. 
      apply Zp_inj; simpl.
      apply rem_prop with 0; lia.
    Qed.

    Fact nat2Zp_one : 〚1〛= Op.
    Proof.
      apply Zp_inj; simpl; auto.
    Qed.

    Fact nat2Zp_invertible n : Zp_invertible 〚n〛 <-> is_gcd p n 1.
    Proof.
      rewrite Zp_invertible_spec.
      symmetry; apply is_gcd_rem.
    Qed.

    Fact nat2Zp_p :〚p〛= Zp.
    Proof.
      apply Zp_inj; simpl.
      apply rem_diag; lia.
    Qed.

    Fact nat2Zp_inj u v : 〚u〛=〚v〛 <-> rem u p = rem v p.
    Proof.
      split; intros H.
      + apply f_equal with (f := @proj1_sig _ _) in H; auto.
      + apply Zp_inj; auto.
    Qed.

    Fact nat2Zp_surj u : { x | x < p /\ u = 〚x〛 }.
    Proof.
      destruct u as (u & Hu); exists u; split; auto.
      apply Zp_inj; simpl.
      rewrite rem_prop with (n := 0) (2 := Hu); auto.
    Qed.

    Fact nat2Zp_plus u v : 〚u+v〛=〚u〛⊕〚v〛.
    Proof.
      apply Zp_inj; simpl.
      rewrite rem_plus_rem, (plus_comm (rem _ _)), rem_plus_rem.
      f_equal; ring.
    Qed.

    Fact nat2Zp_minus u v : v <= u -> 〚u-v〛=〚u〛⊕ ∸〚v〛.
    Proof.
      intros; apply Zp_inj; simpl.
      rewrite rem_plus_rem, (plus_comm (rem _ _)), plus_comm.
      generalize (div u p) (div v p) (div_rem_spec1 u p) (div_rem_spec1 v p).
      intros a b H1 H2.
      assert (b <= a) as Hab.
      { destruct (le_lt_dec b a); auto.
        replace b with ((1+a) + (b-a-1)) in H2 by lia.
        generalize (div_rem_spec2 u Hp) (div_rem_spec2 v Hp); intros H3 H4.
        do 2 rewrite Nat.mul_add_distr_r in H2.
        contradict H; rewrite H1, H2, Nat.mul_1_l.
        generalize (a* p) ((b-a-1)* p); intros; lia. }
      destruct (eq_nat_dec a b) as [ | Ha ]; try subst b.
      + assert (rem v p <= rem u p) as H3.
        { rewrite H1, H2 in H; revert H; intros; lia. }
        symmetry; apply rem_erase with 1.
        rewrite H1 at 2.
        rewrite H2 at 2.
        generalize (a* p) (div_rem_spec2 v Hp); intros; lia.
      + apply rem_erase with (a-b-1).
        rewrite H2 at 1; rewrite H1 at 1.
        do 2 rewrite Nat.mul_sub_distr_r.
        rewrite Nat.mul_1_l.
        assert (b* p + p <= a* p) as E.
        { replace a with (1+b+(a-b-1)) by lia.
          do 2 rewrite Nat.mul_add_distr_r.
          generalize (b* p) ((a-b-1)* p); intros; lia. } 
        revert E.
        generalize (a* p) (b* p) (div_rem_spec2 u Hp) (div_rem_spec2 v Hp); intros.
        lia.
    Qed.

    Fact nat2Zp_minus_one : 〚p-1〛= ∸Op.
    Proof.
      rewrite nat2Zp_minus; try lia.
      rewrite nat2Zp_p, nat2Zp_one; ring.
    Qed.

    Fact nat2Zp_mult u v :〚u*v〛=〚u〛⊗〚v〛.
    Proof.
      apply Zp_inj; simpl.
      rewrite rem_mult_rem, (mult_comm (rem _ _)), rem_mult_rem.
      f_equal; ring.
    Qed.

    Fact nat2Zp_expo n u : 〚mscal mult 1%nat n u〛 = mscal Zp_mult Zp_one n 〚u〛.
    Proof.
      induction n as [ | n IHn ].
      + do 2 rewrite mscal_0; auto.
      + do 2 rewrite mscal_S.
        rewrite nat2Zp_mult, IHn; auto.
    Qed.

    Fact nat2Zp_divides u v :〚u〛=〚v〛-> divides p u -> divides p v.
    Proof.
      intros H.
      apply f_equal with (f := @proj1_sig _ _) in H; simpl in H.
      do 2 (rewrite divides_rem_eq; auto); lia.
    Qed.

    Fact divides_nat2Zp u : divides p u <-> 〚u〛= Zp.
    Proof.
      split.
      + intros (q & Hq); apply Zp_inj; simpl.
        apply rem_prop with q; lia.
      + intros H.
        apply f_equal with (f := @proj1_sig _ _) in H; simpl in H.
        exists (div u p).
        rewrite (div_rem_spec1 u p) at 1; lia.
    Qed.

  End nat2Zp.

  Arguments nat2Zp u /.

  Definition Zp_list := map nat2Zp (list_an 0 p).
  
  Fact Zp_list_spec x : In x Zp_list.
  Proof.
    destruct (nat2Zp_surj x) as (n & H1 & H2); subst.
    apply in_map_iff; exists n; split; auto.
    apply list_an_spec; lia.
  Qed.

  Fact Zp_list_length : length Zp_list = p.
  Proof. unfold Zp_list; rewrite map_length, list_an_length; auto. Qed.

  Fact Zp_invertible_prime x : prime p -> Zp_invertible x <-> x <> Zp.
  Proof.
    intros H.
    split.
    + intros (i & Hi) E.
      subst.
      rewrite Zp_mult_comm, Zp_mult_zero, Zp_zero_is_one in Hi.
      apply prime_ge_2 in H; lia.
    + intros Hx.
      destruct (nat2Zp_surj x) as (u & _ & Hu).
      rewrite Hu; apply nat2Zp_invertible.
      destruct (prime_gcd u H) as [ H1 | H1 ]; auto.
      destruct Hx.
      rewrite Hu; apply divides_nat2Zp; auto.
  Qed.
 
  Fact Zp_prime_integral x y : prime p -> x ⊗ y = Zp -> x = Zp \/ y = Zp.
  Proof.
    intros H1 H2.
    destruct (Zp_eq_dec x Zp) as [ | H ]; auto; right.
    revert H2; apply Zp_invertible_eq_zero, Zp_invertible_prime; auto.
  Qed.

  Fact Zp_prime_square_eq_square x y : prime p -> x⊗x = y⊗y <-> x = y \/ x = ∸y.
  Proof.
    intros H1; split.
    + intros H2.
      assert ((x⊕∸y)⊗(x⊕y) = Zp) as H3.
      { rewrite Zp_mult_plus_distr_l, Zp_mult_plus_distr_r, H2; ring. }
      apply Zp_prime_integral in H3; auto.
      destruct H3 as [ H3 | H3 ]; [ left | right ]; 
        rewrite Zp_opp_plus_eq in H3; rewrite H3; ring.
    + intros [ | ]; subst x; ring.
  Qed.

  Fact Zp_prime_square_one x : prime p -> x⊗x = Op <-> x = Op \/ x = ∸Op.
  Proof.
    rewrite <- (Zp_mult_one Op) at 1.
    apply Zp_prime_square_eq_square.
  Qed.

  (* We define a morphism for Z to Z_Zp *)

  Section Z2Zp.

    Open Scope Z_scope.

    Implicit Types u v w : Z.

    Definition Z2Zp u : Z_Zp.
    Proof using Hp.
      destruct (Z_pos_or_neg u) as [ H | H ].
      + apply nat2Zp, Z.to_nat; exact u.
      + apply Zp_opp, nat2Zp, Z.to_nat; exact (-u).
    Defined.

    Arguments Z2Zp u /.

    Notation "〘 x 〙" := (Z2Zp x).
    Notation "〚 x 〛" := (nat2Zp x).

    Fact Z2Zp_pos u : 0 <= u -> 〘u〙= 〚Z.to_nat u〛.
    Proof.
      intros H.
      unfold Z2Zp.
      destruct (Z_pos_or_neg u); try lia; auto.
    Qed.

    Fact Z2Zp_of_nat n : 〘Z.of_nat n〙 = 〚n〛.
    Proof.
      rewrite Z2Zp_pos, Nat2Z.id; auto.
      apply Zle_0_nat.
    Qed.

    Fact Z2Zp_zero : 〘0〙= Zp.
    Proof.
      rewrite Z2Zp_pos; try lia.
      rewrite Z2Nat.inj_0, nat2Zp_zero; auto.
    Qed.

    Fact Z2Zp_neg u : u <= 0 -> 〘u〙 = ∸〘-u〙.
    Proof.
      intros H.
      unfold Z2Zp at 1.
      destruct (Z_pos_or_neg u) as [ H' | H' ]; try lia; auto.
      replace u with 0 by lia.
      rewrite Z.opp_0, Z2Nat.inj_0, nat2Zp_zero, Z2Zp_zero; auto.
      symmetry; apply Zp_opp_zero.
      unfold Z2Zp.
      destruct (Z_pos_or_neg (-u)) as [ H'' | H'' ]; try lia; auto.
    Qed.

    (* ⊕  ⊗  ∸ *)

    Section Z2Zp_plus.

      Let Z2Zp_plus_loc u v : u <= 0 -> 0 <= v -> -u <= v -> 〘u+v〙=〘u〙⊕〘v〙.
      Proof.
        intros H1 H2 H3.
        rewrite Z2Zp_pos; try lia.
        rewrite Z2Zp_neg; try lia.
        do 2 (rewrite Z2Zp_pos; try lia).
        replace (u+v) with (v-(-u)) by lia.
        rewrite Z2Nat.inj_sub; try lia.
        rewrite nat2Zp_minus.
        + apply Zp_plus_comm.
        + rewrite <- Z2Nat.inj_le; lia.
      Qed.

      Let Z2Zp_plus_loc' u v : u <= 0 -> 0 <= v -> v <= -u -> 〘u+v〙=〘u〙⊕〘v〙.
      Proof.
        intros H1 H2 H3.
        rewrite Z2Zp_neg; try lia.
        rewrite Z2Zp_pos; try lia.
        rewrite Z2Zp_neg; try lia.
        do 2 (rewrite Z2Zp_pos; try lia).
        replace (-(u+v)) with (-u-v) by lia.
        rewrite Z2Nat.inj_sub; try lia.
        rewrite nat2Zp_minus; auto.
        + rewrite Zp_opp_plus, Zp_opp_inv; auto.
        + rewrite <- Z2Nat.inj_le; lia.
      Qed.

      Fact Z2Zp_plus u v : 〘u+v〙=〘u〙⊕〘v〙.
      Proof.
        destruct (Z_pos_or_neg u) as [ H1 | H1 ];
        destruct (Z_pos_or_neg v) as [ H2 | H2 ].
        + do 3 (rewrite Z2Zp_pos; try lia).
          rewrite Z2Nat.inj_add; auto.
          apply nat2Zp_plus.
        + rewrite Z.add_comm, Zp_plus_comm.
          destruct (Z_pos_or_neg (u+v)).
          - apply Z2Zp_plus_loc; lia.
          - apply Z2Zp_plus_loc'; lia.
        + destruct (Z_pos_or_neg (u+v)).
          - apply Z2Zp_plus_loc; lia.
          - apply Z2Zp_plus_loc'; lia.
        + do 3 (rewrite Z2Zp_neg, Z2Zp_pos; try lia).
          rewrite <- Zp_opp_plus; f_equal.
          replace (-(u+v)) with ((-u)+(-v)) by lia.
          rewrite Z2Nat.inj_add; try lia.
          apply nat2Zp_plus.
      Qed.

    End Z2Zp_plus.

    Fact Z2Zp_opp u :〘-u〙= ∸〘u〙.
    Proof.
      apply Zp_plus_inj_l with (Z2Zp u).
      rewrite Zp_minus, <- Z2Zp_plus, <- Z2Zp_zero.
      f_equal; lia.
    Qed.

    Fact Z2Zp_minus u v : 〘u-v〙 = 〘u〙⊕ ∸〘v〙.
    Proof.
      replace (u-v) with (u+(-v)) by lia.
      rewrite Z2Zp_plus; f_equal.
      apply Z2Zp_opp.
    Qed.
   
    Section Z2Zp_canon.

      (* Find a representative in the A interval [0,Z.of_nat p[ *) 

      Let Z2Zp_canon_pos u : 0 <= u -> { v | 〘u〙=〘v〙 /\ 0 <= v < Z.of_nat p }.
      Proof.
        intros H1. 
        rewrite Z2Zp_pos; auto.
        exists (Z.of_nat (rem (Z.to_nat u) p)); split.
        rewrite Z2Zp_of_nat.
        apply nat2Zp_inj.
        rewrite rem_rem; auto.
        split.
        * apply Zle_0_nat.
        * apply inj_lt, div_rem_spec2; auto.
      Qed.

      Let Z2Zp_canon_neg u : u <= 0 -> { v | 〘u〙=〘v〙 /\ 0 <= v < Z.of_nat p }.
      Proof.
        intros H1.
        rewrite Z2Zp_neg; try lia.
        rewrite Z2Zp_opp, Zp_opp_inv.
        destruct (Zp_eq_dec (Z2Zp u) Zp_zero) as [ E | D ].
        + exists 0; split.
          * rewrite E, Z2Zp_zero; auto.
          * split; lia.
        + destruct Z2Zp_canon_pos with (u := -u)
          as (v & H2 & H3); try lia.
          exists (Z.of_nat p - v); split.
          * rewrite Z2Zp_minus, Z2Zp_of_nat, nat2Zp_p, <- H2, Z2Zp_opp; ring.
          * split; try lia.
            destruct (Z.eq_dec v 0) as [ E | ]; try lia.
            subst; destruct D.
            rewrite Z2Zp_opp in H2.
            rewrite <- (Zp_opp_inv 〘 _ 〙), H2, Z2Zp_zero; ring.
      Qed.
 
      Fact Z2Zp_repr_canon u : { v |〘u〙=〘v〙 /\ 0 <= v < Z.of_nat p }.
      Proof.
        destruct (Z_pos_or_neg u); auto.
        apply Z2Zp_canon_neg; lia.
      Qed.

    End Z2Zp_canon.

    Fact Zp_repr_interval a b u :
            Z.of_nat p <= b-a -> { v |〘u〙=〘v〙/\ a <= v < b }.
    Proof.
      intros Hab.
      destruct (Z2Zp_repr_canon (u-a)) as (v & H1 & H2).
      exists (a+v)%Z; split; try lia.
      rewrite Z2Zp_plus, <- H1, Z2Zp_minus; ring.
    Qed.

    Section Z2Zp_mult.
  
      Let Z2Zp_mult_loc u v : 0 <= u -> 0 <= v -> 〘u*v〙=〘u〙⊗〘v〙.
      Proof.
        intros H1 H2.
        rewrite Z2Zp_pos; try lia.
        do 2 (rewrite Z2Zp_pos; try lia).
        rewrite Z2Nat.inj_mul; auto.
        apply nat2Zp_mult.
      Qed.

      Fact Z2Zp_mult u v : 〘u*v〙=〘u〙⊗〘v〙.
      Proof.
        destruct (Z_pos_or_neg u) as [ H1 | H1 ];
        destruct (Z_pos_or_neg v) as [ H2 | H2 ].
        + apply Z2Zp_mult_loc; auto.
        + replace (u*v) with (-(u*-v)); try ring.
          rewrite Z2Zp_opp, Z2Zp_mult_loc; try lia.
          rewrite Z2Zp_opp, Zp_mult_comm, Zp_opp_mult, Zp_opp_inv.
          apply Zp_mult_comm.
        + replace (u*v) with (- ((-u)*v)); try ring.
          rewrite Z2Zp_opp, Z2Zp_mult_loc; try lia.
          rewrite Z2Zp_opp, Zp_opp_mult, Zp_opp_inv; auto.
        + replace (u*v) with ((-u)*(-v)); try ring.
          rewrite Z2Zp_mult_loc; try lia.
          do 2 rewrite Z2Zp_opp.
          do 2 rewrite Zp_opp_mult, Zp_mult_comm.
          apply Zp_opp_inv.
      Qed.

    End Z2Zp_mult.

    Fact Z2Zp_one : 〘1〙 = Op.
    Proof.
      rewrite Z2Zp_pos; try lia.
      apply Zp_inj; simpl; f_equal; auto.
    Qed.

    Section Z2Zp_inj.

      Let Z2Zp_inj_loc u v : v <= u ->〘u〙=〘v〙-> exists i, u-v = i*Z.of_nat p.
      Proof.
        intros H2 H.
        assert (〘u-v〙= Zp) as H1.
        { rewrite Z2Zp_minus, H; ring. }
        rewrite Z2Zp_pos in H1; auto; try lia.
        rewrite <- nat2Zp_zero in H1.
        apply nat2Zp_inj in H1.
        rewrite rem_of_0 in H1.
        generalize (@div_rem_spec1 (Z.to_nat (u-v)) p); intros H3.
        rewrite H1 in H3.
        apply f_equal with (f := Z.of_nat) in H3.
        rewrite Z2Nat.id in H3; auto; try lia.
        rewrite H3.
        exists (Z.of_nat (div (Z.to_nat (u-v)) p)).
        rewrite Nat2Z.inj_add, Nat2Z.inj_mul; simpl; ring.
      Qed.
      
      Fact Z2Zp_inj u v :〘u〙=〘v〙<-> exists i, u-v = i*Z.of_nat p.
      Proof.
        split.
        + destruct (Z_pos_or_neg (u-v)) as [ H | H ].
          * apply Z2Zp_inj_loc; lia. 
          * intros H'; symmetry in H'.
            apply Z2Zp_inj_loc in H'; try lia.
            destruct H' as (i & Hi).
            exists (-i).
            apply f_equal with (f := Z.opp) in Hi.
            ring_simplify in Hi.
            rewrite <- Hi; ring.
        + intros (i & Hi).
          replace u with (v+(u-v)) by lia.
          rewrite Hi, Z2Zp_plus, Z2Zp_mult, Z2Zp_of_nat, nat2Zp_p; ring.
      Qed.

    End Z2Zp_inj.

    Fact Z2Zp_zero_inv u : 
          〘u〙= Zp_zero 
        -> exists v, (u = Z.of_nat p * v)%Z.
    Proof.
      intros H.
      rewrite <- Z2Zp_zero in H.
      apply Z2Zp_inj in H.
      destruct H as (y & Hy); exists y.
      rewrite Zmult_comm, <- Hy; ring.
    Qed.

    Fact nat2Zp_choose : forall x, x = Zp \/ x = Op \/ x = ∸ Op \/ exists m,  (1 < m < p-1)%nat /\〚m〛= x.
    Proof.
      intros (x & Hx).
      destruct x as [ | [ | x ] ].
      + left; apply Zp_inj; simpl; auto.
      + right; left; apply Zp_inj; simpl; rewrite rem_lt; auto.
      + destruct (eq_nat_dec (S (S x)) (p-1)) as [ H | H ].
        * do 2 right; left.
          rewrite <- nat2Zp_minus_one.
          apply Zp_inj; simpl; rewrite rem_lt; lia.
        * do 3 right; exists (S (S x)); split; try lia.
          apply Zp_inj; simpl; rewrite rem_lt; lia.
    Qed.

    Section prime.

      Hypothesis Hp' : prime p.

      Fact nat2Zp_invertible_prime n : (0 < n < p)%nat -> Zp_invertible 〚n〛.
      Proof using Hp'.
        intros Hn.
        apply Zp_invertible_prime; auto.
        intros H.
        apply divides_nat2Zp in H.
        destruct H as ([ | k ] & Hk).
        + simpl in Hk; lia.
        + revert Hn; rewrite Hk; simpl. 
          generalize (k*p)%nat; intros; lia.
      Qed.

      Let Hp'' : (2 <= p)%nat.
      Proof. apply prime_ge_2; trivial. Qed.

      Let Hzero_one : Zp <> Op.
      Proof.
        intros H.
        apply Zp_zero_is_one in H.
        lia.
      Qed.

      Fact Zp_invertible_factorial n : (n < p)%nat -> Zp_invertible 〚fact n〛.
      Proof using Hp'.
        induction n as [ | n IHn ]; intros Hn.
        + rewrite fact_0; apply nat2Zp_invertible_prime; lia.
        + rewrite fact_S, nat2Zp_mult; apply Zp_mult_invertible.
          * apply nat2Zp_invertible_prime; lia.
          * apply IHn; lia.
      Qed.

      Section inv.

        Let Zp_invert_full x : { i | (x = Zp -> i = Zp) /\ (x <> Zp -> i ⊗ x = Op) }.
        Proof.
          destruct (Zp_eq_dec x Zp) as [ Hx | Hx ].
          + exists Zp; split; auto; intros []; auto.
          + destruct Zp_prime_invert with (2 := Hx) as (i & Hi); trivial.
            exists i; split; auto; intros; destruct Hx; auto.
        Qed.

        Definition Zp_invert x := proj1_sig (Zp_invert_full x).

        Fact Zp_invert_spec1 : Zp_invert Zp = Zp.
        Proof. apply (proj2_sig (Zp_invert_full Zp)); trivial. Qed.

        Fact Zp_invert_spec2 x : x <> Zp -> Zp_invert x ⊗ x = Op.
        Proof. apply (proj2_sig (Zp_invert_full x)). Qed.

      End inv.

      Notation inv := Zp_invert.

      Fact Zp_invert_eq_not_zero x y : x <> Zp -> inv x = y <-> y ⊗ x = Op.
      Proof.
        intros H1.
        split.
        + intros H2; rewrite <- H2; apply Zp_invert_spec2; auto.
        + intros H2.
          apply Zp_invert_spec2 in H1.
          rewrite <- (Zp_mult_one (inv x)) , <- H2, <- Zp_mult_assoc,
                    (Zp_mult_comm x), H1, Zp_mult_comm, Zp_mult_one.
          trivial.
      Qed.

      Fact Zp_invert_opp x : inv (∸x) = ∸(inv x).
      Proof.
        destruct (Zp_eq_dec x Zp) as [ Hx | Hx ]. 
        + subst; rewrite Zp_opp_zero, Zp_invert_spec1, Zp_opp_zero; auto.
        + apply Zp_invert_eq_not_zero.
          * contradict Hx.
            rewrite <- (Zp_opp_inv x), Hx, Zp_opp_zero; trivial.
          * do 2 rewrite Zp_opp_mult, Zp_mult_comm.
            rewrite Zp_opp_inv, Zp_invert_spec2; auto.
      Qed.

      Fact Zp_invert_one : inv Op = Op.
      Proof. 
        rewrite Zp_invert_eq_not_zero; auto.
        rewrite Zp_mult_one; auto.
      Qed.
  
      Fact Zp_invert_minus_one : inv (∸ Op) = ∸ Op.
      Proof. rewrite Zp_invert_opp, Zp_invert_one; auto. Qed.

      Fact Zp_invert_fix x : inv x = x <-> x = Zp \/ x = Op \/ x = ∸ Op.
      Proof.
        split.
        + intros H.
          destruct (Zp_eq_dec x Zp) as [ Hx | Hx ]; auto.
          apply Zp_invert_spec2 in Hx.
          rewrite H in Hx.
          apply Zp_prime_square_one in Hx; auto.
        + intros [ | [|]]; subst.
          * apply Zp_invert_spec1.
          * apply Zp_invert_eq_not_zero; try ring.
            intros H; symmetry in H; revert H; rewrite Zp_zero_is_one; lia.
          * apply Zp_invert_eq_not_zero; try ring.
            intros H.
            rewrite <- Zp_opp_zero in H.
            symmetry in H; apply Zp_opp_inj in H.
            revert H; rewrite Zp_zero_is_one; lia.
      Qed.

      Fact Zp_invert_involutive x : inv (inv x) = x.
      Proof.
        destruct (Zp_eq_dec x Zp) as [ Hx | Hx ]; subst.
        + do 2 rewrite Zp_invert_spec1; auto.
        + apply Zp_invert_eq_not_zero.
          * intros H.
            apply Zp_invert_spec2 in Hx.
            rewrite H, Zp_mult_zero in Hx.
            apply Zp_zero_is_one in Hx; lia.
          * rewrite Zp_mult_comm; apply Zp_invert_spec2; auto.
      Qed.

      Fact Zp_invert_not_fix n : (1 < n < p-1)%nat -> inv〚n〛<>〚n〛.
      Proof.  
        intros H1 H2.
        apply Zp_invert_fix in H2.
        destruct H2 as [ H2 | [ H2 | H2 ] ].
        + rewrite <- nat2Zp_zero in H2.
          apply nat2Zp_inj in H2.
          rewrite rem_lt, rem_lt in H2; lia.
        + rewrite <- nat2Zp_one in H2.
          apply nat2Zp_inj in H2.
          rewrite rem_lt, rem_lt in H2; lia.
        + rewrite <- nat2Zp_minus_one in H2.
          apply nat2Zp_inj in H2.
          rewrite rem_lt, rem_lt in H2; lia.
      Qed.

      Fact Zp_invert_stable n : (1 < n < p-1)%nat -> exists m, (1 < m < p-1)%nat /\〚m〛= inv〚n〛.
      Proof.
        intros Hn.
        destruct (nat2Zp_choose (inv 〚n〛)) as [ H | [ H | [ H | H ] ] ]; auto; 
          exfalso; apply f_equal with (f := inv) in H; 
          rewrite Zp_invert_involutive in H; symmetry in H.
        + rewrite Zp_invert_spec1 in H.
          rewrite <- nat2Zp_zero, nat2Zp_inj in H.
          rewrite rem_lt, rem_lt in H; lia.
        + rewrite Zp_invert_one, <- nat2Zp_one in H.
          rewrite nat2Zp_inj, rem_lt, rem_lt in H; lia.
        + rewrite Zp_invert_minus_one, <- nat2Zp_minus_one in H.
          rewrite nat2Zp_inj, rem_lt, rem_lt in H; lia.
      Qed.

      Definition Zp_lprod := fold_right Zp_mult Zp_one.

      Fact Zp_lprod_nil : Zp_lprod nil = Op.
      Proof. trivial. Qed.

      Fact Zp_lprod_cons x l : Zp_lprod (x::l) = x ⊗ Zp_lprod l.
      Proof. trivial. Qed.
   
      Fact Zp_lprod_app l m : Zp_lprod (l++m) = Zp_lprod l ⊗  Zp_lprod m.
      Proof.
        induction l as [ | x l IHl ].
        + rewrite Zp_lprod_nil, Zp_mult_one; auto.
        + simpl app; do 2 rewrite Zp_lprod_cons.
          rewrite IHl; ring.
      Qed.

      Theorem Zp_mult_autoinv l : ~ list_has_dup l -> (forall x, In x l -> x <> Zp /\ inv x <> x /\ In (inv x) l) -> Zp_lprod l = Op.
      Proof.
        induction on l as IHl with measure (length l); intros H0 Hl.
        destruct l as [ | x l ].
        + rewrite Zp_lprod_nil; auto.
        + destruct (Hl x) as (H1 & H2 & [H3 | H3]); try (simpl; auto; fail).
          1: destruct H2; auto.
          destruct in_split with (1 := H3) as (u & v & ?); subst.
          rewrite Zp_lprod_cons, Zp_lprod_app, Zp_lprod_cons.
          rewrite (Zp_mult_assoc _ (inv x)), (Zp_mult_comm _ (inv x)).
          repeat rewrite Zp_mult_assoc.
          rewrite (Zp_mult_comm _ (inv x)), Zp_invert_spec2; auto.
          rewrite Zp_mult_one, <- Zp_lprod_app.
          apply IHl.
          * simpl; do 2 rewrite app_length; simpl; lia.
          * contradict H0.
            constructor 2.
            apply perm_list_has_dup with (inv x::u++v).
            - apply Permutation_cons_app; auto.
            - constructor 2; auto.
          * intros y Hy.
            destruct (Hl y) as (G1 & G2 & G3).
            - apply in_app_or in Hy; right; apply in_or_app; simpl; tauto.
            - repeat (split; auto).
              destruct G3 as [ G3 | G3 ].
              ++ destruct H0; rewrite G3 at 2.
                 rewrite Zp_invert_involutive.
                 constructor 2.
                 apply perm_list_has_dup with (y::u++v).
                 ** apply Permutation_cons_app; auto.
                 ** constructor 1; auto.
              ++ apply in_or_app.
                 apply in_app_or in G3.
                 destruct G3 as [ | [ G3 | ] ]; try tauto.
                 exfalso.
                 apply f_equal with (f := inv) in G3.
                 do 2 rewrite Zp_invert_involutive in G3.
                 destruct H0.
                 apply perm_list_has_dup with (inv x::(x::u)++v).
                 ** apply Permutation_cons_app with (l1 := x::u); auto.
                 ** simpl; constructor 2; constructor 1; subst; auto.
      Qed.

      Fact Zp_lprod_fact n : 〚fact (S n)〛= Zp_lprod (map nat2Zp (list_an 2 n)).
      Proof using Hp'.
        induction n as [ | n IHn ].
        + apply Zp_inj; simpl; auto.
        + rewrite fact_S, nat2Zp_mult.
          replace (S n)%nat with (n+1)%nat by lia.
          rewrite list_an_plus, map_app, Zp_lprod_app, <- IHn, Zp_mult_comm.
          f_equal.
          * do 2 f_equal; lia.
          * simpl list_an; unfold map. 
            rewrite Zp_lprod_cons, Zp_mult_comm, Zp_mult_one.
            f_equal; lia.
      Qed.

      Theorem Wilson_thm_1 :〚fact (p-1)〛= ∸Op.
      Proof using Hp'.
        replace (p-1)%nat with (S (p-2))%nat by lia.
        rewrite Zp_lprod_fact.
        destruct (eq_nat_dec p 2) as [ H1 | H1 ].
        + rewrite H1; simpl map; rewrite Zp_lprod_nil.
          rewrite <- nat2Zp_minus_one; apply nat2Zp_inj.
          rewrite H1; auto.
        + replace (p-2)%nat with (p-3+1)%nat by lia.
          rewrite list_an_plus, map_app, Zp_lprod_app.
          replace (p-3+2)%nat with (p-1)%nat by lia.
          simpl list_an at 2; unfold map at 2.
          rewrite Zp_lprod_cons, Zp_lprod_nil.
          rewrite Zp_mult_autoinv.
          * rewrite nat2Zp_minus_one; ring.
          * intros H.
            apply list_has_dup_map_inv in H.
            - revert H; apply not_list_an_has_dup.
            - intros x y; do 2 rewrite list_an_spec.
              intros Hx Hy.
              rewrite nat2Zp_inj, rem_lt, rem_lt; auto; lia.
          * intros x; rewrite in_map_iff.
            intros (n & ? & Hn); subst.
            rewrite list_an_spec in Hn.
            split; [ | split ].
            - intros H.
              rewrite <- nat2Zp_zero in H.
              apply nat2Zp_inj in H.
              rewrite rem_of_0, rem_lt in H; lia.
            - apply Zp_invert_not_fix; lia.
            - destruct Zp_invert_stable with n as (m & G1 & G2); try lia.
              apply in_map_iff.
              exists m; split; auto.
              apply list_an_spec; lia.
      Qed. 

    End prime.

    Fact Zp_divides_and_invertible d k n i : (d * k = n)%nat ->〚i〛⊗〚d〛= Op ->〚k〛=〚i〛⊗〚n〛.
    Proof.
      intros H1 H2.
      rewrite <- H1, nat2Zp_mult, Zp_mult_assoc, H2; ring.
    Qed.

  End Z2Zp.

End Zp.

Fact divides_not_0_interval p q : q <> 0 -> divides p q -> 1 <= p <= q.
Proof.
  intros Hq ([ | k ] & Hk); try lia.
Qed.

Fact divides_fact_lt q n : 1 <= q <= n -> divides q (fact n).
Proof.
  revert q; induction n as [ | n IHn ].
  + intros; rewrite fact_0; lia.
  + intros q Hq; rewrite fact_S.
    destruct (eq_nat_dec q (S n)).
    - subst; exists (fact n); ring.
    - apply divides_mult, IHn; lia.
Qed.

Theorem Wilson_theorem p : 2 <= p -> prime p <-> divides p (fact (p-1)+1).
Proof.
  intros H1; split.
  + intros H2.
    assert (Hp : p <> 0) by lia.
    rewrite divides_nat2Zp with (Hp := Hp).
    rewrite nat2Zp_plus, Wilson_thm_1; auto.
    rewrite nat2Zp_one, Zp_plus_comm, Zp_minus; auto.
  + intros H2; split; try lia.
    intros q Hq.
    destruct (eq_nat_dec q p) as [ Hp | Hp ]; auto.
    generalize (divides_trans Hq H2); intros H3.
    apply divides_plus_inv in H3.
    - apply divides_1_inv in H3; auto.
    - apply divides_fact_lt.
      apply divides_not_0_interval in Hq; lia.
Qed.

Section Z2Zp_morphishm.

  Variable (p : nat) (Hp : p <> 0).

  Fact Z2Zp_morphishm : ring_morphism 0%Z 1%Z Zplus Zmult Z.opp 
                                      (Zp_zero Hp) (Zp_one Hp) (Zp_plus Hp) (Zp_mult Hp) (Zp_opp Hp) (Z2Zp Hp).
  Proof.
    exists.
    + apply Z2Zp_zero.
    + apply Z2Zp_one.
    + apply Z2Zp_plus.
    + apply Z2Zp_mult.
    + apply Z2Zp_opp.
  Qed.

End Z2Zp_morphishm.
