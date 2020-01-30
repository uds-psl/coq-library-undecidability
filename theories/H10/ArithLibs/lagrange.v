(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega Eqdep_dec ZArith List.

From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list gcd prime php utils_nat.
From Undecidability.H10.ArithLibs Require Import Zp.

Set Implicit Arguments.

Section lagrange.

  Fact prime_2_or_odd p : prime p -> p = 2 \/ exists n, 0 < n /\ p = 2*n+1.
  Proof.
    intros Hp.
    assert (H1 : p <> 0).
    { generalize (prime_ge_2 Hp); omega. }
    assert (H3 : 2 <> 0) by discriminate.
    destruct (eq_nat_dec p 2) as [ | H2 ]; auto; right.
    assert (rem p 2 = 1) as Hp1.
    { generalize (div_rem_spec2 p H3).
      case_eq (rem p 2).
      + intros H _.
        apply divides_rem_eq in H.
        apply proj2 in Hp.
        destruct (Hp _ H); subst; omega.
      + intros; omega. }
    exists (div p 2); split.
    + generalize (div_rem_spec1 p 2) (prime_ge_2 Hp).
      destruct (div p 2); intros;  omega.
    + rewrite mult_comm.
      rewrite (div_rem_spec1 p 2) at 1.
      f_equal; auto.
  Qed.

  Lemma lagrange_prelim p n : prime p -> p = 2*n+1 -> 0 < n -> exists a b, divides p (1+a*a+b*b) /\ 2*a <= p-1 /\ 2*b <= p-1.
  Proof.
    intros H2 Hn2 Hn1.
    assert (Hp : p <> 0) by omega.
    set (l := list_an 0 (1+n)).
    assert (Hl : forall x, In x l <-> x <= n).
    { unfold l; intros x; rewrite list_an_spec; omega. }
    set (f x := nat2Zp Hp (x*x)).
    assert (Hf : forall x y, In x l -> In y l -> f x = f y -> x = y).
    { unfold f; intros x y G1 G2 H.
      do 2 rewrite nat2Zp_mult in H.
      apply Zp_prime_square_eq_square in H; auto.
      destruct H as [ H | H ].
      + rewrite nat2Zp_inj in H.
        rewrite <- (@rem_idem x p), H, rem_idem; auto.
        - apply Hl in G2; subst; omega.
        - apply Hl in G1; subst; omega.
      + apply f_equal with (f := @proj1_sig _ _) in H; simpl in H.
        rewrite rem_idem in H.
        2: apply Hl in G1; subst; omega.
        case_eq (rem y p).
        - intros Hy.
          rewrite Hy, Nat.sub_0_r, rem_diag in H; auto.
          rewrite rem_idem in Hy; try omega.
          apply Hl in G2; subst; omega.
        - intros w Hw.
          rewrite rem_idem in H; try omega.
          rewrite H.
          apply Hl in G2.
          apply Hl in G1.
          rewrite rem_idem in H; omega. }
    set (g y := Zp_opp Hp (Zp_plus Hp (Zp_one Hp) (f y))).
    assert (Hg : forall x y, In x l -> In y l -> g x = g y -> x = y).
    { intros x y G1 G2 G3.
      unfold g in G3.
      apply Zp_opp_inj, Zp_plus_inj_l in G3.
      revert G3; apply Hf; auto. }
    destruct partition_intersection with (l := map f l) (m := map g l) (k := Zp_list Hp)
        as [ G | [ G | (u & G1 & G2) ] ].
    * rewrite Zp_list_length, app_length, map_length, map_length.
      unfold l; rewrite list_an_length; omega.
    * intros ? _; apply Zp_list_spec.
    * apply list_has_dup_map_inv in G; auto.
      apply not_list_has_dup_an in G; tauto.
    * apply list_has_dup_map_inv in G; auto.
      apply not_list_has_dup_an in G; tauto.
    * rewrite in_map_iff in G1.
      rewrite in_map_iff in G2.
      destruct G1 as (a & G3 & G4).
      destruct G2 as (b & G5 & G6).
      exists a, b; split; [ | split ].
      + rewrite divides_nat2Zp with (Hp := Hp).
        rewrite (plus_comm 1), <- plus_assoc.
        do 2 rewrite nat2Zp_plus.
        rewrite nat2Zp_one.
        fold (f a).
        apply Zp_opp_plus_eq.
        fold (f b); fold (g b).
        rewrite G3, G5, Zp_plus_zero.
        trivial.
      + apply Hl in G4; rewrite Hn2; omega.
      + apply Hl in G6; rewrite Hn2; omega.
  Qed.

  Let square_lemma x y : (x+y)*(x+y) = x*x+2*(x*y)+y*y.
  Proof. ring. Qed.

  Lemma lagrange_prelim' p : prime p -> exists n a b, n*p = 1+a*a+b*b /\ 0 < n < p.
  Proof.
    intros Hp.
    destruct (prime_2_or_odd Hp) as [ | (n & Hn1 & Hn2) ].
    + exists 1, 1, 0; subst; auto.
    + destruct (lagrange_prelim Hp Hn2 Hn1) as (a & b & (k & Hk) & Ha & Hb).
      exists k, a, b; split; auto.
      split.
      1: destruct k; simpl in Hk; try omega; discriminate.
      assert (a <= n) as Ha' by omega.
      assert (b <= n) as Hb' by omega.
      destruct (le_lt_dec p k) as [ H | H ]; auto.
      exfalso.
      assert (a*a+2*(1*1)+b*b <= k*p) as C; try omega.
      apply le_trans with ((n+n)*(n+n)).
      2: apply mult_le_compat; omega.
      rewrite square_lemma.
      apply plus_le_compat.
      2: apply mult_le_compat; auto.
      apply plus_le_compat.
      1: apply mult_le_compat; auto.
      apply mult_le_compat_l.
      apply mult_le_compat; omega.
  Qed.

  Section rem_square_opp.

    Variable (x m : nat) (Hx : x < m).

    Let Hm : m <> 0. Proof. omega. Qed.

    Add Ring Zp_ring : (Zp_is_ring Hm).

    Fact rem_square_opp : rem (x*x) m = rem ((m-x)*(m-x)) m.
    Proof.
      rewrite <- nat2Zp_inj with (Hp := Hm).
      rewrite (nat2Zp_mult Hm (m-x)), nat2Zp_mult.
      rewrite !nat2Zp_minus; try omega.
      rewrite !nat2Zp_p; ring.
    Qed.

  End rem_square_opp.

  Section rem_square_div2. 

    Variable (m : nat) (Hm : 0 < m).

    Let Hm2 : 2*m <> 0. Proof. omega. Qed.

    Fact rem_square_div2_even x : exists y, rem (x*x) (2*m) = rem (y*y) (2*m) /\ y <= m.
    Proof.
      destruct (le_lt_dec (rem x (2*m)) m) as [ H | H ].
      + exists (rem x (2*m)); split; auto.
        rewrite rem_mult_rem, (mult_comm (rem _ _)), rem_mult_rem; auto.
      + generalize (div_rem_spec2 x Hm2); intros H1.
        exists (2*m - rem x (2*m)); split; try omega.
        rewrite <- rem_square_opp; auto.
        rewrite rem_mult_rem, (mult_comm (rem _ _) x), rem_mult_rem; auto.
    Qed.

    Let Hm3 : 1+2*m <> 0. Proof. omega. Qed.

    Fact rem_square_div2_odd x : exists y, rem (x*x) (1+2*m) = rem (y*y) (1+2*m) /\ y <= m.
    Proof.
      destruct (le_lt_dec (rem x (1+2*m)) m) as [ H | H ].
      + exists (rem x (1+2*m)); split; auto.
        rewrite rem_mult_rem, (mult_comm (rem _ _)), rem_mult_rem; auto.
      + generalize (div_rem_spec2 x Hm3); intros H1.
        exists (1+2*m - rem x (1+2*m)); split; try omega.
        rewrite <- rem_square_opp; auto.
        rewrite rem_mult_rem, (mult_comm (rem _ _) x), rem_mult_rem; auto.
    Qed.

  End rem_square_div2.

  Fact rem_square_div2 x m : 1 < m -> exists y, rem (x*x) m = rem (y*y) m /\ y <= div m 2.
  Proof.
    intros Hm.
    destruct (euclid_2 m) as (p & [ Hp | Hp ]).
    + subst m; rewrite div_2_fix_1.
      apply rem_square_div2_even; omega.
    + subst; rewrite div_2_fix_2.
      apply rem_square_div2_odd; omega.
  Qed.

  Fact rem_sum_fun a b c m : rem a m = rem b m -> rem (a+c) m = rem (b+c) m.
  Proof. intros H; rewrite rem_plus, H, <- rem_plus; auto. Qed.

  Fact rem_sum4_rem a b c d m : rem (a+b+c+d) m = rem (rem a m+rem b m+rem c m+rem d m) m.
  Proof.
    do 3 (rewrite rem_plus; apply rem_sum_fun; rewrite rem_rem); auto.
  Qed.

  Fact Z2Zp_div m (Hm : m <> 0) x : 
          Z2Zp Hm x = Zp_zero Hm 
       -> exists y, (x = Z.of_nat m * y)%Z.
  Proof.
    intros H.
    rewrite <- Z2Zp_zero in H.
    apply Z2Zp_inj in H.
    destruct H as (y & Hy); exists y.
    rewrite Zmult_comm, <- Hy; ring.
  Qed.

  Fact Zsquare_bound x y : (-y <= x <= y -> x*x <= y*y)%Z.
  Proof.
    intros (H1 & H2).
    destruct (Z_pos_or_neg x).
    + apply Z.square_le_mono_nonneg; auto.
    + replace (y*y)%Z with ((-y)*(-y))%Z by ring.
      apply Z.square_le_mono_nonpos; omega.
  Qed.

  Fact Zrem_double m (Hm : m <> 0) x :  exists y, Z2Zp Hm x = Z2Zp Hm y
                                              /\ (4*(y*y) <= Z.of_nat m * Z.of_nat m)%Z.
  Proof.
    destruct (euclid_2 m) as (p & [ H | H ]).
    + destruct (Zp_repr_interval Hm (- Z.of_nat p)%Z (Z.of_nat p) x) as (y & H1 & H2).
      * rewrite H, Nat2Z.inj_mul; simpl Z_of_nat; omega.
      * exists y; split; auto.
        rewrite H, Nat2Z.inj_mul.
        simpl Z.of_nat.
        replace (2*Z.of_nat p*(2*Z.of_nat p))%Z 
        with    (4*(Z.of_nat p*Z.of_nat p))%Z by ring.
        apply Zmult_le_compat_l; try omega.
        apply Zsquare_bound; omega.
    + destruct (Zp_repr_interval Hm (- Z.of_nat p)%Z (1+Z.of_nat p) x) as (y & H1 & H2).
      * rewrite H, Nat2Z.inj_add, Nat2Z.inj_mul; simpl Z_of_nat; omega.
      * exists y; split; auto.
        apply Z.le_trans with (Z.of_nat (2*p) * Z.of_nat (2*p))%Z.
        - rewrite Nat2Z.inj_mul.
          simpl Z.of_nat.
          replace (2*Z.of_nat p*(2*Z.of_nat p))%Z 
          with    (4*(Z.of_nat p*Z.of_nat p))%Z by ring.
          apply Zmult_le_compat_l; try omega.
          apply Zsquare_bound; omega.
        - apply Zsquare_bound; subst.
          rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul; simpl Z.of_nat; omega.
  Qed.
 
  Fact bounded_four x1 x2 x3 x4 m : 
            (x1 <= m -> x2 <= m -> x3 <= m -> x4 <= m
         -> x1+x2+x3+x4 = 4*m -> x1 = m /\ x2 = m /\ x3 = m /\ x4 = m)%Z.
  Proof. omega. Qed.

  Fact positive_sum_4 a b c d : 
    (0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> a + b + c + d = 0 -> a = 0 /\ b = 0 /\ c = 0 /\ d = 0)%Z.
  Proof. intros; omega. Qed.

  Fact four_square_zero x1 x2 x3 x4 : 
          (x1*x1+x2*x2+x3*x3+x4*x4 = 0)%Z -> (x1 = 0 /\ x2 = 0 /\ x3 = 0 /\ x4 = 0)%Z.
  Proof.
    intros H.
    apply positive_sum_4 in H; try apply Z.square_nonneg.
    destruct H as (H1 & H2 & H3 & H4).
    apply Zmult_integral in H1.
    apply Zmult_integral in H2.
    apply Zmult_integral in H3.
    apply Zmult_integral in H4.
    omega.
  Qed.
 
  Fact Zsquare_inj x y : (x*x = y*y -> { x = y } + { - x = y } )%Z.
  Proof.
    intros H.
    assert ( (x+y)*(x-y) = 0 )%Z as E.
    { rewrite Z.mul_sub_distr_l, !Z.mul_add_distr_r, H; ring. }
    apply Zmult_integral in E.
    destruct (Z.eq_dec x y); auto.
    right; omega.
  Qed.

  Fact four_square_simpl x m : (4*(x*x) = Z.of_nat m*Z.of_nat m)%Z -> { n | m = 2*n /\ (x = Z.of_nat n \/ (x = - Z.of_nat n)%Z) }.
  Proof.
    intros H.
    replace (4*(x*x))%Z with ((2*x)*(2*x))%Z in H by ring.
    apply Zsquare_inj in H.
    destruct H as [ H | H ].
    + destruct Z_of_nat_complete_inf with x as (k & ->).
      * generalize (Zle_0_nat m); omega.
      * exists k; split; auto.
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_mul, <- H; auto.
    + destruct (Z_of_nat_complete_inf (Z.opp x)) as (k & Hk).
      * generalize (Zle_0_nat m); omega.
      * exists k; split.
        - apply Nat2Z.inj.
          rewrite Nat2Z.inj_mul, <- H, <- Hk; ring.
        - right; rewrite <- Hk; ring.
  Qed.

  Fact four_square_simpl' x m : (4*(x*x) = Z.of_nat (2*m)*Z.of_nat (2*m))%Z 
                             -> x = Z.of_nat m \/ (x = - Z.of_nat m)%Z.
  Proof.
    intros H.
    replace (4*(x*x))%Z with ((2*x)*(2*x))%Z in H by ring.
    apply Zsquare_inj in H.
    destruct H as [ H | H  ]; rewrite Nat2Z.inj_mul in H; 
     change (Z.of_nat 2) with 2%Z in H; omega.
  Qed.

  Fact Zsquare_plus (a b : Z) : ((a+b)*(a+b) = a*a + 2*a*b + b*b)%Z.
  Proof. ring. Qed.

  Section half_modulus_lemma.

    (* x = +- m [ 2*m ] -> x² = m² [4*m²] 

       x = m+2*k*m
       x² = m²+2*2*k*m²+4*k²m²
    *)

    Variable (m : nat) (H2m : 2*m <> 0) (Hm2 : 4*m*m <> 0).

    Let lemma1 x :
          Z2Zp H2m x = nat2Zp H2m m 
       -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
    Proof.
      intros H.
      rewrite <- Z2Zp_of_nat in H.
      apply Z2Zp_inj in H.
      destruct H as (k & H).
      assert (x = Z.of_nat m+2*k*Z.of_nat m)%Z as Hx.
      { rewrite Nat2Z.inj_mul, Zmult_assoc, (Zmult_comm k) in H.
        change 2%Z with (Z.of_nat 2); omega. }
      rewrite Hx, Zsquare_plus, !Z2Zp_plus.
      replace (2*Z.of_nat m * (2*k*Z.of_nat m))%Z
      with    (Z.of_nat (4*m*m)*k)%Z.
      2:{ rewrite !Nat2Z.inj_mul; ring. }
      replace (2*k*Z.of_nat m * (2*k*Z.of_nat m))%Z
        with    (Z.of_nat (4*m*m)*(k*k))%Z.
      2:{ rewrite !Nat2Z.inj_mul; ring. }
      rewrite (Z2Zp_mult _ _ k), Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero.
      rewrite (Z2Zp_mult _ _ (k*k)), Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero.
      rewrite !Zp_plus_zero_r, <- Nat2Z.inj_mul, Z2Zp_of_nat; auto.
    Qed.

    Let lemma2 x :
          (Z2Zp H2m x = Zp_opp H2m (nat2Zp H2m m))%Z 
       -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
    Proof.
      intros H.
      replace (x*x)%Z with ((-x)*(-x))%Z by ring.
      apply lemma1.
      rewrite Z2Zp_opp, H, Zp_opp_inv; auto.
    Qed.

    Fact half_modulus_lemma' x :
           Z2Zp H2m x = nat2Zp H2m m 
       \/ (Z2Zp H2m x = Zp_opp H2m (nat2Zp H2m m))%Z
       -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
    Proof. intros []; auto. Qed.

    Fact half_modulus_lemma x y : Z2Zp H2m x = Z2Zp H2m y
                 -> y = Z.of_nat m \/ y = (- Z.of_nat m)%Z
                 -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
    Proof.
      intros H1 H2.
      apply half_modulus_lemma'.
      rewrite H1.
      destruct H2; subst y; [ left | right ].
      + rewrite Z2Zp_of_nat; auto.
      + rewrite Z2Zp_opp, Z2Zp_of_nat; auto.
    Qed.

  End half_modulus_lemma.

  Let four_squares a b c d := (a*a+b*b+c*c+d*d)%Z.

  Fact Euler_squares x y a1 b1 c1 d1 a2 b2 c2 d2 :
         (x = four_squares a1 b1 c1 d1
       -> y = four_squares a2 b2 c2 d2
       -> x*y = four_squares (a1*a2+b1*b2+c1*c2+d1*d2)
                             (a1*b2-b1*a2+d1*c2-c1*d2)
                             (a1*c2-c1*a2+b1*d2-d1*b2)
                             (a1*d2-d1*a2+c1*b2-b1*c2))%Z.
  Proof. intros -> ->; unfold four_squares; ring. Qed.

  Section lagrange_prime.

    Variable (p : nat) (Hp : prime p).

    Let P n := 1 <= n < p /\ exists a b c d, Z.of_nat (n*p) = (a*a+b*b+c*c+d*d)%Z.

    (** DLW: This one was a pain in the ... *)

    Let lagrange_prime_step m : P m -> 1 < m -> exists n, n < m /\ P n.
    Proof.
      intros (H1 & x1 & x2 & x3 & x4 & H2) H3.
      assert (Hm : m <> 0) by omega.
      generalize (Zrem_double Hm x1)
                 (Zrem_double Hm x2)
                 (Zrem_double Hm x3)
                 (Zrem_double Hm x4).
      intros (y1 & E1 & Q1) (y2 & E2 & Q2) (y3 & E3 & Q3) (y4 & E4 & Q4).
      assert (Z2Zp Hm (y1*y1+y2*y2+y3*y3+y4*y4) = Z2Zp Hm 0) as H4.
      { rewrite !Z2Zp_plus, !Z2Zp_mult, <- E1, <- E2, <- E3, <- E4.
        rewrite <- !Z2Zp_mult, <- !Z2Zp_plus, <- H2.
        rewrite Nat2Z.inj_mul, Z2Zp_mult.
        rewrite Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero, Z2Zp_zero; auto. }
      apply Z2Zp_inj in H4.
      destruct H4 as (r & Hr).
      rewrite Z.sub_0_r in Hr.
      assert (4 * (r * Z.of_nat m) <= 4 * (Z.of_nat m * Z_of_nat m))%Z as Hr'.
      { rewrite <- Hr, !Z.mul_add_distr_l; omega. }
      rewrite !(Zmult_comm 4) in Hr'.
      apply Zmult_le_reg_r in Hr'; try omega.
      apply Zmult_le_reg_r in Hr'; try omega.
      assert (0 <= r * Z_of_nat m)%Z as Hr''.
      { rewrite <- Hr; repeat apply Z.add_nonneg_nonneg; apply Z.square_nonneg. }
      apply Zmult_le_0_reg_r in Hr''.
      2:{ apply (inj_gt m 0); omega. }
      apply Z_of_nat_complete_inf in Hr''.
      destruct Hr'' as (k & ?); subst r.
      apply Nat2Z.inj_le in Hr'.
      destruct (eq_nat_dec m k) as [ <- | Hk1 ].
      { apply f_equal with (f := fun i => (4*i)%Z) in Hr.
        rewrite !Z.mul_add_distr_l in Hr.
        apply bounded_four in Hr; auto.
        destruct Hr as (F1 & F2 & F3 & F4).
        apply four_square_simpl in F1.
        destruct F1 as (q & Hq & F1).
        rewrite Hq in F2, F3, F4. 
        apply four_square_simpl' in F2.
        apply four_square_simpl' in F3.
        apply four_square_simpl' in F4.
        subst m. 
        assert (4*q*q <> 0) as Hq.
        { destruct q; simpl; try discriminate; omega. }
        apply half_modulus_lemma with (1 := E1) (Hm2 := Hq) in F1.
        apply half_modulus_lemma with (1 := E2) (Hm2 := Hq) in F2.
        apply half_modulus_lemma with (1 := E3) (Hm2 := Hq) in F3.
        apply half_modulus_lemma with (1 := E4) (Hm2 := Hq) in F4.
        assert (Z2Zp Hq (Z.of_nat (2 * q * p)) = Zp_zero Hq) as C.
        { rewrite H2, !Z2Zp_plus, F1, F2, F3, F4.
          rewrite <- !nat2Zp_plus.
          replace (q*q+q*q+q*q+q*q) with (4*q*q) by ring.
          rewrite nat2Zp_p; auto. }
        rewrite Z2Zp_of_nat in C.
        apply divides_nat2Zp in C.
        destruct C as (d & Hd).
        assert (divides (2*q) p) as C.
        { replace (d*(4*q*q)) with (2*q*(d*(2*q))) in Hd by ring.
          apply Nat.mul_cancel_l in Hd; try omega.
          exists d; auto. }
        apply Hp in C.
        destruct C as [ C | C ]; try omega. }
      destruct (eq_nat_dec k 0) as [ -> | Hk2 ].
      { simpl in Hr.
        apply four_square_zero in Hr.
        destruct Hr as (? & ? & ? & ?); subst y1 y2 y3 y4.
        assert (Hm2 : m*m <> 0).
        { destruct m; simpl; try discriminate; omega. }
        assert (forall x, Z2Zp Hm x = Z2Zp Hm 0 -> Z2Zp Hm2 (x*x) = Zp_zero Hm2) as L.
        { intros x Hx.
          apply Z2Zp_inj in Hx.
          destruct Hx as (d & Hd).
          rewrite Z.sub_0_r in Hd.
          rewrite Hd.
          replace (d*Z.of_nat m*(d*Z.of_nat m))%Z
          with    (Z.of_nat (m*m)*(d*d))%Z.
          2:{ rewrite Nat2Z.inj_mul; ring. }
          rewrite Z2Zp_mult, Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero; auto. }
        apply L in E1.
        apply L in E2.
        apply L in E3.
        apply L in E4.
        clear L.
        assert (Z2Zp Hm2 (Z.of_nat (m*p)) = Zp_zero Hm2) as C.
        { rewrite H2, !Z2Zp_plus, E1, E2, E3, E4, !Zp_plus_zero; auto. }
        rewrite Z2Zp_of_nat in C.
        apply divides_nat2Zp in C.
        destruct C as (d & Hd).
        assert (divides m p) as C.
        { replace (d*(m*m)) with (m*(d*m)) in Hd by ring.
          apply Nat.mul_cancel_l in Hd; try omega.
          exists d; auto. }
        apply Hp in C.
        destruct C as [ C | C ]; try omega. }
      assert (0 < k < m) as Hk by omega.
      clear Hr' Hk1 Hk2.
      symmetry in Hr.
      rewrite <- Nat2Z.inj_mul in Hr.
      clear Q1 Q2 Q3 Q4.
      assert (exists a b c d, Z.of_nat (k*p*m*m) = four_squares a b c d%Z
                           /\ Z2Zp Hm a = Zp_zero Hm
                           /\ Z2Zp Hm b = Zp_zero Hm
                           /\ Z2Zp Hm c = Zp_zero Hm
                           /\ Z2Zp Hm d = Zp_zero Hm) as Q.
      { exists (x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4)%Z,
               (x1 * y2 - x2 * y1 + x4 * y3 - x3 * y4)%Z, 
               (x1 * y3 - x3 * y1 + x2 * y4 - x4 * y2)%Z,
               (x1 * y4 - x4 * y1 + x3 * y2 - x2 * y3)%Z; split.
        + rewrite <- (Euler_squares _ _ _ _ _ _ _ _ H2 Hr).
          rewrite <- Nat2Z.inj_mul; f_equal; ring.
        + msplit 3.
          * rewrite !Z2Zp_plus, !Z2Zp_mult. 
            rewrite <- E1, <- E2, <- E3, <- E4.
            rewrite <- !Z2Zp_mult, <- !Z2Zp_plus.
            rewrite <- H2, Nat2Z.inj_mul, Z2Zp_mult, 
                    Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero; auto.
          * repeat (rewrite !Z2Zp_minus || rewrite !Z2Zp_plus). 
            rewrite !Z2Zp_mult.
            rewrite <- E1, <- E2, <- E3, <- E4.
            rewrite <- !Z2Zp_mult.
            repeat (rewrite <- !Z2Zp_minus || rewrite <- !Z2Zp_plus).
            rewrite <- Z2Zp_zero; f_equal; ring.
          * repeat (rewrite !Z2Zp_minus || rewrite !Z2Zp_plus). 
            rewrite !Z2Zp_mult.
            rewrite <- E1, <- E2, <- E3, <- E4.
            rewrite <- !Z2Zp_mult.
            repeat (rewrite <- !Z2Zp_minus || rewrite <- !Z2Zp_plus).
            rewrite <- Z2Zp_zero; f_equal; ring.
          * repeat (rewrite !Z2Zp_minus || rewrite !Z2Zp_plus). 
            rewrite !Z2Zp_mult.
            rewrite <- E1, <- E2, <- E3, <- E4.
            rewrite <- !Z2Zp_mult.
            repeat (rewrite <- !Z2Zp_minus || rewrite <- !Z2Zp_plus).
            rewrite <- Z2Zp_zero; f_equal; ring. }
      clear x1 x2 x3 x4 H2 H3 y1 E1 y2 E2 y3 E3 y4 E4 Hr.
      destruct Q as (a & b & c & d & H & Ha & Hb & Hc & Hd).
      apply Z2Zp_div in Ha; destruct Ha as (x & ->).
      apply Z2Zp_div in Hb; destruct Hb as (y & ->).
      apply Z2Zp_div in Hc; destruct Hc as (z & ->).
      apply Z2Zp_div in Hd; destruct Hd as (w & ->).
      exists k; split; try omega; split; try omega.
      exists x, y, z, w.
      apply Z.mul_cancel_r with (p := Z.of_nat (m*m)).
      { intros E.
        apply Nat2Z.inj with (m := 0) in E.
        destruct m; try discriminate; omega. }
      rewrite <- Nat2Z.inj_mul, mult_assoc, H.
      rewrite Nat2Z.inj_mul; unfold four_squares; ring.
    Qed.

    Let lagrange_prime_rec : P 1.
    Proof.
      destruct (lagrange_prelim' Hp) as (n & a & b & H1 & H2 & H3).
      cut (P n).
      + revert H2 H3; clear H1.
        induction on n as IH with measure n.
        intros H2 H3 H.
        destruct (le_lt_dec n 1) as [ | Hn ].
        * now replace 1 with n by omega.
        * destruct (lagrange_prime_step H) as (m & H4 & H5); auto.
          generalize H5; destruct H5; apply IH; auto; omega.
      + split; try omega.
        exists 0%Z, 1%Z, (Z.of_nat a), (Z.of_nat b).
        rewrite H1, !Nat2Z.inj_add, !Nat2Z.inj_mul.
        simpl Z.of_nat at 1; omega.
    Qed.

    Theorem lagrange_prime : exists a b c d, Z.of_nat p = (a*a+b*b+c*c+d*d)%Z.
    Proof.
      replace p with (1*p) by omega.
      apply lagrange_prime_rec.
    Qed.

  End lagrange_prime.

  Check lagrange_prime.
  Print Assumptions lagrange_prime.

  Open Scope Z_scope.

  Lemma lagrange_theorem_nat : forall n, exists a b c d, Z.of_nat n = a*a+b*b+c*c+d*d.
  Proof.
    induction n as [ | | p Hp | x y Hx Hy ] using prime_rect.
    + exists 0, 0, 0, 0; auto.
    + exists 1, 0, 0, 0; auto.
    + apply lagrange_prime; auto.
    + destruct Hx as (a1 & b1 & c1 & d1 & H1).
      destruct Hy as (a2 & b2 & c2 & d2 & H2).
      subst.
      exists (a1*a2+b1*b2+c1*c2+d1*d2),
             (a1*b2-b1*a2+d1*c2-c1*d2),
             (a1*c2-c1*a2+b1*d2-d1*b2),
             (a1*d2-d1*a2+c1*b2-b1*c2).
      rewrite Nat2Z.inj_mul; apply Euler_squares; auto.
  Qed.

  (** An relative integer is positive iff it is the sum of four squares *)

  Lemma lagrange_theorem_Z n : 0 <= n <-> exists a b c d, n = a*a+b*b+c*c+d*d.
  Proof.
    split.
    + intros H.
      destruct Z_of_nat_complete with (1 := H) as (m & ->).
      apply lagrange_theorem_nat.
    + intros (a & b & c & d & ->).
      generalize (a*a) (b*b) (c*c) (d*d) 
                 (Z.square_nonneg a) (Z.square_nonneg b)
                 (Z.square_nonneg c) (Z.square_nonneg d).
      intros; omega.
  Qed.

End lagrange.

Check lagrange_theorem_Z.


