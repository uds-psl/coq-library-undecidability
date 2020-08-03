(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Euclidian division and Bezout's identity *)

Require Import List Arith Lia Permutation Extraction.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list utils_nat 
                 gcd prime binomial.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

Set Implicit Arguments.

Section Informative_Chinese_Remainder_theorems.

  Hint Resolve divides_refl divides_mult divides_mult_r : core.

  Section Binary.

    Variable (u v a b : nat) (Hu : u <> 0) (Hv : v <> 0) (Huv : is_gcd u v 1).

    Theorem CRT_bin_informative : { w | rem w u = rem a u /\ rem w v = rem b v /\ 2 < w }.
    Proof.
      destruct bezout_rel_prime with (1 := Huv) as (x & y & H1).
      assert (rem (x*u) v = rem 1 v) as H2.
      { rewrite rem_plus_div with (a := 1) (b := u*v); auto.
        rewrite <- H1; apply rem_plus_div; auto. }
      assert (rem (y*v) u = rem 1 u) as H3.
      { rewrite rem_plus_div with (a := 1) (b := u*v); auto.
        rewrite <- H1, plus_comm.
        apply rem_plus_div; auto. }
      exists (3*(u*v)+a*(y*v)+b*(x*u)); msplit 2.
      + rewrite <- rem_plus_rem, (mult_assoc b).
        rewrite rem_scal with (k := b*x), rem_diag; auto.
        rewrite Nat.mul_0_r, rem_of_0, Nat.add_0_r.
        rewrite <- rem_plus_rem, rem_scal, H3, <- rem_scal, Nat.mul_1_r.
        rewrite rem_plus_rem, plus_comm.
        symmetry; apply rem_plus_div; auto.
      + rewrite <- plus_assoc, (plus_comm (a*_)), plus_assoc.
        rewrite <- rem_plus_rem, (mult_assoc a).
        rewrite rem_scal with (k := a*y), rem_diag; auto.
        rewrite Nat.mul_0_r, rem_of_0, Nat.add_0_r.
        rewrite <- rem_plus_rem, rem_scal, H2, <- rem_scal, Nat.mul_1_r.
        rewrite rem_plus_rem, plus_comm.
        symmetry; apply rem_plus_div; auto.
      + apply lt_le_trans with (3*1); try lia.
    Qed.

  End Binary.

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
        - assert (0 < m1 * m2); try lia.
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

End Informative_Chinese_Remainder_theorems.

Theorem CRT u v a b : u <> 0 -> v <> 0 -> is_gcd u v 1 -> exists w, rem w u = rem a u /\ rem w v = rem b v /\ 2 < w.
Proof.
  intros Hu Hv H.
  destruct (@CRT_bin_informative u v a b) as (w & ?); auto.
  exists w; auto.
Qed.

Section sequence_of_coprimes.

  Let seq_of_coprimes_lt n i j : i < j <= n -> is_gcd (1+i*fact n) (1+j*fact n) 1.
  Proof.
    intros (H1 & H2).
    apply no_common_prime_is_coprime; try discriminate.
    intros p Hp H3 H4.
    assert (divides p ((j-i)*fact n)) as H5.
    { replace ((j-i)*fact n) with (1+j*fact n - (1+i*fact n)).
      + apply divides_minus; auto.
      + rewrite Nat.mul_sub_distr_r; lia. }
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
    { apply prime_ge_2 in Hp; lia. }
    destruct Hp.
    split; try lia.
    apply divides_le in H5; lia.
  Qed.

  Theorem seq_of_coprimes n i j : 
          i <= n 
       -> j <= n
       -> i <> j
       -> is_gcd (1+i*fact n) (1+j*fact n) 1.
  Proof.
    intros H1 H2 H3.
    destruct (lt_eq_lt_dec i j) as [ [] | ]; try tauto;
      [ | apply is_gcd_sym ]; apply seq_of_coprimes_lt; lia.
  Qed.

End sequence_of_coprimes.

Section Godel_beta.

  (** Gödel Beta function and its "inverse" as a Coq function
      for the reduction H10C -> termination of one particular µ-rec function *) 

  Definition godel_beta a b n := rem a (S ((S n)*b)).

  Theorem godel_beta_inv n (v : vec nat n) : 
     { a : nat & { b | forall p, godel_beta a b (pos2nat p) = vec_pos v p } }.
  Proof.
    set (j := S (lmax (n :: vec_list v))).
    assert (n < j) as Hm1.
    { apply le_n_S, lmax_prop; left; auto. }
    assert (forall p, vec_pos v p < j) as Hm2.
    { intros p; apply le_n_S, lmax_prop.
      right; apply vec_list_In. }
    revert Hm1 Hm2; generalize j; clear j.
    intros j Hj1 Hj2.
    set (m := vec_set_pos (fun p : pos n => 1+(S (pos2nat p)*fact j))).
    destruct (CRT_informative m v) as (w & Hw).
    + intros p; unfold m; rewrite vec_pos_set; discriminate.
    + intros p q H; unfold m; repeat rewrite vec_pos_set.
      apply seq_of_coprimes.
      * generalize (pos2nat_prop p); lia.
      * generalize (pos2nat_prop q); lia.
      * contradict H; inversion H.
        apply pos2nat_inj; auto.
    + exists w, (fact j).
      intros p; unfold godel_beta.
      generalize (Hw p); unfold m; repeat rewrite vec_pos_set.
      intros E; unfold plus in E; rewrite E.
      apply rem_idem.
      apply lt_le_trans with (1 := Hj2 _).
      apply le_trans with (S (1*j)); try lia.
      apply le_n_S, mult_le_compat; try lia.
      apply divides_le.
      * generalize (fact_gt_0 j); lia.
      * apply divides_n_fact_n; lia.
  Qed.

  Corollary godel_beta_fun_inv n f : { a : _ & { b | forall p, p < n -> f p = godel_beta a b p } }.
  Proof.
    destruct godel_beta_inv with (v := vec_set_pos (fun p : pos n => f (pos2nat p)))
       as (a & b & H).
    exists a, b; intros p Hp.
    specialize (H (nat2pos Hp)).
    rewrite vec_pos_set, pos2nat_nat2pos in H.
    auto.
  Qed.

  Theorem godel_beta_fun_inv_triples n f : 
     { a : _ & { b | forall p, p < n -> f p = (godel_beta a b (  3*p),
                                               godel_beta a b (1+3*p),
                                               godel_beta a b (2+3*p)) } }.
  Proof.
    assert (H3 : 3 <> 0) by lia.
    set (g n := match rem n 3, f (div n 3) with
      | 0, (x,_,_) => x
      | 1, (_,y,_) => y
      | _, (_,_,z) => z
    end).
    destruct (godel_beta_fun_inv (3*n) g) as (a & b & Hab).
    exists a, b; intros p Hp.
    rewrite mult_comm.
    do 2 rewrite (plus_comm _ (p*_)).
    replace (p*3) with (p*3+0) at 1 by lia.
    rewrite <- (Hab (p*3+0)), <- (Hab (p*3+1)), <- (Hab (p*3+2)); try lia.
    unfold g.
    do 3 rewrite (rem_erase p 3 _ eq_refl).
    repeat (rewrite rem_idem; try lia).
    repeat (rewrite (@div_prop (p*3+_) 3 _ _ eq_refl); try lia).
    destruct (f p) as ((?,?),?); auto.
  Qed.
 
End Godel_beta.
