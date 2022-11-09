(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* ** Two infinite sequences of primes *)

Require Import List Arith Lia Bool Permutation.

From Undecidability.Shared.Libs.DLW 
  Require Import utils utils_tac utils_list utils_nat gcd rel_iter prime pos vec.

Set Implicit Arguments.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Set Implicit Arguments.

(* Unique decomposition with a prime *)

Lemma prime_neq_0 p : prime p -> p <> 0.
Proof.
  intros ? % prime_ge_2; lia.
Qed.

#[export] Hint Resolve prime_neq_0 : core.

Lemma power_factor_lt_neq p i j x y : 
         p <> 0 
      -> i < j 
      -> ~ divides p x 
      -> p^i * x <> p^j * y.
Proof.
  intros H1 H2 H3 H5.
  replace j with (i+S (j-i-1)) in H5 by lia.
  rewrite Nat.pow_add_r, <- Nat.mul_assoc in H5.
  rewrite Nat.mul_cancel_l in H5.
  2: apply Nat.pow_nonzero; auto.
  apply H3; subst x; simpl. 
  do 2 apply divides_mult_r; apply divides_refl.
Qed.

Lemma power_factor_uniq p i j x y : 
         p <> 0  
      -> ~ divides p x
      -> ~ divides p y 
      -> p^i * x = p^j * y
      -> i = j /\ x = y.
Proof.
  intros H1 H2 H3 H4.
  destruct (lt_eq_lt_dec i j) as [ [ H | H ] | H ].
  + exfalso; revert H4; apply power_factor_lt_neq; auto.
  + split; auto; subst j.
    rewrite Nat.mul_cancel_l in H4; auto.
    apply Nat.pow_nonzero; auto.
  + exfalso; symmetry in H4; revert H4; apply power_factor_lt_neq; auto.
Qed.

(* The unboundedness of primes *)

Lemma prime_above m : { p | m < p /\ prime p }.
Proof.
  destruct (prime_factor (n := fact m + 1)) as (p & ? & ?).
  - pose proof (lt_O_fact m); lia.
  - exists p; eauto. destruct (Nat.lt_ge_cases m p); eauto.
    eapply divides_plus_inv in H0.
    + eapply divides_1_inv in H0; subst. destruct H; lia.
    + eapply divides_fact. eapply prime_ge_2 in H; eauto.
Qed.

Lemma prime_dec p : { prime p } + { ~ prime p }.
Proof.
  destruct (le_lt_dec 2 p) as [ H | H ].
  + destruct (prime_or_div H) as [ (q & H1 & H2) | ? ]; auto.
    right; intros C; apply C in H2; lia.
  + right; intros (H1 & H2).
    destruct (H2 2); try lia.
    exists 0; simpl; lia.
Qed.

Lemma first_prime_above m : { p | m < p /\ prime p /\ forall q, m < q -> prime q -> p <= q }.
Proof.
  destruct min_dec with (P := fun p => m < p /\ prime p)
    as (p & H1 & H2).
  + intros n.
    destruct (lt_dec m n); destruct (prime_dec n); tauto.
  + destruct (prime_above m) as (p & ?); exists p; auto.
  + exists p; firstorder.
Qed.

Lemma prime_divides p q :
  prime p -> prime q -> divides p q -> p = q.
Proof.
  now intros Hp Hq [ [] % Hp | ] % Hq.
Qed.

Definition nxtprime n := proj1_sig (first_prime_above n).

Fact nxtprime_spec1 n : n < nxtprime n.
Proof. apply (proj2_sig (first_prime_above n)). Qed.

Fact nxtprime_spec2 n : prime (nxtprime n).
Proof. apply (proj2_sig (first_prime_above n)). Qed.

#[export] Hint Resolve nxtprime_spec1 nxtprime_spec2 prime_2 : core.

Fixpoint notprime_bool_rec n k :=
  match k with
    | 0   => true
    | S k' => negb (prime_bool n) && notprime_bool_rec (S n) k'
  end.

Theorem prime_bool_spec' p : prime_bool p = false <-> ~ prime p.
Proof.
  rewrite <- not_true_iff_false, prime_bool_spec; tauto.
Qed.

Fact notprime_bool_rec_spec n k : notprime_bool_rec n k = true <-> forall i, n <= i < k+n -> ~ prime i.
Proof.
  revert n; induction k as [ | k IHk ]; intros n; simpl.
  + split; auto; intros; lia.
  + rewrite andb_true_iff, negb_true_iff, 
            <- not_true_iff_false, prime_bool_spec, IHk.
    split.
    * intros (H1 & H2) i Hi.
      destruct (eq_nat_dec n i); subst; auto.
      apply H2; lia.
    * intros H; split; intros; apply H; lia.
Qed.

Definition nxtprime_bool n p := Nat.leb (S n) p && notprime_bool_rec (S n) (p - S n) && prime_bool p.

Fact nxtprime_bool_spec n p : nxtprime_bool n p = true <-> nxtprime n = p.
Proof.
  unfold nxtprime_bool.
  rewrite !andb_true_iff, Nat.leb_le, notprime_bool_rec_spec, prime_bool_spec.
  unfold nxtprime.
  destruct (first_prime_above n) as (q & G1 & G2 & G3); simpl.
  split.
  + intros ((H1 & H2) & H3).
    apply Nat.le_antisymm.
    * apply G3; auto.
    * apply Nat.nlt_ge. 
      intro; apply (H2 q); auto; lia.
  + intros ->; lsplit 2; auto.
    intros q Hq C; apply G3 in C; lia.
Qed.

Definition nthprime (n : nat) := iter nxtprime 2 n.

Lemma nthprime_prime n : prime (nthprime n).
Proof. unfold nthprime; destruct n; simpl; auto; rewrite iter_swap; auto. Qed. 

#[export] Hint Resolve nthprime_prime : core.

Lemma nthprime_ge n m : n < m -> nthprime n < nthprime m.
Proof.
  unfold nthprime.
  induction 1; simpl iter; rewrite iter_swap; auto.
  apply Nat.lt_trans with (2 := nxtprime_spec1 _); auto.  
Qed.

Lemma nthprime_inj n m : nthprime n = nthprime m -> n = m.
Proof.
  destruct (lt_eq_lt_dec n m) as [ [ H | ] | H ]; auto; 
    intros; eapply nthprime_ge in H; lia.
Qed.

Fact nthprime_nxt i p q : nthprime i = p -> nxtprime p = q -> nthprime (S i) = q.
Proof.
  replace (S i) with (i+1) by lia.
  unfold nthprime at 2.
  rewrite iter_plus; fold (nthprime i).
  intros -> ?; simpl; auto.
Qed.

(* Certified Erastosthene sieve would be helpfull here *)

Fact nthprime_0 : nthprime 0 = 2.
Proof. auto. Qed.

Local Ltac nth_prime_tac H := 
  apply nthprime_nxt with (1 := H);
  apply nxtprime_bool_spec; auto.

Fact nthprime_1 : nthprime 1 = 3.    Proof. nth_prime_tac nthprime_0. Qed.
Fact nthprime_2 : nthprime 2 = 5.    Proof. nth_prime_tac nthprime_1. Qed.
Fact nthprime_3 : nthprime 3 = 7.    Proof. nth_prime_tac nthprime_2. Qed.
Fact nthprime_4 : nthprime 4 = 11.   Proof. nth_prime_tac nthprime_3. Qed.
Fact nthprime_5 : nthprime 5 = 13.   Proof. nth_prime_tac nthprime_4. Qed.
Fact nthprime_6 : nthprime 6 = 17.   Proof. nth_prime_tac nthprime_5. Qed.

Record primestream :=
  {
    str :> nat -> nat;
    str_inj : forall n m, str n = str m -> n = m;
    str_prime : forall n, prime (str n);
  }.

#[export] Hint Immediate str_prime : core.
#[export] Hint Resolve str_inj : core.

Lemma primestream_divides (ps : primestream) n m :  divides (ps n) (ps m) -> n = m.
Proof.
  destruct ps as [ str H1 H2 ]; simpl.
  intros ? % prime_divides; eauto.
Qed.

Definition ps : primestream.
Proof.
  exists (fun n => nthprime (2 * n)); auto.
  intros; apply nthprime_inj in H; lia.
Defined.

Fact ps_1 : ps 1 = 5.
Proof. simpl; apply nthprime_2. Qed.

Definition qs : primestream.
Proof.
  exists (fun n => nthprime (1 + 2 * n)); auto.
  intros; apply nthprime_inj in H; lia.
Defined.

Fact qs_1 : qs 1 = 7.
Proof. simpl; apply nthprime_3. Qed.

Lemma ps_qs : forall n m, ps n = qs m -> False.
Proof. intros ? ? ? % nthprime_inj; lia. Qed. 

#[export] Hint Resolve ps_qs : core.

Lemma ps_qs_div n m : ~ divides (ps n) (qs m).
Proof. intros ? % prime_divides; eauto. Qed.

Lemma qs_ps_div n m : ~ divides (qs n) (ps m).
Proof. intros ? % prime_divides; eauto. Qed.

Fixpoint exp {n} (i : nat) (v : vec nat n) : nat :=
  match v with
    | vec_nil => 1
    | x##v    => qs i ^ x * exp (S i) v
  end.

Fact exp_nil i : exp i vec_nil = 1.
Proof. auto. Qed.

Fact exp_cons n i x v : @exp (S n) i (x##v) = qs i^x*exp (S i) v.
Proof. auto. Qed.

Fact exp_zero n i : @exp n i vec_zero = 1.
Proof.
  revert i; induction n as [ | n IHn ]; intros i; simpl; auto.
  rewrite IHn; ring.
Qed.

Fact exp_app n m i v w : @exp (n+m) i (vec_app v w) = exp i v * exp (n+i) w.
Proof.
  revert i; induction v as [ | x n v IHv ]; intros i.
  + rewrite vec_app_nil, exp_zero; simpl; ring.
  + rewrite vec_app_cons, exp_cons.
    simpl plus; rewrite exp_cons, IHv.
    replace (n+S i) with (S (n+i)) by lia; ring.
Qed.

Local Notation divides_mult_inv := prime_div_mult.

Lemma not_prime_1 : ~ prime 1.
Proof. intros [ [] ]; auto. Qed.

Lemma not_ps_1 n : ~ ps n = 1.
Proof.
  intros H; generalize (str_prime ps n).
  rewrite H; apply not_prime_1.
Qed. 

Lemma not_qs_1 n : ~ qs n = 1.
Proof.
  intros H; generalize (str_prime qs n).
  rewrite H; apply not_prime_1.
Qed. 

#[export] Hint Resolve not_prime_1 not_qs_1 : core.

Lemma divides_pow p n k : prime p -> divides p (n ^ k) -> divides p n.
Proof.
  induction k.
  - cbn; intros H H0 % divides_1_inv; subst; exfalso; revert H; apply not_prime_1.
  - cbn; intros ? [ | ] % divides_mult_inv; eauto.
Qed.  

Opaque ps qs.

Lemma ps_exp n m (v : vec nat m) i : ~ divides (ps n) (exp i v).
Proof.
  revert i; induction v as [ | m x v IHv ]; intros i; simpl.
  - intros H % divides_1_inv; revert H; apply not_ps_1.
  - intros [H % divides_pow | ] % divides_mult_inv; eauto.
    + now eapply ps_qs_div in H.
    + eapply IHv; eauto.
Qed.

Coercion tonat {n} := @pos2nat n.

Lemma vec_prod_div m (v : vec nat m) (u0 : nat) (p : pos m) i :
    vec_pos v p = S u0 -> qs (p + i) * exp i (vec_change v p u0) = exp i v.
Proof.
  revert p i; induction v; intros p i; analyse pos p; simpl; intros H.
  - rewrite pos2nat_fst; subst; simpl; ring.
  - rewrite pos2nat_nxt; simpl.
    rewrite <- IHv with (1 := H).
    unfold tonat.
    replace (S (pos2nat p + i)) with (pos2nat p+S i); ring.
Qed.         

Lemma qs_exp_div i j n v : i < j -> ~ divides (qs i) (@exp n j v).
Proof with eauto.
  revert i j; induction v; intros i j Hi.
  + cbn; intros ? % divides_1_inv % not_qs_1; auto.
  + cbn; intros [ H % divides_pow | H  ] % divides_mult_inv; eauto.
    * eapply primestream_divides in H; lia.
    * eapply IHv in H; eauto.
Qed.

Lemma qs_shift n m j k (v : vec nat k) :
  divides (qs n) (exp j v) <-> divides (qs (m + n)) (exp (m + j) v).
Proof.
  revert m n j; induction v as [ | x k v IHv ]; intros m n j.
  - cbn; split; intros ? % divides_1_inv % not_qs_1; tauto.
  - cbn. split.
    + intros [ | ] % divides_mult_inv; auto.
      * destruct x.
        -- cbn in H; revert H.
           intros ? % divides_1_inv % not_qs_1; tauto.
        -- eapply divides_pow in H; auto. 
           eapply primestream_divides in H as ->.
           cbn; do 2 apply divides_mult_r; apply divides_refl.
      * eapply divides_mult. 
        rewrite IHv with (m := m) in H.
        rewrite <- plus_n_Sm in H; auto.
    + intros [ | ] % divides_mult_inv; auto.
      * destruct x.
        -- cbn in H; revert H.
           intros ? % divides_1_inv % not_qs_1; tauto.
        -- eapply divides_pow in H; auto. 
           eapply primestream_divides in H.
           assert (n = j) by lia. subst.
           cbn; do 2 apply divides_mult_r; apply divides_refl.
      * eapply divides_mult. replace (S (m + j)) with (m + S j) in H by lia.
        rewrite <- IHv in H. eauto.
Qed.

Lemma vec_prod_mult m v (u : pos m) i : @exp m i (vec_change v u (1 + vec_pos v u)) = qs (u + i) * exp i v.
Proof.
  revert i; induction v; analyse pos u; intros.
  + rewrite pos2nat_fst; simpl; ring.
  + rewrite pos2nat_nxt; simpl; rewrite IHv.
    unfold tonat.
    replace (pos2nat u+S i) with (S (pos2nat u+i)) by lia; ring.
Qed.

Lemma inv_exp q p1 p2 x y : 
         q <> 0 
      -> ~ divides q p1 
      -> ~ divides q p2 
      -> q ^ x * p1 = q ^ y * p2 
      -> x = y.
Proof.
  intros H1 H2 H3 H4.
  apply power_factor_uniq in H4; tauto.
Qed.

Lemma exp_inj n i v1 v2 :
  @exp n i v1 = exp i v2 -> v1 = v2.
Proof.
  revert i v2; induction v1 as [ | x n v1 IH ]; intros i v2.
  + vec nil v2; auto.
  + vec split v2 with y.
    simpl; intros H.
    assert (forall v, ~ divides (qs i) (@exp n (S i) v)) as G.
    { intros v; apply qs_exp_div; auto. }
    apply power_factor_uniq in H; auto.
    destruct H; f_equal; subst; eauto.
Qed.

Lemma exp_inv_inc n u v1 :
  @exp n 0 (vec_change v1 u (S (vec_pos v1 u))) = qs u * exp 0 v1.
Proof.
  enough (forall i, exp i (vec_change v1 u (S (vec_pos v1 u))) = qs (i + u) * exp i v1). eapply H.
  induction v1 as [ | n x v1 IHv1 ]; analyse pos u; intros.
  + rewrite pos2nat_fst, Nat.add_0_r; cbn; ring.
  + intros; rewrite pos2nat_nxt; simpl; rewrite IHv1; unfold tonat.
    replace (S i+pos2nat u) with (i+S (pos2nat u)) by lia; ring.
Qed.
