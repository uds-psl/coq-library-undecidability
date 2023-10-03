(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* ** Prime numbers *)

Require Import List Arith Lia Bool Permutation.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list utils_nat gcd sums.

Set Implicit Arguments.

Section prime.

  Hint Resolve divides_0 divides_1 divides_mult divides_refl divides_0_inv : core.

  Infix "<d" := divides (at level 70, no associativity).

  Definition prime p := p <> 1 /\ forall q, q <d p -> q = 1 \/ q = p.

  Fact prime_divides p q : prime p -> prime q -> p <d q -> p = q.
  Proof. now intros Hp Hq [ []%Hp | ]%Hq. Qed.

  Fact prime_2 : prime 2.
  Proof. 
    split; try lia.
    apply divides_2_inv.
  Qed.

  Hint Resolve prime_2 : core.

  Fact prime_algo p : prime p <-> p = 2 \/ 3 <= p /\ ~ 2 <d p /\ forall n, 3+2*n < p -> ~ 3+2*n <d p.
  Proof.
    split.
    + intros (H1 & H2).
      destruct (le_lt_dec 3 p) as [ H | H ].
      * right; split; auto; split.
        - intros H3; apply H2 in H3; lia.
        - intros n Hn C; apply H2 in C; lia.
      * left; destruct p as [ | [ | [ | p ] ] ]; try lia.
        destruct (H2 2); try lia.
        exists 0; auto.
    + intros [ H1 | (H1 & H2 & H3) ].
      * subst; auto.
      * split; try lia.
        intros q Hq.
        destruct (euclid_2 q) as (k & [ H4 | H4 ]).
        - destruct H2; apply divides_trans with (2 := Hq).
          exists k; lia.
        - destruct k; try lia.
          destruct (le_lt_dec p (3+2*k)) as [ H5 | H5 ].
          ++ apply divides_le in Hq; lia.
          ++ destruct (H3 k); auto.
             eq goal Hq; f_equal; lia.
  Qed.

  Definition divides_bool n p := 
    match p mod n with
      | 0 => true
      | _ => false
    end.

  Fact modS_divide n p : p mod S n = 0 <-> S n <d p.
  Proof.
    unfold divides. split.
    - intros E. rewrite (Nat.div_mod_eq p (S n)). exists (p / S n). lia.
    - intros [k ->]. generalize (Nat.div_mod_eq (k * (S n)) (S n)).
      rewrite Nat.div_mul; lia.
  Qed.

  Fact divides_bool_spec n p : divides_bool (S n) p = true <-> S n <d p.
  Proof.
    unfold divides_bool.
    generalize (modS_divide n p).
    case_eq (p mod S n); try tauto.
    intros k H1 <-; split; discriminate.
  Qed.

  Fact divides_bool_spec' n p : divides_bool (S n) p = false <-> ~ S n <d p.
  Proof.
    rewrite <- divides_bool_spec.
    destruct (divides_bool (S n) p); now split.
  Qed.

  Fixpoint prime_bool_rec n p : bool := 
    match n with 
      | 0       => true
      | 1       => true
      | 2       => true 
      | S (S n') => negb (divides_bool n p) && prime_bool_rec n' p
    end.

  Fact prime_bool_rec_spec n p : n <= p -> prime_bool_rec n p = true <-> forall k, 3 <= n-2*k -> ~ n-2*k <d p.
  Proof.
    induction on n as IHn with measure n; intros Hn.
    destruct n as [ | [ | [ | n' ] ] ].
    1-3: split; try (simpl; auto; fail); intros _ k H; lia.
    unfold prime_bool_rec; fold (prime_bool_rec (S n') p).
    revert Hn; set (m := S n'); intros Hn. 
    rewrite andb_true_iff, negb_true_iff, divides_bool_spec', IHn; try lia.
    split.
    + intros (H1 & H2) [ | q ] G1 G2.
      * apply H1 in G2; auto.
      * apply (H2 q); try lia.
        eq goal G2; f_equal; lia.
    + intros H1; split.
      * apply (H1 0); lia.
      * intros k G1 G2; apply (H1 (S k)); try lia.
        eq goal G2; f_equal; lia.
  Qed.

  (* This is a somewhat naive algo. to test for primality *)

  Definition prime_bool p := 
    Nat.eqb p 2 || Nat.leb 3 p && negb (divides_bool 2 p) && prime_bool_rec (p-2) p.

  Theorem prime_bool_spec p : prime_bool p = true <-> prime p.
  Proof.
    unfold prime_bool.
    rewrite orb_true_iff, !andb_true_iff, negb_true_iff, divides_bool_spec'.
    rewrite Nat.eqb_eq, Nat.leb_le.
    split.
    + intros [ H1 | ((H1 & H2) & H3) ].
      * subst; auto.
      * split; try lia.
        destruct (euclid_2 p) as (p' & [ Hp | Hp ]).
        { destruct H2; exists p'; lia. }
        destruct p' as [ | p' ]; try (exfalso; lia).
        rewrite prime_bool_rec_spec in H3; try lia.
        intros q Hq.
        destruct (euclid_2 q) as (k & [ H4 | H4 ]).
        - destruct H2; apply divides_trans with (2 := Hq); exists k; lia.
        - destruct k as [ | k ]; try lia.
          destruct (le_lt_dec p q) as [ H5 | H5 ].
          ++ apply divides_le in Hq; lia.
          ++ assert (k < p') as H6 by lia.
             destruct (H3 (p'-S k)); try lia.
             eq goal Hq; f_equal; lia.
    + intros (H1 & H2).
      destruct (le_lt_dec 3 p) as [ H3 | H3 ].
      * right; lsplit 2; auto.
        - intros C; apply H2 in C; lia.
        - apply prime_bool_rec_spec; try lia.
          intros q H4 H5.
          apply H2 in H5; lia.
      * left; destruct p; try lia.
        destruct (H2 2); try lia.
        exists 0; auto.
  Qed.

  Fact prime_ge_2 p : prime p -> 2 <= p.
  Proof.
    destruct p as [ | [ | p ] ]; try lia.
    + intros [ _ H ]; subst.
      destruct (H 2); auto; discriminate.
    + intros [ [] _ ]; auto.
  Qed.

  Fact prime_gcd p q : prime p -> is_gcd p q 1 \/ p <d q.
  Proof.
    intros H.
    generalize (gcd p q) (gcd_spec p q); intros g Hg.
    destruct (proj2 H _ (proj1 Hg)); subst; auto.
    right; apply Hg.
  Qed.

  Fact prime_div_mult p x y : prime p -> p <d x*y -> p <d x \/ p <d y. 
  Proof.
    intros H1 H2.
    destruct (prime_gcd x H1); auto.
    right; revert H H2; apply is_rel_prime_div.
  Qed.

  Fact divides_pow p n k : prime p -> p <d n^k -> p <d n.
  Proof.
    intros Hp.
    induction k as [ | k IHk ]; simpl.
    + now intros ->%divides_1_inv.
    + intros []%prime_div_mult; auto.
  Qed.

  Definition prime_or_div p : 2 <= p -> { q | 2 <= q < p /\ q <d p } + { prime p }.
  Proof.
    intros Hp.
    destruct bounded_search with (m := S p) (P := fun n => 2 <= n < p /\ n <d p)
      as [ (q & H1 & H2) | H1 ].
    + intros n _.
      destruct (le_lt_dec p n).
      { right; intros; lia. }
      destruct (le_lt_dec 2 n).
      * destruct (divides_dec p n) as [ (?&?) | ].
        - left; subst; auto.
        - right; tauto.
      * right; lia.
    + left; exists q; split; try tauto; try lia.
    + right; split; auto.
      * lia.
      * intros q Hq.
        destruct q as [ | q]; auto.
        - apply divides_0_inv in Hq; auto.
        - assert (~ 2 <= S q < p) as H2.
          { intros H; apply (H1 (S q)); auto.
            apply le_n_S, divides_le; auto; lia. }
          apply divides_le in Hq; lia.
  Qed.

  Theorem prime_factor n : 2 <= n -> { p | prime p /\ p <d n }.
  Proof.
    induction on n as IHn with measure n; intro Hn.
    destruct (prime_or_div Hn) as [ (q & H1 & H2) | H1 ].
    2: exists n; auto.
    destruct (IHn q) as (p & H3 & H4); try lia.
    exists p; split; auto.
    now apply divides_trans with (1 := H4).
  Qed.

  Section prime_rect.

    Variables (P : nat -> Type)
              (HP0 : P 0)
              (HP1 : P 1)
              (HPp : forall p, prime p -> P p)
              (HPm : forall x y, P x -> P y -> P (x*y)).

    Theorem prime_rect n : P n.
    Proof using HP0 HP1 HPp HPm.
      induction on n as IHn with measure n.
      destruct n as [ | [ | n ] ]; auto.
      destruct (@prime_factor (S (S n))) as (p & H1 & H2); try lia.
      apply divides_div in H2.
      rewrite H2.
      apply HPm.
      + apply IHn.
        rewrite H2 at 2.
        rewrite <- Nat.mul_1_r at 1.
        apply prime_ge_2 in H1.
        apply Nat.mul_lt_mono_pos_l; lia.
      + apply HPp, H1.
    Qed.

  End prime_rect.

  Corollary no_common_prime_is_coprime x y : x <> 0 -> (forall p, prime p -> p <d x -> p <d y -> False) -> is_gcd x y 1.
  Proof.
    intros Hx H; split; [ | split ].
    + apply divides_1.
    + apply divides_1.
    + intros k H1 H2.
      destruct k as [ | [ | k ] ].
      * apply divides_0_inv in H1; lia.
      * apply divides_1.
      * destruct prime_factor with (n := S (S k)) as (p & P1 & P2); try lia.
        exfalso; apply H with p; auto; apply divides_trans with (S (S k)); auto.
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

  Fact is_rel_prime_mult p q l : is_gcd p q 1 -> is_gcd p l 1 -> is_gcd p (q*l) 1.
  Proof.
    intros H1 H2.
    destruct p as [ | p ].
    + generalize (is_gcd_fun H1 (is_gcd_0l _)) (is_gcd_fun H2 (is_gcd_0l _)).
      intros; subst; auto.
    + apply no_common_prime_is_coprime; try lia.
      do 2 (apply proj2 in H1; apply proj2 in H2).
      intros k Hk H3 H4.
      apply prime_div_mult with (1 := Hk) in H4.
      destruct H4 as [ H4 | H4 ]; 
      [ generalize (H1 _ H3 H4) 
      | generalize (H2 _ H3 H4) ];
        intro H5; apply divides_1_inv in H5; subst; 
        destruct Hk; lia.
  Qed.

  Fact is_rel_prime_expo p q l : is_gcd p q 1 -> is_gcd p (mscal mult 1 l q) 1.
  Proof.
    intros H.
    induction l as [ | l IHl ].
    + rewrite mscal_0; apply is_gcd_1r.
    + rewrite mscal_S; apply is_rel_prime_mult; auto.
  Qed.

  (* Every positive number is the product of a list of primes *)

  Notation lprod := (fold_right mult 1).

  Fact lprod_ge_1 l : Forall prime l -> 1 <= lprod l.
  Proof.
    induction 1 as [ | x l H IH ]; simpl; auto.
    change 1 with (1*1) at 1; apply Nat.mul_le_mono; auto.
    apply prime_ge_2 in H; lia.
  Qed.

  Fact lprod_app l m : lprod (l++m) = lprod l * lprod m.
  Proof. induction l; simpl; lia. Qed.

  Theorem prime_decomp n : n <> 0 -> { l | n = lprod l /\ Forall prime l }.
  Proof.
    induction on n as IHn with measure n; intro Hn.
    destruct (eq_nat_dec n 1) as [ Hn' | Hn' ].
    + exists nil; simpl; auto.
    + destruct (@prime_factor n) as (p & H1 & H2); try lia.
      apply divides_div in H2; revert H2.
      generalize (div n p); intros k Hk.
      assert (k <> 0) as Hk'.
      { intros ?; subst; destruct Hn; auto. }
      destruct (IHn k) as (l & H2 & H3); auto.
      - rewrite Hk.
        generalize (prime_ge_2 H1).
        rewrite Nat.mul_comm.
        destruct p as [ | [ | p ] ]; simpl; intros; lia.
      - exists (p::l); split; auto.
        simpl; rewrite <- H2, Nat.mul_comm; auto.
  Qed.

  Hint Resolve lprod_ge_1 prime_ge_2 : core.

  Fact prime_in_decomp p l : prime p -> Forall prime l -> p <d lprod l -> In p l.
  Proof.
    intros H1.
    induction 1 as [ | x l Hl IHl ]; simpl; intros H2.
    + apply divides_1_inv in H2; apply (proj1 H1); auto.
    + destruct (prime_gcd x H1) as [ H3 | H3 ].
      apply is_rel_prime_div with (1 := H3) in H2; auto.
      apply (proj2 Hl) in H3.
      destruct H3 as [ H3 | H3 ]; auto.
      contradict H3;apply H1.
  Qed.

  (* Prime decomposition is unique up-to permutation *) 

  Theorem prime_decomp_uniq l m : Forall prime l -> Forall prime m -> lprod l = lprod m -> l ~p m.
  Proof.
    intros H; revert H m.
    induction 1 as [ | x l Hx Hl IHl ].
    + induction 1 as [ | y m Hy Hm IHm ]; simpl; auto.
      intros C; exfalso.
      assert (2*1 <= y*lprod m) as D.
      { apply Nat.mul_le_mono; auto. }
      simpl in D; lia.
    + simpl; intros m Hm H1.
      assert (In x m) as H2.
      { apply prime_in_decomp with (1 := Hx); auto.
        exists (lprod l); rewrite Nat.mul_comm; auto. }
      apply in_split in H2.
      destruct H2 as (m1 & m2 & H2); subst.
      apply Permutation_cons_app, IHl.
      * rewrite Forall_app in Hm.
        destruct Hm as [ ? Hm ].
        inversion Hm.
        apply Forall_app; auto.
      * rewrite lprod_app.
        rewrite lprod_app in H1; simpl in H1.
        rewrite Nat.mul_assoc, (Nat.mul_comm _ x), <- Nat.mul_assoc in H1.
        apply Nat.mul_cancel_l in H1; auto.
        apply prime_ge_2 in Hx; lia.
  Qed.

End prime.

Section base_decomp.

  (* [m0;m1;...;mk] -> m0 + p*(m1+....) *)

  Fixpoint expand p l :=
    match l with
      | nil  => 0
      | x::l => x+p*expand p l
    end.

  Notation power := (mscal mult 1).

  Fact expand_app p l m : expand p (l++m) = expand p l + power (length l) p * expand p m.
  Proof.
    induction l as [ | x l IH ]; simpl; try lia.
    rewrite power_S, IH, Nat.mul_add_distr_l, Nat.mul_assoc; lia.
  Qed.

  Fact expand_0 p l : Forall (eq 0) l -> expand p l = 0.
  Proof.
    induction 1 as [ | x l H1 H2 IH2 ]; simpl; subst; auto.
    rewrite IH2, Nat.mul_comm; auto.
  Qed.

  Section base_p.

    Variables (p : nat) (Hp : 2 <= p).

    Let base_p_full n : { l | n = expand p l }.
    Proof.
      induction on n as IH with measure n.
      destruct (eq_nat_dec n 0) as [ Hn | Hn ].
      + exists nil; auto.
      + destruct (@euclid n p) as (m & r & H1 & H2); try lia.
        destruct (IH m) as (l & H3).
        * destruct m; try lia.
          rewrite H1, Nat.mul_comm.
          apply Nat.lt_le_trans with (2*S m + r); try lia.
          apply Nat.add_le_mono; auto.
          apply Nat.mul_le_mono; auto.
        * exists (r::l); simpl.
          rewrite Nat.mul_comm, Nat.add_comm, <- H3, H1; auto.
    Qed.

    Definition base_p n := proj1_sig (base_p_full n).
    Fact base_p_spec n : n = expand p (base_p n).
    Proof. apply (proj2_sig (base_p_full n)). Qed.

    Fact base_p_uniq l1 l2 : Forall2 (fun x y => x < p /\ y < p) l1 l2 -> expand p l1 = expand p l2 -> l1 = l2.
    Proof using Hp.
      induction 1 as [ | x1 x2 l1 l2 H1 H2 IH2 ]; auto; simpl; intros H3.
      rewrite (Nat.add_comm x1), (Nat.add_comm x2), (Nat.mul_comm p), (Nat.mul_comm p) in H3.
      apply div_rem_uniq in H3; try lia.
      destruct H3 as [ H3 ]; subst; f_equal; auto.
    Qed.

  End base_p.

End base_decomp.
