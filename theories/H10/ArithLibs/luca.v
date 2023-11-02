(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* ** Luca's theorem *)

Require Import Arith Nat Lia List.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac gcd prime binomial sums rel_iter.

From Undecidability.H10.ArithLibs 
  Require Import Zp.

Set Implicit Arguments.

Local Notation power := (mscal mult 1).
Local Notation expo := (mscal mult 1).

Section fact.

  Let factorial_cancel n a b : fact n * a = fact n * b -> a = b.
  Proof.
    apply Nat.mul_cancel_l.
    generalize (fact_gt_0 n); intro; lia.
  Qed.
  
  Notation Π := (msum mult 1).

  Notation mprod_an := (fun a n => Π n (fun i => i+a)).

  Fact mprod_factorial n : fact n = mprod_an 1 n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite msum_0; auto.
    + rewrite msum_plus1; auto.
      rewrite Nat.mul_comm, <- IHn, fact_S.
      f_equal; lia.
  Qed.

  Variable (p : nat) (Hp : p <> 0).

  Notation "〚 x 〛" := (nat2Zp Hp x).

  Let expo_p_cancel n a b : expo n p * a = expo n p * b -> a = b.
  Proof.
    apply Nat.mul_cancel_l.
    generalize (power_ge_1 n Hp); intros; lia.
  Qed.

  Fact mprod_factorial_Zp i n :〚mprod_an (i*p+1) n〛=〚fact n〛.
  Proof.
    rewrite mprod_factorial.
    induction n as [ | n IHn ].
    + do 2 rewrite msum_0; auto.
    + do 2 (rewrite msum_plus1; auto).
      do 2 rewrite nat2Zp_mult; f_equal; auto.
      apply nat2Zp_inj.
      rewrite (Nat.add_comm n), <- Nat.add_assoc, Nat.add_comm.
      rewrite <- rem_plus_div; auto.
      * f_equal; lia.
      * apply divides_mult, divides_refl.
  Qed.

  Notation φ := (fun n r => mprod_an (n*p+1) r).
  Notation Ψ := (fun n => Π n (fun i => mprod_an (i*p+1) (p-1))).

  Let phi_Zp_eq n r :〚φ n r〛=〚fact r〛.
  Proof. apply mprod_factorial_Zp. Qed.

  Fact mprod_factorial_mult n : fact (n*p) = expo n p * fact n * Ψ n.
  Proof using Hp.
    induction n as [ | n IHn ].
    + rewrite Nat.mul_0_l, msum_0, mscal_0, fact_0; auto.
    + replace (S n*p) with (n*p+p) by ring.
      rewrite mprod_factorial, msum_plus, <- mprod_factorial; auto.
      replace p with (S (p-1)) at 2 by lia.
      rewrite msum_plus1; auto.
      rewrite <- Nat.add_assoc.
      replace (p-1+1) with p by lia.
      replace (n*p+p) with ((S n)*p) by ring.
      rewrite mscal_S, fact_S, msum_S.
      rewrite IHn.
      repeat rewrite Nat.mul_assoc.
      rewrite (Nat.mul_comm _ p).
      repeat rewrite <- Nat.mul_assoc.
      do 2 f_equal.
      rewrite (Nat.mul_comm (S n)).
      repeat rewrite <- Nat.mul_assoc; f_equal.
      repeat rewrite Nat.mul_assoc; f_equal.
      rewrite msum_ext with (f := fun i => n*p+i+1)
                            (g := fun i => i+(n*p+1)).
      2: intros; ring. 
      rewrite <- msum_plus1; auto.
  Qed.
 
  Lemma mprod_factorial_euclid n r : fact (n*p+r) = expo n p * fact n * φ n r * Ψ n.
  Proof using Hp.
    rewrite mprod_factorial, msum_plus; auto.
    rewrite <- mprod_factorial.
    rewrite msum_ext with (f := fun i => n*p+i+1)
                          (g := fun i => i+(n*p+1)).
    2: intros; ring. 
    rewrite mprod_factorial_mult; auto; ring.
  Qed.

  Notation Zp := (Zp_zero Hp).
  Notation Op := (Zp_one Hp).
  Notation "∸" := (Zp_opp Hp).
  Infix "⊗" := (Zp_mult Hp) (at level 40, left associativity).
  Notation expoZp := (mscal (Zp_mult Hp) (Zp_one Hp)).

  Hint Resolve Nat_mult_monoid : core.

  Let Psi_Zp_eq n :〚Ψ n〛= expoZp n〚fact (p-1)〛.
  Proof.
    induction n as [ | n IHn ].
    + rewrite msum_0, mscal_0; auto.
    + rewrite msum_plus1, nat2Zp_mult.
      rewrite mscal_plus1; auto.
      2: apply Zp_mult_monoid.
      2: apply Nat_mult_monoid.
      f_equal; auto.
  Qed.

  Hypothesis (Hprime : prime p).

  Let phi_Zp_invertible n r : r < p -> Zp_invertible Hp 〚φ n r〛.
  Proof.
    intros H; simpl; rewrite phi_Zp_eq.
    apply Zp_invertible_factorial; auto.
  Qed.

  Let Psi_Zp_invertible n : Zp_invertible Hp 〚Ψ n〛.
  Proof.
    simpl; rewrite (Psi_Zp_eq n).
    apply Zp_expo_invertible, Zp_invertible_factorial; auto; lia.
  Qed.

  (* rewrite the binomial theorem

               fact k * fact (n-k) * binomial n k = fact n   

      when      

         k = K*p + k0
         n = N*p + n0

      with
       
      1)  K <= N & k0 <= n0
   
      we get n-k = (N-K)*p + (n0-k0) and

        expo K     p * fact K     * φ K      k0     * Ψ K
      .* expo (N-K) p * fact (N-K) * φ (N-K) (n0-k0) * Ψ (N-K)
      .* binomial n k 
      = expo N p     * fact N     * φ N      n0     * Ψ N.

      hence, simplifying by expo N p  we get

        fact K * fact (N-K) * φ K k0 * Ψ K * φ (N-K) (n0-k0) * Ψ (N-K) * binomial n k = fact N * φ N n0 * Ψ N. 

      then in Z/Zp we derive (modulo Wilson's theorem, unnecessary here〚fact (p-1)〛=〚-1〛) 

       〚fact K〛⊗〚fact (N-K)〛⊗〚fact k0〛⊗〚-1〛^K⊗〚fact (n0-k0)〛⊗〚-1〛^(N-K)⊗〚binomial n k〛
      =〚fact N〛⊗〚fact n0〛⊗〚-1〛^N

        that we combine with 〚fact K〛⊗〚fact (N-K)〛⊗〚binomial N K〛=〚fact N〛
                        and  〚fact k0〛⊗〚fact (n0-k0)〛⊗〚binomial n0 k0〛=〚fact n0〛

        to derive the result:〚binomial n k 〛=〚binomial N K〛⊗〚binomial n0 k0〛

      with 
 
      2) K < N & n0 < k0

      we have n-k = (N-(K+1))*p + (p-(k0-n0)) and

        expo K         p * fact K         * φ K          k0         * Ψ K
      .* expo (N-(K+1)) p * fact (N-(K+1)) * φ (N-(K+1)) (p-(k0-n0)) * Ψ (N-(K+1))
      .* binomial n k 
      = expo N p     * fact N     * φ N      n0     * Ψ N.

      hence
 
         fact K * φ K k0 * Ψ K * fact (N-(K+1)) * φ (N-(K+1)) (p-(k0-n0)) * Ψ (N-(K+1)) * binomial n k 
       = p * ....

      then in Z/Zp all the left factor are invertible except binomial n k which must thus be〚0〛 *)

  Section binomial_without_p_not_zero.

    Variable (n N n0 k K k0 : nat) (Hn : n = N*p+n0) (Hk : k = K*p+k0) (H1 : K <= N) (H2 : k0 <= n0).

    Let Hkn : k <= n.
    Proof.
      rewrite Hn, Hk.
      replace N with (K+(N-K)) by lia.
      rewrite Nat.mul_add_distr_r.
      generalize ((N-K)*p); intros; lia.
    Qed.
   
    Let Hnk : n - k = (N-K)*p+(n0-k0).
    Proof.
      rewrite Hn, Hk, Nat.mul_sub_distr_r.
      cut (K*p <= N*p).
      + generalize (K*p) (N*p); intros; lia.
      + apply Nat.mul_le_mono; auto.
    Qed.
  
    Fact binomial_wo_p : φ K k0 * Ψ K * φ (N-K) (n0-k0) * Ψ (N-K) * binomial n k 
                       = binomial N K * φ N n0 * Ψ N.
    Proof using Hkn.
      apply (factorial_cancel (N-K)); repeat rewrite Nat.mul_assoc.
      rewrite (Nat.mul_comm (fact _) (binomial _ _)).
      apply (factorial_cancel K); repeat rewrite Nat.mul_assoc.
      rewrite (Nat.mul_comm (fact _) (binomial _ _)).
      rewrite <- binomial_thm; auto.
      apply expo_p_cancel with N.
      repeat rewrite Nat.mul_assoc.
      rewrite <- mprod_factorial_euclid, <- Hn.
      rewrite binomial_thm with (1 := Hkn).
      rewrite Hnk. 
      rewrite Hk at 3.
      replace N with (K+(N-K)) at 1 by lia.
      rewrite power_plus.
      do 2 rewrite mprod_factorial_euclid.
      ring.
    Qed.

    Hypothesis (Hn0 : n0 < p).

    Hint Resolve Zp_mult_monoid : core.

    Fact binomial_Zp_prod :〚binomial n k〛=〚binomial N K〛⊗〚binomial n0 k0〛.
    Proof using Hkn Hn0 Hprime.
      generalize binomial_wo_p; intros G.
      apply f_equal with (f := nat2Zp Hp) in G.
      repeat rewrite nat2Zp_mult in G.
      repeat rewrite Psi_Zp_eq in G.
      repeat rewrite phi_Zp_eq in G.
      rewrite binomial_thm with (1 := H2) in G.
      repeat rewrite nat2Zp_mult in G.
      rewrite (Zp_mul_comm _ _〚 fact k0 〛) in G.
      repeat rewrite Zp_mul_assoc in G.
      rewrite (Zp_mul_comm _ _〚 fact k0 〛) in G.
      repeat rewrite <- Zp_mul_assoc in G.
      apply Zp_invertible_cancel_l in G.
      2: apply Zp_invertible_factorial; auto; lia.
      repeat rewrite Zp_mul_assoc in G.
      do 2 rewrite (Zp_mul_comm _ _〚 fact _ 〛) in G.
      repeat rewrite <- Zp_mul_assoc in G.
      apply Zp_invertible_cancel_l in G.
      2: apply Zp_invertible_factorial; auto; lia.
      repeat rewrite Zp_mul_assoc in G.
      rewrite <- mscal_plus in G; auto.
      replace (K+(N-K)) with N in G by lia.
      rewrite (Zp_mul_comm _ _ (expoZp _ _)) in G.
      apply Zp_invertible_cancel_l in G; trivial.
      apply Zp_expo_invertible, Zp_invertible_factorial; auto; lia.
    Qed.

  End binomial_without_p_not_zero.

  Section binomial_without_p_zero.

    Variable (n N n0 k K k0 : nat) (Hn : n = N*p+n0) (Hk : k = K*p+k0) 
             (H1 : K < N) (H2 : n0 < k0) (Hk0 : k0 < p).

    Let H3 : p - (k0-n0) < p.    Proof. lia. Qed.
    Let H4 : S (N-1) = N.        Proof. lia. Qed.
    Let H5 : N-1 = K+(N-(K+1)).  Proof. lia. Qed.
    Let H6 : N = K+1+(N-(K+1)).  Proof. lia. Qed.
    Let HNK : N-K = S (N-(K+1)). Proof. lia. Qed.

    Let Hkn : k <= n.
    Proof.
      rewrite Hn, Hk, H6.
      do 2 rewrite Nat.mul_add_distr_r.
      generalize ((N-(K+1))*p); clear H3 H4 H5 H6 HNK; intros; lia.
    Qed.
   
    Let Hnk : n - k = (N-(K+1))*p+(p-(k0-n0)).
    Proof.
      rewrite Hn, Hk, Nat.mul_sub_distr_r.
      cut ((K+1)*p <= N*p).
      + rewrite Nat.mul_add_distr_r.
        generalize (K*p) (N*p); clear H3 H4 H5 H6 HNK Hkn; intros; lia.
      + apply Nat.mul_le_mono; auto; clear H3 H4 H5 H6 HNK Hkn; lia.
    Qed.

    Fact binomial_with_p : fact K * fact (N-(K+1)) * φ K k0 * Ψ K * φ (N-(K+1)) (p-(k0-n0)) * Ψ (N-(K+1)) * binomial n k 
                         = p * fact N * φ N n0 * Ψ N.
    Proof using Hkn.
      apply expo_p_cancel with (N-1).
      repeat rewrite Nat.mul_assoc.
      rewrite (Nat.mul_comm (expo _ _) p).
      rewrite <- mscal_S.
      rewrite H4, <- mprod_factorial_euclid, <- Hn.
      rewrite binomial_thm with (1 := Hkn).
      rewrite Hnk.
      rewrite Hk at 3.
      do 2 rewrite mprod_factorial_euclid.
      rewrite H5 at 1.
      rewrite power_plus.
      ring.
    Qed.

    Fact binomial_with_p' : φ K k0 * Ψ K * φ (N-(K+1)) (p-(k0-n0)) * Ψ (N-(K+1)) * binomial n k 
                          = p * binomial N K * (N-K) * φ N n0 * Ψ N.
    Proof using Hkn.
      apply (factorial_cancel (N-(K+1))); repeat rewrite Nat.mul_assoc.
      apply (factorial_cancel K); repeat rewrite Nat.mul_assoc.
      rewrite binomial_with_p.
      rewrite binomial_thm with (n := N) (p := K).
      2: { apply Nat.lt_le_incl; auto. }
      rewrite HNK at 1.
      rewrite fact_S.
      rewrite <- HNK.
      ring.
    Qed.
 
    Fact binomial_Zp_zero :〚binomial n k〛= Zp.
    Proof using Hkn Hprime.
      generalize binomial_with_p'; intros G.
      apply f_equal with (f := nat2Zp Hp) in G.
      repeat rewrite nat2Zp_mult in G.
      rewrite nat2Zp_p in G.
      repeat rewrite Zp_mult_zero in G.
      apply Zp_invertible_eq_zero in G; auto.
      repeat (apply Zp_mult_invertible; auto).
    Qed.

  End binomial_without_p_zero.

End fact.

Section lucas_lemma.

  (* https://math.stackexchange.com/questions/1463758/proof-of-lucas-theorem-without-the-polynomial-hint *)

  Variables (p : nat) (Hprime : prime p).

  Let Hp : p <> 0.
  Proof.
    generalize (prime_ge_2 Hprime); intro; lia.
  Qed.

  Variables (n N n0 k K k0 : nat)
            (G1 : n = N*p+n0)  (G2 : n0 < p)
            (G3 : k = K*p+k0)  (G4 : k0 < p).

  Let choice : (K <= N  /\ k0 <= n0)
            \/ (n0 < k0 /\ K < N)
            \/ ((n0 < k0 \/ N < K) /\ n < k).
  Proof.
    destruct (le_lt_dec k n) as [ H0 | H0 ];
    destruct (le_lt_dec k0 n0) as [ H1 | H1 ];
    destruct (le_lt_dec K N) as [ H2 | H2 ]; try lia.
    + do 2 right; split; auto.
      rewrite G1, G3.
      replace K with (N+1+(K-N-1)) by lia.
      do 2 rewrite Nat.mul_add_distr_r.
      generalize ((K-N-1)*p); intros; lia.
    + destruct (eq_nat_dec N K); try lia.
    + do 2 right; split; auto.
      rewrite G1, G3.
      replace K with (N+1+(K-N-1)) by lia.
      do 2 rewrite Nat.mul_add_distr_r.
      generalize ((K-N-1)*p); intros; lia.
  Qed.

  Theorem lucas_lemma : rem (binomial n k) p = rem (binomial N K * binomial n0 k0) p.
  Proof using choice.
    destruct choice as [ (H1 & H2) 
                     | [ (H1 & H2)
                       | (H1 & H2) ] ]; clear choice.
    3: { rewrite binomial_gt with (1 := H2).
         f_equal.
         destruct H1 as [ H1 | H1 ]; 
           rewrite binomial_gt with (1 := H1); ring. }
    + apply nat2Zp_inj with (Hp := Hp).
      rewrite nat2Zp_mult.
      apply binomial_Zp_prod; auto.
    + rewrite binomial_gt with (1 := H1).
      rewrite Nat.mul_0_r.
      apply nat2Zp_inj with (Hp := Hp).
      rewrite nat2Zp_zero.
      apply binomial_Zp_zero with (2 := G1) (3 := G3); auto.
  Qed.

End lucas_lemma.

(* Eval compute in binomial 3 0. *)

Section lucas_theorem.

  Variable (p : nat) (Hp : prime p).

  Implicit Types (l m : list nat).

  (* base_p [x0;x1;x2;...] =  x0 + x1*p + x2*p² ...*)

  Notation base_p := (expand p).

  Fixpoint binomial_p l :=
    match l with
      | nil  => fix loop m := match m with
        | nil  => 1
        | y::m => binomial 0 y * loop m
      end
      | x::l => fun m => match m with
        | nil   => binomial x 0 * binomial_p l nil 
        | y::m  => binomial x y * binomial_p l m
      end
    end.

  Fact binomial_p_fix00 : binomial_p nil nil = 1.
  Proof. auto. Qed.

  Fact binomial_p_fix01 y m : binomial_p nil (y::m) = binomial 0 y * binomial_p nil m.
  Proof. auto. Qed.

  Fact binomial_p_fix10 x l : binomial_p (x::l) nil = binomial x 0 * binomial_p l nil.
  Proof. auto. Qed.

  Fact binomial_p_fix11 x l y m : binomial_p (x::l) (y::m) = binomial x y * binomial_p l m.
  Proof. auto. Qed.

  (* This is Luca's thm as described eg on Wikipedia

      if p is prime
      and x = x0 + x1*p + x2*p² ...
      and y = y0 + y1*p + y2*p² ...

      then the identity 
 
         binomial x y = binomial x0 y0 * binomial x1 y1 * binomial x2 y2 * ...

      holds modulo p

   *)

  Theorem lucas_theorem (l m : list nat) : 
         Forall (fun i => i < p) l               (* digits must be less than p*)
      -> Forall (fun i => i < p) m               (* digits must be less than p*)
      -> rem (binomial (base_p l) (base_p m)) p 
       = rem (binomial_p l m) p.
  Proof using Hp.
    intros H; revert H m.
    induction 1 as [ | x l H1 H2 IH2 ];
    induction 1 as [ | y m H3 H4 IH4 ].
    + simpl; auto.
    + rewrite binomial_p_fix01; simpl base_p.
      rewrite <- rem_mult_rem, <- IH4, rem_mult_rem, 
              (Nat.mul_comm p), Nat.add_comm, (Nat.mul_comm (binomial _ _)).
      apply lucas_lemma; auto; simpl; lia.
    + rewrite binomial_p_fix10; simpl base_p.
      rewrite <- rem_mult_rem, <- IH2, rem_mult_rem; auto.
      rewrite (Nat.mul_comm p), Nat.add_comm, (Nat.mul_comm (binomial _ _)).
      apply lucas_lemma; auto; simpl; lia.
    + rewrite binomial_p_fix11; simpl base_p.
      rewrite <- rem_mult_rem, <- IH2, rem_mult_rem; auto.
      rewrite !(Nat.mul_comm p), !(Nat.add_comm _ (_ * _)), (Nat.mul_comm (binomial _ _)).
      apply lucas_lemma; auto; simpl; lia.
  Qed.

End lucas_theorem.

(* Check lucas_theorem. *)
