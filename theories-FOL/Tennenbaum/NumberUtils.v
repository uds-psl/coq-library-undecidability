Require Import Arith Lia Nat.
From Undecidability.Synthetic Require Import DecidabilityFacts.
From FOL.Tennenbaum Require Import SyntheticInType MoreDecidabilityFacts.
Notation dec_eq_nat := Nat.eq_dec.

Definition iffT (x y : Type) := prod (x->y) (y->x).
Lemma lt_rect f :
  (forall x, (forall y, y < x -> f y) -> f x) -> forall x, f x.
Proof.
  intros H x. apply H.
  induction x.
  - intros; lia. 
  - intros y Hy. apply H.
    intros z Hz. apply IHx. lia.
Defined.



(** * Division with Rest *)

Definition Euclid d x :
  { q & { r &  x = q*d + r  /\  (0 < d -> r < d)  }}.
Proof.
  destruct d as [|d].
  exists 0, x. repeat split; lia.
  induction x as [|x IH].
  - exists 0, 0. repeat split; lia.
  - destruct IH as (q&r&[]).
    specialize (dec_eq_nat d r) as [].
    + exists (S q), 0. split; lia.
    + exists q, (S r). split; lia.
Defined.


(* Div y x gives the number of times y can be substracted from x *)
Definition Div y x := projT1 (Euclid y x).
(* Mod y x gives the remainder of x after division by y *)
Definition Mod y x := projT1 (projT2 (Euclid y x)).



Fact Factor y x : 
  x = (Div y x)*y + Mod y x.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.


Fact Mod_bound y x : 
  0 < y -> Mod y x < y.
Proof.
  apply (projT2 (projT2 (Euclid _ _))).
Qed.



Fact Mod_lt y x : 
  0 < y <= x -> Mod y x < x.
Proof.
  intros [H ].
  apply (Mod_bound _ x) in H. lia.
Qed.


Lemma Div_lt y x : 
  0 < y <= x -> 0 < Div y x.
Proof.
  intros [H1 H2].
  rewrite (Factor y x) in H2 at 1.
  specialize ((Mod_bound y x) H1) as H3.
  enough (Div y x <> 0) by lia.
  intros E. rewrite E in *; cbn in *.
  lia.
Qed.


(** Uniqueness *)
  
Section Uniqueness.

  Variable m : nat.


  Lemma Fac_unique a1 b1 a2 b2 : b1 < m -> b2 < m ->
    a1*m + b1 = a2*m + b2 -> a1 = a2 /\ b1 = b2.
  Proof.
    intros.
    destruct (Nat.lt_trichotomy a1 a2) as [ |[]]; nia.
  Qed.


  Theorem unique x a b : b < m ->
    x = a*m + b <-> Div m x = a /\ Mod m x = b.
  Proof.
    split.
    - rewrite (Factor m x) at 1. intros.
      specialize (Mod_bound m x) as ?.
      apply Fac_unique; lia.
    - intros [<- <-]. apply Factor.
  Qed.
  
  
  Corollary Fac_eq a b : b < m ->
      Div m (a*m + b) = a /\ Mod m (a*m + b) = b.
  Proof. intros. now apply (unique _). Qed.


End Uniqueness.



Lemma lt_nat_equiv x y : 
  x < y <-> exists k, S x + k = y.
Proof.
  split. 
  induction y in x |-*. lia.
  destruct x; intros. exists y; lia.
  destruct (IHy x) as [k <-]. lia.
  exists k; lia.
  intros []. lia.
Qed.

Lemma Mod_divides y x : 
  iffT (Mod y x = 0) ({ k & x = k*y }).
Proof.
  split.
  - intros H. exists (Div y x). rewrite plus_n_O. rewrite <- H. apply Factor.
  - intros [k ->]. destruct y. cbn. lia.
    assert (0 < S y) as [? H]%(Fac_eq _ k) by lia. now rewrite <- plus_n_O in H.
Qed.

Lemma Mod_le x N : 
  N > 0 -> Mod x N = 0 -> x <= N.
Proof.
  intros ? [k ?]%Mod_divides. assert (k > 0) by lia. nia.
Qed.

Fact Mod_id m x : x < m -> Mod m x = x.
Proof.
  intros H.
  apply (Fac_eq m 0 x H).
Qed.


(** Homomorphism property of the modulus. *)

Section Homomorphism.

  Variable m : nat.
  Local Notation "'M' x" := (Mod m x) (at level 10).
  Local Notation "'D' x" := (Div m x) (at level 10).
  

  Lemma Mod_plus_multiple d r : 
    M (d*m + r) = M r.
  Proof.
    assert (m = 0 \/ 0 < m) as [->|] by lia; cbn. lia.
    eapply (Fac_unique m _ _ (d + D r)).
    all: try now apply Mod_bound.
    rewrite <-Factor.
    rewrite (Factor m r) at 1. lia.
  Qed.


  Theorem Mod_add_hom x y: 
    M (x + y) = M (M x + M y).
  Proof.
    symmetry.
    rewrite <-(Mod_plus_multiple (D x + D y)).
    rewrite (Factor m x), (Factor m y) at 3.
    f_equal. lia.
  Qed.


  Lemma Mod_mult_hom_l x y : 
    M (x * y) = M (M x * y).
  Proof.
    symmetry.
    erewrite <-(Mod_plus_multiple (D x * y)).
    rewrite (Factor m x) at 3.
    f_equal. lia.
  Qed.


  Theorem Mod_mult_hom x y:
    M (x * y) = M (M x * M y).
  Proof.
    symmetry.
    erewrite <-(Mod_plus_multiple (D x * D y * m + D x * M y + D y * M x )).
    rewrite (Factor m x), (Factor m y) at 5.
    f_equal. lia.
  Qed.

  Fact Mod0_is_0 : M 0 = 0.
  Proof. destruct m; reflexivity. Qed.

  Corollary ModMod_is_Mod x : 
    M (M x) = M x.
  Proof.
    change (M x) with (0 + M x) at 1. 
    now rewrite <-Mod0_is_0, <-Mod_add_hom.
  Qed.


End Homomorphism.



(** * Prime Numbers *)

Section PrimeDec.

  (** Irreducible Numbers *)

  Definition irred' p := p > 1 /\ forall n, Mod n p = 0 -> (n = 1) \/ (n = p).

  Lemma irred_bounded p : (p > 1 /\ forall n, n < p -> Mod n p = 0 -> (n = 1) \/ (n = p) ) <-> irred' p.
  Proof.
    split.
    - intros [? H]. split. assumption.
      intros. enough (n < p \/ n = p) as [ | ->].
      apply H. all : auto.
      enough (n <= p) by lia.
      apply Mod_le; lia.
    - unfold irred'. intuition.
  Qed.


  Definition irred p := p > 1 /\ forall n, n < p -> Mod n p = 0 -> n = 1.

  Goal forall p, irred p <-> irred' p.
  Proof.
    unfold irred, irred'.
    setoid_rewrite <-irred_bounded.
    intuition. destruct (H1 _ H H2).
    auto. lia.
  Qed.


  (** It is decidable whether a number is irreducible. *)
  Lemma Dec_sigT_irred : 
    Dec_sigT (irred).
  Proof.
    intros n. unfold irred. apply Dec.and_dec. apply lt_dec.
    apply dec_lt_bounded_forall.
    intros x. apply impl_dec; apply dec_eq_nat.
  Defined.


  Lemma irred1 N : 
    irred N + (N > 1 -> {x & x < N /\ Mod x N = 0 /\ x <> 1}).
  Proof.
    destruct (Dec_sigT_irred N) as [|H]; auto.
    right. intros HN. apply Witnessing_nat. 
    intros x. apply and_dec; eauto. apply lt_dec.
    unfold irred in *.
    apply dec_DM_and in H.
    - destruct H. tauto.
      apply neg_lt_bounded_forall in H.
      destruct H as [n []].
      exists n. split. tauto.
      apply dec_DM_impl in H0; eauto. intros x.
      apply impl_dec; apply dec_eq_nat.
    - apply lt_dec.
    - apply dec_lt_bounded_forall.
      intros n. apply impl_dec; eauto.
  Qed.

  Lemma dec_irred_factor N : 
    irred N + (N > 1 -> {x & {y & 1 < x < N  /\ x*y = N }} ).
  Proof.
    destruct (irred1 N) as [| H]; auto.
    right. intros [x Hx]%H.
    destruct Hx as (?&[y Hy]%Mod_divides&?).
    exists x, y. nia.
  Qed.

  (** Every number > 1 has an irreducible factor. *)
  
  Lemma irred_factor n : 
    n > 1 -> { k | irred k /\ Mod k n = 0}.
  Proof.
    pattern n. apply lt_rect. intros N IH HN.
    destruct (dec_irred_factor N) as [|H].
    - exists N. split. auto.
      apply Mod_divides. exists 1; lia.
    - destruct (H HN) as [x [y ((H1&H2)&H3) ]].
      assert (x > 1) by nia.
      destruct (IH x H2 H1) as [k Hk].
      exists k. split. tauto.
      rewrite <-H3. rewrite Mod_mult_hom, (proj2 Hk).
      apply Mod0_is_0.
  Qed.


  Lemma irred_Mod_eq m x : 
    irred x -> m > 1 -> Mod m x = 0 -> m = x.
  Proof.
    intros Hx Hm Eq.
    enough (m < x \/ m = x) as []; auto.
    apply Hx in H; intuition lia.
    apply Mod_le in Eq; try lia.
    unfold irred in *; lia.
  Qed.


   Lemma irred_integral_domain n a b : 
    irred n -> Mod n (a*b) = 0 -> Mod n a = 0 \/ Mod n b = 0.
  Proof.
    intros irred_n.
    induction a as [a Hrec] using lt_rect.
    intros Eq.
    assert (n <= a \/ a < n) as [] by lia.
    - rewrite <-ModMod_is_Mod.
      apply Hrec. apply Mod_lt. split.
      enough (n > 1) by lia. apply irred_n.
      lia. now rewrite <-Mod_mult_hom_l.
    - assert (a = 0 \/ a > 0) as [-> |] by lia.
      rewrite Mod0_is_0; auto.
      edestruct (Hrec (Mod a n)).
      now apply Mod_bound.
      3 : right; apply H1.
      cut (Mod n (n * b) = 0).
      rewrite (Factor a n) at 2.
      rewrite Nat.mul_add_distr_r.
      rewrite Mod_add_hom, <- Nat.mul_assoc, Mod_mult_hom.
      now rewrite Eq, Nat.mul_0_r, <- Mod_add_hom.
      rewrite Nat.mul_comm, <-(Nat.add_0_r (_ * _)).
      now rewrite Mod_plus_multiple, Mod0_is_0.
      enough (Mod a n = 0) as E.
      apply irred_n in E. 
      rewrite E, Nat.mul_1_l in Eq. all: auto.
      rewrite Mod_id in H1. auto.
      apply Mod_lt. lia.
  Qed.
  
  


  Definition prime p := p > 1 /\ forall a b, Mod p (a*b) = 0 -> Mod p a = 0 \/ Mod p b = 0.

  (** Prime and irreducible are equivalent *)
  
  Lemma prime_irred_equiv p : irred p <-> prime p.
  Proof.
    split; intros [? H]; split; auto.
    - intros a b Hab. apply irred_integral_domain.
      unfold irred; auto. assumption.
    - intros n H1 H2. 
      destruct (fst (Mod_divides _ _) H2) as [k Hk].
      destruct (H k n).
      + rewrite <-Hk. apply Mod_divides. exists 1. now cbn.
      + destruct (fst (Mod_divides _ _) H3) as [? ->].
        assert (p*(x*n) = p*1) as ?%Nat.mul_cancel_l by lia.
        apply Nat.mul_eq_1 in H4. all: lia.
      + apply Mod_le in H3. all: lia.
  Qed.


  Corollary Dec_sigT_prime : 
    Dec_sigT (prime).
  Proof.
    refine (Dec_sigT_transport _ _ Dec_sigT_irred prime_irred_equiv).
  Qed.


End PrimeDec.




Section PrimeInf.


  Fixpoint faktorial n :=
    match n with
    | 0 => 1
    | S x => (faktorial x)*n
    end.

  Notation "x !" := (faktorial x) (at level 2).


  Fact fac1 : forall n, 0 < n!.
  Proof. induction n; cbn; lia. Qed.

  Fact fac2 : forall n, 0 < n -> Mod n (n !) = 0.
  Proof.
    intros n H. destruct n; try lia.
    apply Mod_divides. exists (n !). 
    reflexivity.
  Qed.

  Lemma fac3 : forall x y, 0 < y <= x -> Mod y (x!) = 0.
  Proof.
    intros x y H.
    induction x in y, H |-*.
    - lia.
    - assert (y = S x \/ y <= x) as [<-|] by lia; cbn.
      now apply fac2.
      rewrite Mod_mult_hom, IHx.
      apply Mod0_is_0. lia.
  Qed.

  (** There are infinitely many irreducible numbers. *)

  Lemma infty_irred : forall N, { p & N < p /\ irred p}.
  Proof.
    intros n.
    destruct (irred_factor (n! + 1)) as [k [[] ]].
    specialize(fac1 n). lia.
    exists k. split.
    - rewrite Mod_add_hom in *.
      assert (n < k <-> ~ (k <= n)) as G by lia.
      apply G. intros ?.
      enough (1 = 0) by lia.
      rewrite <-H1 at 2.
      rewrite fac3. 2: lia. 
      cbn; rewrite ModMod_is_Mod.
      symmetry. refine ( proj2 (Fac_eq _ 0 _ _)); lia.
    - unfold irred. tauto.
  Defined.

  (** An injective function producing infinitely many irreducible numbers. *)

  Fixpoint Irred n := match n with
                      | 0 => projT1 (infty_irred 0)
                      | S x => projT1 (infty_irred (Irred x))
                      end.


  Lemma mono_inj f : (forall x,  f x < f (S x)) -> inj f.
  Proof.
    intros Hf.
    assert (H : forall n x, x < n -> f x < f n).
    induction n.
    - lia.
    - intros x. 
      assert (x < S n <-> x < n \/ x = n) as -> by lia.
      intros [| ->].
      + specialize (Hf n). specialize (IHn _ H). lia.
      + apply Hf.
    - intros x y eq.
      destruct (dec_eq_nat x y); auto.
      assert (x < y \/ y < x) as [G|G] by lia.
      all: specialize (H _ _ G); lia.
  Qed.

  
  Lemma inj_Irred : inj Irred.
  Proof.
    apply mono_inj.
    intros x.
    apply (proj1 (projT2 (infty_irred (Irred x)))).
  Qed.

  Lemma irred_Irred x : irred (Irred x).
  Proof.
    destruct x; apply (projT2 (infty_irred _)).
  Qed.
  
  
End PrimeInf.