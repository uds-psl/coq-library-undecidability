(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Max Lia Wellfounded Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import list_focus utils_tac utils_list utils_nat.

Set Implicit Arguments.

(* We show that unbounded decidable predicates are exactly
    the direct images of strictly increasing sequences nat -> nat 

    Hence, this gives an easy construction of the sequence
    of all primes ...

*)

Section list_choose_d.

  Variable (X : Type) (P Q : X -> Prop).

  Theorem list_choose_d l : (forall x, In x l -> P x \/ Q x)
                           -> (exists x, In x l /\ P x)
                           \/ forall x, In x l -> Q x.
  Proof.
    induction l as [ | x l IHl ]; intros Hl.
    + right; intros _ [].
    + destruct (Hl x) as [ H1 | H1 ].
      * left; auto.
      * left; exists x; simpl; auto.
      * destruct IHl as [ (y & H2 & H3) | H2 ].
        - intros; apply Hl; right; auto.
        - left; exists y; simpl; auto.
        - right; intros ? [ <- | ]; auto.
  Qed.

End list_choose_d.

Section bounded_choose_d.

  Variable (P Q : nat -> Prop).

  Theorem bounded_choose_d n : (forall x, x < n -> P x \/ Q x)
                           -> (exists x, x < n /\ P x)
                           \/ forall x, x < n -> Q x.
  Proof.
    intros H.
    destruct list_choose_d with (P := P) (Q := Q) (l := list_an 0 n)
      as [ (x & H1 & H2) | H1 ].
    + intro; rewrite list_an_spec; intro; apply H; lia.
    + left; exists x; split; auto.
      apply list_an_spec in H1; lia.
    + right; intros x Hx; apply H1, list_an_spec; lia.
  Qed. 

End bounded_choose_d.

Section bounded_min.

  Variable (P Q : nat -> Prop).

  Theorem bounded_min_d n :   (forall x, x < n -> P x \/ Q x)
                           -> (exists x, x < n /\ P x /\ forall y, y < x -> Q y)
                           \/ forall x, x < n -> Q x.
  Proof.
    induction n as [ | n IHn ]; intros Hn.
    + right; intros; lia.
    + destruct IHn as [ (x & H1 & H2 & H3) | H1 ].
      * intros; apply Hn; lia.
      * left; exists x; msplit 2; auto; lia.
      * destruct (Hn n); auto.
        - left; exists n; msplit 2; auto.
        - right; intros x Hx.
          destruct (eq_nat_dec x n); subst; auto.
          apply H1; lia.
  Qed.

End bounded_min.

Section list_choose_dep.

  Variable (X : Type) (P Q : X -> Prop).

  Theorem list_choose_dep l : (forall x, In x l -> { P x } + { Q x })
                           -> { x | In x l /\ P x }
                            + { forall x, In x l -> Q x }.
  Proof.
    induction l as [ | x l IHl ]; intros Hl.
    + right; intros _ [].
    + destruct (Hl x) as [ H1 | H1 ].
      * left; auto.
      * left; exists x; simpl; auto.
      * destruct IHl as [ (y & H2 & H3) | H2 ].
        - intros; apply Hl; right; auto.
        - left; exists y; simpl; auto.
        - right; intros ? [ <- | ]; auto.
  Qed.

End list_choose_dep.


Section sinc_decidable.

  Variable (P : nat -> Prop)
           (f : nat -> nat) 
           (Hf : forall n, f n < f (S n))
           (HP : forall n, P n <-> exists k, n = f k).

  Let f_mono x y : x <= y -> f x <= f y.
  Proof.
    induction 1 as [ | y H IH ]; auto.
    apply le_trans with (1 := IH), lt_le_weak, Hf.
  Qed.

  Let f_smono x y : x < y -> f x < f y.
  Proof.
    intros H; apply f_mono in H.
    apply lt_le_trans with (2 := H), Hf.
  Qed.

  Let f_ge_n n : n <= f n.
  Proof.
    induction n as [ | n IHn ]; try lia.
    apply le_trans with (2 := Hf _); lia.
  Qed.

  Let unbounded n : exists k, n <= k /\ P k.
  Proof. exists (f n); split; auto; rewrite HP; exists n; auto. Qed.

  Let decidable n : { P n } + { ~ P n }.
  Proof.
    destruct (@bounded_search (S n) (fun i => f i = n))
      as [ (i & H1 & H2) | H1 ].
    + intros i _; destruct (eq_nat_dec (f i) n); tauto.
    + left; rewrite HP; eauto.
    + right; rewrite HP; intros (k & Hk).
      symmetry in Hk; generalize Hk; apply H1.
      rewrite <- Hk; apply le_n_S; auto.
  Qed.

  Theorem sinc_decidable : (forall n, exists k, n <= k /\ P k)
                         * (forall n, { P n } + { ~ P n }).
  Proof. split; auto. Qed.

End sinc_decidable.

Section decidable_sinc.

  Variable (P    : nat -> Prop)
           (Punb : forall n, exists k, n <= k /\ P k)
           (Pdec : forall n, { P n } + { ~ P n }).

  Let next n : { k | P k /\ n <= k /\ forall x, P x -> x < n \/ k <= x }.
  Proof.
    destruct min_dec with (P := fun k => P k /\ n <= k)
      as (k & (H1 & H2) & H3).
    + intros i; destruct (Pdec i); destruct (le_lt_dec n i); try tauto; right; intro; lia.
    + destruct (Punb (S n)) as (k & H1 & H2).
      exists k; split; auto; lia.
    + exists k; repeat (split; auto).
      intros x Hx.
      destruct (le_lt_dec n x); try lia.
      right; apply H3; auto.
  Qed.

  Let f := fix f n := match n with 
    | 0   => proj1_sig (next 0)
    | S n => proj1_sig (next (S (f n)))
  end.

  Let f_sinc n : f n < f (S n).
  Proof.
    simpl.
    destruct (next (S (f n))) as (?&?&?&?); auto.
  Qed.

  Let f_select x : { n | f n <= x < f (S n) } + { x < f 0 }.
  Proof.
    induction x as [ | x IHx ].
    + destruct (eq_nat_dec 0 (f 0)) as [ H | H ].
      * left; exists 0; rewrite H at 2 3; split; auto.
      * right; lia.
    + destruct IHx as [ (n & Hn) | Hx ].
      * destruct (eq_nat_dec (S x) (f (S n))) as [ H | H ].
        - left; exists (S n); rewrite H; split; auto.
        - left; exists n; lia.
      * destruct (eq_nat_dec (S x) (f 0)) as [ H | H ].
        - left; exists 0; rewrite H; split; auto.
        - right; lia.
  Qed.
 
  Let f_P n : P n <-> exists k, n = f k.
  Proof.
    split.
    + intros Hn.
      destruct (f_select n) as [ (k & Hk) | C ].
      * simpl in Hk.
        destruct (next (S (f k))) as (m & H1 & H2 & H3); simpl in Hk.
        apply H3 in Hn.
        destruct Hn as [ Hn | Hn ]; try lia.
        exists k; lia.
      * simpl in C.
        destruct (next 0) as (m & H1 & H2 & H3); simpl in C.
        apply H3 in Hn; lia.
    + intros (k & Hk); subst.
      induction k as [ | k IHk ]; simpl.
      * destruct (next 0) as (m & H1 & H2 & H3); simpl; auto.
      * destruct (next (S (f k))) as (m & H1 & H2 & H3); simpl; auto.
  Qed.

  Theorem decidable_sinc : { f | (forall n, f n < f (S n))
                              /\ (forall n, P n <-> exists k, n = f k) }.
  Proof. exists f; auto. Qed.

End decidable_sinc.

(*
Check sinc_decidable.
Check decidable_sinc.
*)

