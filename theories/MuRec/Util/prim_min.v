(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_nat.

Set Implicit Arguments.

Set Default Proof Using "Type".

Section iter.

  Variable (X : Type) (f : X -> X). 

  Fixpoint iter n x :=
    match n with 
      | 0   => x
      | S n => f (iter n x)
    end.

  Fact iter_plus n m x : iter (n+m) x = iter n (iter m x).
  Proof. induction n; simpl; f_equal; auto. Qed.

  Fact iter_S n x : iter (S n) x = iter n (f x).
  Proof. replace (S n) with (n+1) by lia; apply iter_plus. Qed.

End iter.

Section prim_min.

  Variable (X : Type) (f : nat -> nat).

  Let min_f n : f n = 0 -> { k | k <= n /\ f k = 0 /\ forall i, i < k -> f i <> 0 }.
  Proof.
    intros Hn.
    destruct first_which with (P := fun i => f i = 0) as (k & H1 & H2). 
    + intros; apply eq_nat_dec.
    + exists n; auto.
    + exists k; split; auto.
      destruct (le_lt_dec k n); auto.
      destruct (H2 n); auto. 
  Qed.
 
  Let g i := match f i with 0 => i | _ => S i end.

  Let prim_min_rec n a := iter g n a.

  Let prim_min_rec_spec_0 n a : (forall i, i < n -> f (i+a) <> 0) -> forall i, i <= n -> prim_min_rec i a = i+a.
  Proof.
    unfold prim_min_rec.
    revert a; induction n as [ | n IHn ]; intros a Hn.
    + intros i Hi; replace i with 0 by lia; auto.
    + intros [ | i ] Hi; auto.
      * rewrite iter_S.
        unfold g at 2.
        generalize (Hn 0); simpl; intros E.
        destruct (f a); try lia.
        rewrite IHn; try lia.
        intros j Hj.
        replace (j+S a) with (S j+a) by lia.
        apply Hn; lia.
  Qed.

  Let prim_min_rec_spec_1 n a : f a = 0 -> prim_min_rec n a = a.
  Proof.
    intros Ha; unfold prim_min_rec.
    induction n as [ | n IHn ]; auto.
    rewrite iter_S.
    unfold g at 2; rewrite Ha; auto.
  Qed.

  Definition prim_min n := prim_min_rec n 0.

  Fact prim_min_spec n : f n = 0 -> f (prim_min n) = 0 /\ forall i, i < prim_min n -> f i <> 0.
  Proof.
    intros Hn.
    destruct (min_f Hn) as (k & H1 & H2 & H3).
    assert (prim_min n = k) as H4.
    { unfold prim_min. 
      unfold prim_min_rec.
      replace n with (n-k+k) by lia.
      rewrite iter_plus.
      fold (prim_min_rec k 0).
      rewrite prim_min_rec_spec_0 with (n := k) (a := 0); auto.
      rewrite plus_comm; apply prim_min_rec_spec_1; auto.
      intros; apply H3; lia. }
    rewrite H4; auto.
  Qed.

End prim_min.
