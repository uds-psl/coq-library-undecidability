(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import php.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_chains.

Set Implicit Arguments.

Section wf_strict_order_list.

  Variable (X : Type) (R : X -> X -> Prop).
  Hypothesis (Rirrefl : forall x, ~ R x x)
             (Rtrans : forall x y z, R x y -> R y z -> R x z).

  Implicit Type l : list X.

  Fact chain_trans n x y : chain R n x y -> n = 0 /\ x = y \/ R x y.
  Proof.
    induction 1 as [ x | n x y z H1 H2 IH2 ]; auto.
    destruct IH2 as [ [] | ]; subst; right; auto.
    apply Rtrans with (1 := H1); auto.
  Qed.

  Corollary chain_irrefl n x : n = 0 \/ ~ chain R n x x.
  Proof.
    destruct n as [ | n ]; auto; right; intros H.
    destruct (chain_trans H) as [ (? & _) | H1 ]; try discriminate.
    revert H1; apply Rirrefl.
  Qed.

  Variable (m : list X) (Hm : forall x y, R x y -> In x m).

  Fact chain_list_incl l x y : chain_list R l x y -> l = nil \/ incl l m.
  Proof.
    induction 1 as [ x | x l y z H1 H2 IH2 ]; simpl; auto; right.
    apply incl_cons.
    + apply Hm with (1 := H1); auto.
    + destruct IH2; auto; subst l; intros _ [].
  Qed.

  (* Any chain of length above length m contains a duplicated
      value (by the PHP) hence a non nil sub-chain with identical 
      endpoints, contradicting chain_irrefl *)

  Lemma chain_bounded n x y : chain R n x y -> n <= length m.
  Proof.
    intros H.
    destruct (le_lt_dec n (length m)) as [ | C ]; auto.
    destruct chain_chain_list with (1 := H)
      as (ll & H1 & H2).
    cut (list_has_dup ll).
    + intros H3.
      apply list_has_dup_equiv in H3.
      destruct H3 as (z & l & u & r & ->).
      apply chain_list_app_inv in H1.
      destruct H1 as (a & _ & H1).
      apply chain_list_cons_inv in H1.
      destruct H1 as (<- & k & H3 & H1).
      apply chain_list_app_inv in H1.
      destruct H1 as (p & H4 & H1).
      apply chain_list_cons_inv in H1.
      destruct H1 as (<- & _ & _ & _).
      apply chain_list_chain in H4.
      destruct (chain_irrefl (S (length u)) z)
        as [ | [] ]; try discriminate.
      constructor 2 with k; auto.
    + apply chain_list_incl in H1.
      destruct H1 as [ -> | H1 ].
      * subst; simpl in C; lia.
      * apply finite_php_dup with (2 := H1); lia.
  Qed.

  (* Since chains have bounded length, we get WF *)

  Theorem wf_strict_order_list : well_founded R.
  Proof.
    apply wf_chains.
    intros x; exists (length m). 
    intros ? ?; apply chain_bounded.
  Qed.

End wf_strict_order_list.

Section wf_strict_order_finite.

  Variable (X : Type) (HX : exists l, forall x : X, In x l) 
           (R : X -> X -> Prop)
           (Rirrefl : forall x, ~ R x x)
           (Rtrans : forall x y z, R x y -> R y z -> R x z).

  Theorem wf_strict_order_finite : well_founded R.
  Proof.
    destruct HX as (m & Hm).
    apply wf_strict_order_list with (m := m); auto.
  Qed.

End wf_strict_order_finite.
