(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import Arith List Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import php.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_chains.

Set Implicit Arguments.

Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊆" := incl (at level 70, no associativity).

Section wf_strict_order_list.

  Variable (X : Type) (R : X -> X -> Prop).
  Hypothesis (Rirrefl : forall x, ~ R x x)
             (Rtrans : forall x y z, R x y -> R y z -> R x z).

  Implicit Type l : list X.

  Fact chain_trans n x y : chain R n x y -> n = 0 /\ x = y \/ R x y.
  Proof. induction 1 as [ | ? ? ? ? ? ? [ [] | ] ]; subst; eauto. Qed.

  Corollary chain_irrefl n x :~ chain R (S n) x x.
  Proof.
    intros H.
    apply chain_trans in H as [ (? & _) | H ]; try easy.
    revert H; apply Rirrefl.
  Qed.

  (* Assume a list over approximating the domain of R *)

  Variable (m : list X) (Hm : forall x y, R x y -> x ∊ m).

  Hint Resolve incl_nil_l incl_cons : core.

  Fact chain_list_incl l x y : chain_list R l x y -> l ⊆ m.
  Proof. induction 1; simpl; eauto. Qed.

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
      apply list_has_dup_equiv in H3 as (z & l & u & r & ->).
      apply chain_list_app_inv in H1 as (a & _ & H1).
      apply chain_list_cons_inv in H1 as (<- & k & H3 & H1).
      apply chain_list_app_inv in H1 as (p & H4 & H1).
      apply chain_list_cons_inv in H1 as (<- & _ & _ & _).
      apply chain_list_chain in H4.
      destruct (@chain_irrefl (length u) z).
      constructor 2 with k; auto.
    + apply chain_list_incl in H1.
      apply finite_php_dup with (2 := H1); lia.
  Qed.

  (* Since chains have bounded length, we get WF *)

  Hint Resolve chain_bounded : core.

  Theorem wf_strict_order_list : well_founded R.
  Proof. apply wf_chains; eauto. Qed.

End wf_strict_order_list.

Section wf_strict_order_finite.

  Variable (X : Type) (HX : exists l, forall x : X, x ∊ l) 
           (R : X -> X -> Prop)
           (Rirrefl : forall x, ~ R x x)
           (Rtrans : forall x y z, R x y -> R y z -> R x z).

  Theorem wf_strict_order_finite : well_founded R.
  Proof.
    destruct HX as (m & Hm).
    apply wf_strict_order_list with (m := m); auto.
  Qed.

End wf_strict_order_finite.
