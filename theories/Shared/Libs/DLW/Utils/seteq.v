(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                                                            *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** A inductive characterization of list bi-inclusion
    as closure under contraction and permutation

    The proof does not require decidable equality
    and uses the somehow generalized PHP that
    states m ⊆ l and |l| <= |m| -> m has dup \/ l ~p m

 *)

Require Import Arith Lia List Permutation.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import php.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import measure_ind.

Set Implicit Arguments.

Reserved Notation "x ≡ y" (at level 70, no associativity).
Reserved Notation "x ⊆ y" (at level 70, no associativity).

Local Infix "~p" := (@Permutation _) (at level 70, no associativity).

Section seteq.

  Variable X : Type.

  (** When viewed as sets, the lists are equivalent,
      ie closed under perm + contraction + RST *)

  Inductive seteq : list X -> list X -> Prop :=
    | seteq_nil   : nil ≡ nil
    | seteq_skip  : forall x l m, l ≡ m -> x::l ≡ x::m
    | seteq_swap  : forall x y l, x::y::l ≡ y::x::l
    | seteq_dup   : forall x l, x::x::l ≡ x::l
    | seteq_sym   : forall l m, l ≡ m -> m ≡ l 
    | seteq_trans : forall l m k, l ≡ m -> m ≡ k -> l ≡ k
  where "l ≡ m" := (seteq l m).

  Hint Constructors seteq : core.

  Fact perm_seteq l m : l ~p m -> l ≡ m.
  Proof. induction 1; eauto. Qed.

  Notation "l ⊆ m" := (incl l m).

  Fact incl_cons_mono (x : X) l m : l ⊆ m -> x::l ⊆ x::m.
  Proof. intros ? ? [ -> | ]; simpl; auto. Qed.

  Fact incl_swap (x y : X) l : x::y::l ⊆ y::x::l.
  Proof. intros ? [ -> | [ -> | ] ]; simpl; auto. Qed.

  Fact incl_cntr (x : X) l : x::x::l ⊆ x::l.
  Proof. intros ? [ -> | [ -> | ] ]; simpl; auto. Qed.

  Hint Resolve incl_refl incl_cons_mono incl_swap incl_cntr incl_tl : core.

  Fact seqeq_incl l m : l ≡ m -> l ⊆ m /\ m ⊆ l.
  Proof.
    induction 1 as [ | x l m H [] | x y l | x l 
                   | l m H []
                   | l m k H1 IH1 H2 IH2 ]; auto.
    split; apply incl_tran with m; tauto.
  Qed.

  Lemma list_has_dup_seteq l : list_has_dup l -> exists m, m ≡ l /\ length m < length l.
  Proof.
    induction 1 as [ l x H | l x H (m & H1 & H2) ].
    + induction l as [ | y l IHl ].
      * exfalso; destruct H.
      * destruct H as [ -> | H ].
        - exists (x::l); simpl; split; auto; lia.
        - destruct (IHl H) as (m & H1 & H2).
          exists (y::m); simpl in *; split; try lia.
          apply seteq_trans with (y::x::l); auto.
    + exists (x::m); simpl; split; auto; lia.
  Qed.

  (** The proof by induction on |l|+|m| for l ⊆ m and m ⊆ l

      Three cases:

      (1) m has dup    (2) l ~p m      (3) l has dup

      For (2) If l ~p m then it is trivial

      Otherwise (1 or 3), if eg l has dup then l ≡ l' for a shorter l' 
      we deduce l' ⊆ m and m ⊆ l' by seqeq_incl
      and apply the induction hypothesis to (l',m)

    *)

  Lemma incl_seteq l m : l ⊆ m -> m ⊆ l -> l ≡ m.
  Proof.
    induction on l m as IH with measure (length l + length m).
    intros H1 H2.
    destruct (le_lt_dec (length l) (length m)) as [ H3 | H3 ];
      [ destruct length_le_and_incl_implies_dup_or_perm with (1 := H3)
        as [ H4 | H4 ]; auto | ].
    + destruct list_has_dup_seteq with (1 := H4) as (m' & H5 & H6).
      apply seteq_trans with m'; auto.
      apply seqeq_incl in H5; destruct H5.
      apply IH; try lia; apply incl_tran with m; auto.
    + apply seteq_sym, perm_seteq; auto.
    + generalize (finite_php_dup H3 H1); intros H4.
      destruct list_has_dup_seteq with (1 := H4) as (m' & H5 & H6).
      apply seteq_trans with m'; auto.
      apply seqeq_incl in H5; destruct H5.
      apply IH; try lia; apply incl_tran with l; auto.
  Qed.

  Hint Resolve seqeq_incl incl_seteq : core.

  (** seteq is equivalent to bi-inclusion *)

  Theorem seteq_bi_incl l m : l ≡ m <-> l ⊆ m /\ m ⊆ l.
  Proof. split; auto; intros []; auto. Qed.

End seteq.

Local Infix "≡" := seteq.
Local Infix "⊆" := incl.

(*
Print seteq.
Check seteq_bi_incl.
Print Assumptions seteq_bi_incl.
*)