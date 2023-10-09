(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                                                            *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* A inductive characterization of list bi-inclusion
    as closure under contraction and permutation

    The proof does not require decidable equality
    and uses the somehow generalized PHP that
    states m ⊆ l and |l| <= |m| -> m has dup \/ l ~p m

 *)

Require Import Arith Lia List Permutation.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac php.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import measure_ind.

Set Implicit Arguments.

Local Reserved Notation "x ≡ y" (at level 70, no associativity).
Local Reserved Notation "x ⪼ y" (at level 70, no associativity).

Local Notation lhd := list_has_dup.
Local Infix "~p" := Permutation (at level 70, no associativity).
Local Notation "⌊ l ⌋" := (length l) (at level 1, format "⌊ l ⌋").

Local Infix "∈" := In (at level 70, no associativity).
Local Infix "⊆" := incl (at level 70, no associativity).
Local Infix "≃ₛ" := (fun l p => l ⊆ p /\ p ⊆ l) (at level 70, no associativity).

Section incl_extra.

  Variable (X : Type).

  Implicit Type (l : list X).

  Hint Resolve incl_refl incl_tl incl_cons incl_nil_l : core.

  Fact lequiv_refl l : l ≃ₛ l.
  Proof. split; auto. Qed.

  Fact lequiv_sym l m : l ≃ₛ m -> m ≃ₛ l.
  Proof. simpl; tauto. Qed.

  Fact lequiv_trans l m k : l ≃ₛ m -> m ≃ₛ k -> l ≃ₛ k.
  Proof. intros [] []; split; apply incl_tran with m; auto. Qed.

  Fact incl_cons_simpl x l m : l ⊆ m -> x::l ⊆ x::m.
  Proof. intros; apply incl_cons; simpl; auto. Qed.

  Fact incl_tail_simpl x l : l ⊆ x::l.
  Proof. auto. Qed.

  Hint Resolve incl_cons_simpl incl_tail_simpl : core.

  Fact incl_swap (x y : X) l : x::y::l ⊆ y::x::l.
  Proof. intros ? [ -> | [ -> | ] ]; simpl; auto. Qed.

  Fact incl_cntr (x : X) l : x::x::l ⊆ x::l.
  Proof. intros ? [ -> | [ -> | ] ]; simpl; auto. Qed.

  Fact lequiv_swap x y l : x::y::l ≃ₛ y::x::l.
  Proof. split; apply incl_cons; simpl; auto. Qed.

  Fact lequiv_app_comm l m : l++m ≃ₛ m++l.
  Proof. split; intros ?; rewrite !in_app_iff; tauto. Qed.

  Fact incl_cons_l_inv l m x : x::m ⊆ l -> x ∈ l /\ m ⊆ l.
  Proof.
    intros H; split.
    + apply H; simpl; auto.
    + apply incl_tran with (2 := H); simpl; auto.
  Qed.

  Hint Resolve perm_skip Permutation_cons_app : core.

  Fact incl_app_r_inv l m p : m ⊆ l++p -> exists m1 m2, m ~p m1++m2 /\ m1 ⊆ l /\ m2 ⊆ p.
  Proof.
    induction m as [ | x m IHm ].
    + exists nil, nil; auto.
    + intros H; apply incl_cons_l_inv in H as (H1 & H2).
      destruct (IHm H2) as (m1 & m2 & H3 & H4 & H5).
      apply in_app_or in H1 as [].
      * exists (x::m1), m2; simpl; auto.
      * exists m1, (x::m2); simpl; auto.
  Qed.
  
  Fact incl_cons_r_inv x l m : 
         m ⊆ x::l -> exists m1 m2, m ~p m1 ++ m2 /\ Forall (eq x) m1 /\ m2 ⊆ l.
  Proof.
    intros H.
    apply (@incl_app_r_inv (x::nil) _ l) in H as (m1 & m2 & H1 & H2 & H3).
    exists m1, m2; msplit 2; auto.
    rewrite Forall_forall.
    intros a Ha; apply H2 in Ha; destruct Ha as [ | [] ]; auto.
  Qed.

  Fact incl_right_cons_choose x l m : m ⊆ x::l -> x ∈ m \/ m ⊆ l.
  Proof.
    intros H; apply incl_cons_r_inv in H
      as ([ | y m1] & m2 & H1 & H2 & H3).
    + right.
      intros u H; apply H3; revert H.
      apply Permutation_in; auto.
    + left.
      apply Permutation_in with (1 := Permutation_sym H1).
      rewrite Forall_forall in H2.
      rewrite (H2 y); left; auto.
  Qed.

  Fact incl_left_right_cons x l y m : 
          x::l ⊆ y::m  -> y = x /\ y ∈ l 
                       \/ y = x /\ l ⊆ m
                       \/ x ∈ m /\ l ⊆ y::m.
  Proof.
    intros H; apply incl_cons_l_inv in H
      as [ [|] H2 ]; auto.
    apply incl_right_cons_choose in H2; tauto.
  Qed.

  Fact perm_incl_left m1 m2 l: m1 ~p m2 -> m2 ⊆ l -> m1 ⊆ l.
  Proof. intros H1 H2 ? H; apply H2; revert H; apply Permutation_in; auto. Qed.

  Fact perm_incl_right m l1 l2: l1 ~p l2 -> m ⊆ l1 -> m ⊆ l2.
  Proof. intros H1 H2 ? ?; apply Permutation_in with (1 := H1), H2; auto. Qed.
  
End incl_extra.

Section seteq.

  Variable X : Type.

  Implicit Types l : list X.

  Inductive list_contract : list X -> list X -> Prop :=
    | lc_nil      : nil ⪼  nil
    | lc_skip     : forall x l m, l ⪼ m -> x::l ⪼ x::m
    | lc_swap     : forall x y l, x::y::l ⪼ y::x::l
    | lc_cntr     : forall x l, x::x::l ⪼ x::l
    | lc_trans    : forall l m k, l ⪼ m -> m ⪼ k -> l ⪼ k
  where "l ⪼ m" := (list_contract l m).

  Hint Constructors list_contract : core.

  Fact perm_lc l m : l ~p m -> l ⪼ m.
  Proof. induction 1; eauto. Qed.

  Fact lc_length l m : l ⪼ m -> ⌊m⌋ <= ⌊l⌋.
  Proof. induction 1; simpl; lia. Qed.

  Fact lc_nil_inv_l l : nil ⪼ l -> l = nil.
  Proof.
    intros H; apply lc_length in H.
    destruct l; simpl in *; auto; lia.
  Qed.

  Hint Resolve perm_swap perm_trans : core.

  Fact lc_length_perm l m : l ⪼ m -> ⌊m⌋ < ⌊l⌋ \/ l ~p m.
  Proof.
    induction 1 as [ | ? ? ? ? [] | | 
      | ? ? ? ? [] ? [] ]; simpl; eauto;
      repeat match goal with
        | H: _ ⪼ _ |- _ => apply lc_length in H
      end; lia.
  Qed.

  Fact lc_refl l : l ⪼ l.
  Proof. apply perm_lc; auto. Qed.

  (* When viewed as sets, the lists are equivalent,
      ie closed under perm + contraction + RST *)

  Inductive list_seteq : list X -> list X -> Prop :=
    | lseq_nil   : nil ≡ nil
    | lseq_skip  : forall x l m, l ≡ m -> x::l ≡ x::m
    | lseq_swap  : forall x y l, x::y::l ≡ y::x::l
    | lseq_dup   : forall x l, x::x::l ≡ x::l
    | lseq_sym   : forall l m, l ≡ m -> m ≡ l 
    | lseq_trans : forall l m k, l ≡ m -> m ≡ k -> l ≡ k
  where "l ≡ m" := (list_seteq l m).

  Hint Constructors list_seteq : core.

  Fact lc_lseq l m : l ⪼ m -> l ≡ m.
  Proof. induction 1; eauto. Qed.

  Hint Resolve perm_lc lc_lseq : core.

  Fact perm_lseq l m : l ~p m -> l ≡ m.
  Proof. auto. Qed.

  Hint Resolve incl_refl incl_cons_simpl incl_swap incl_cntr incl_tl incl_tran : core.

  Fact lseq_lequiv l m : l ≡ m -> l ≃ₛ m.
  Proof.
    induction 1 as [ | ? ? ? ? [] | | 
                   | ? ? ? []
                   | ? ? ? ? [] ? [] ]; eauto.
  Qed.
 
  Hint Resolve lseq_lequiv : core.

  Fact lc_lequiv l m : l ⪼ m -> l ≃ₛ m.
  Proof. intro; apply lseq_lequiv; auto. Qed.

  Hint Resolve incl_l_nil : core.

  Fact lc_nil_inv_r l : l ⪼ nil -> l = nil.
  Proof. intros H; apply lc_lequiv in H as []; auto. Qed.
 
  Hint Resolve list_has_dup_swap in_eq in_cons in_list_hd0 in_list_hd1 : core.

  Notation lhd_cons_iff := list_has_dup_cons_iff.

  Fact lc_lhd l m : l ⪼ m -> lhd m -> lhd l.
  Proof.
    induction 1 as [ | x l m H IH | | | ]; eauto.
    rewrite !lhd_cons_iff; intros []; auto.
    apply lc_lequiv in H as []; auto.
  Qed.

  Fact lseq_incl l m : l ≡ m -> l ⊆ m.
  Proof. intro; apply lseq_lequiv; auto. Qed.

  (* A list with a dup is contractible in a smaller one *) 

  Lemma lhd_lc l : lhd l -> exists m, l ⪼ m /\ ⌊m⌋ < ⌊l⌋.
  Proof.
    induction 1 as [ l x H | l x H (m & H1 & H2) ].
    + apply in_split in H as (l1 & l2 & ->).
      exists (l1++x::l2); split; simpl; try lia.
      apply lc_trans with (x::x::l1++l2).
      * apply perm_lc, perm_skip, Permutation_sym,
              Permutation_cons_app; auto.
      * apply lc_trans with (1 := lc_cntr _ _), perm_lc,
              Permutation_cons_app; auto.
    + exists (x::m); split; simpl; auto; lia.
  Qed.

  Hint Resolve lc_lseq : core.

  Lemma lhd_lseq l : lhd l -> exists m, l ≡ m /\ ⌊m⌋ < ⌊l⌋.
  Proof. intro H; apply lhd_lc in H as (? & ? & ?); eauto. Qed.

  Hint Constructors list_contract : core.

  Hint Resolve lc_refl lc_lhd : core.

  Lemma lequiv_php_choose l m : l ≃ₛ m -> l ~p m \/ lhd l \/ lhd m.
  Proof.
    intros [ I1 I2 ].
    destruct (le_lt_dec ⌊m⌋ ⌊l⌋) as [ H1 | H1 ].
    + apply length_le_and_incl_implies_dup_or_perm in H1; tauto.
    + apply finite_php_dup in H1; tauto.
  Qed.

  (* if l and m are equivalent, either
     1) l ~p m in which case l is contractible into m
     2) lhd l hence l is contracted into a smaller one and recursion
     3) lhd m hence m is contracted into a smaller one and recursion
   *)

  Hint Resolve lequiv_trans : core.

  Lemma lequiv_lc l m : l ≃ₛ m -> exists c, l ⪼ c /\ m ⪼ c.
  Proof.
    induction on l m as IH with measure (⌊l⌋+⌊m⌋); intros H1.
    destruct (lequiv_php_choose H1) as [ H2 | [ H2 | H2 ] ]; eauto.
    + apply lhd_lc in H2 as (c & ? & ?).
      destruct (IH c m) as (d & ? & ?); eauto; lia.
    + apply lhd_lc in H2 as (c & ? & ?).
      destruct (IH l c) as (d & ? & ?); eauto; lia.
  Qed.

  Lemma lequiv_lseq l m : l ≃ₛ m -> l ≡ m.
  Proof. intros H; apply lequiv_lc in H as (c & []); eauto. Qed.

  Hint Resolve lequiv_lseq : core.

  (* seteq is equivalent to bi-inclusion *)

  Theorem lseq_lequiv_iff l m : l ≡ m <-> l ≃ₛ m.
  Proof. split; auto. Qed.

  (* A nice induction principle for list bi-inclusion *)

  Section lequiv_ind.

    Variables (P : list X -> list X -> Prop)
              (HP0 : P nil nil)
              (HP1 : forall x l m, l ≃ₛ m -> P l m -> P (x::l) (x::m))
              (HP2 : forall x y l, P (x::y::l) (y::x::l))
              (HP3 : forall x l, P (x::x::l) (x::l))
              (HP4 : forall l m, l ≃ₛ m -> P l m -> P m l)
              (HP5 : forall l m k, l ≃ₛ m -> P l m -> m ≃ₛ k -> P m k -> P l k).

    Theorem lequiv_ind l m : l ≃ₛ m -> P l m.
    Proof using All. rewrite <- lseq_lequiv_iff; induction 1; eauto. Qed.

  End lequiv_ind.

  Lemma lequiv_lhd_or_contract l m : l ≃ₛ m -> lhd m \/ l ⪼  m.
  Proof.
    simpl; intros H.
    destruct lequiv_lc with (1 := H) as (d & H1 & H2).
    apply lc_length_perm in H2 as [ H2 | H2 ].
    + apply finite_php_dup in H2; auto.
      apply lc_lseq, lseq_lequiv in H1.
      apply incl_tran with l; tauto.
    + right; apply lc_trans with (1 := H1).
      apply perm_lc, Permutation_sym; auto.
  Qed.

End seteq.
