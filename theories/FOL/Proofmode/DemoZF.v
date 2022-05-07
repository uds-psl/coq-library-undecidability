From Equations Require Import Equations.
Require Equations.Type.DepElim.
From Undecidability.Shared Require Import Dec.
From Undecidability.FOL Require Import Util.Syntax Util.FullDeduction Util.FullTarski ZF.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode.
Require Import String List.

Import ListNotations.
Open Scope string_scope.



Section ZF.

Existing Instance falsity_on.
Variable p : peirce.

Instance eqdec_funcs : EqDec ZF_func_sig.
Proof. intros x y; decide equality. Qed.

Instance eqdec_preds : EqDec ZF_pred_sig.
Proof. intros x y; decide equality. Qed.

Ltac custom_fold ::= fold sub in *.
Ltac custom_unfold ::= unfold sub in *.

Definition ax_refl := ∀ $0 ≡ $0.
Definition ax_sym := ∀ ∀ $1 ≡ $0 → $0 ≡ $1.
Definition ax_trans := ∀ ∀ ∀ $2 ≡ $1 → $1 ≡ $0 → $2 ≡ $0.
Definition ax_eq_elem := ∀ ∀ ∀ ∀ $3 ≡ $1 → $2 ≡ $0 → $3 ∈ $2 → $1 ∈ $0.
Definition ZF := ax_ext::ax_eset::ax_pair::ax_union::ax_power::ax_om1::ax_om2::ax_refl::ax_sym::ax_trans::ax_eq_elem::nil.



(** Setup rewriting *)

Program Instance ZF_Leibniz : Leibniz ZF_func_sig ZF_pred_sig falsity_on.
Next Obligation. exact equal. Defined.
Next Obligation. exact ZF. Defined.
Next Obligation. fintros. fapply ax_refl. Qed.
Next Obligation. fintros. fapply ax_sym. ctx. Qed.
Next Obligation.
  unfold ZF_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
  destruct F; repeat dependent elimination t0; repeat dependent elimination t.
  - fapply ax_refl.
  - cbn in H1; destruct H1 as [H1 [H2 _]]. fstart.
    fapply ax_ext; fintros "x" "H"; fapply ax_pair; fapply ax_pair in "H" as "[H|H]". 
    + fleft. feapply ax_trans. fapply "H". fapply H1.
    + fright. feapply ax_trans. fapply "H". fapply H2.
    + fleft. feapply ax_trans. fapply "H". fapply ax_sym. fapply H1.
    + fright. feapply ax_trans. fapply "H". fapply ax_sym. fapply H2.
  - cbn in H1; destruct H1 as [H1 _]. fstart.
    fapply ax_ext; fintros "x" "H"; fapply ax_union; fapply ax_union in "H" as "[y [H1 H2]]"; fexists y; fsplit.
    + feapply ax_eq_elem. fapply ax_refl. fapply H1. ctx.
    + ctx.
    + feapply ax_eq_elem. fapply ax_refl. feapply ax_sym. fapply H1. ctx.
    + ctx.
  - cbn in H1; destruct H1 as [H1 _]. fstart.
    fapply ax_ext; fintros "x" "H"; fapply ax_power in "H"; fapply ax_power; fintros y "H1".
    + feapply ax_eq_elem. fapply ax_refl. fapply H1. fapply "H". ctx.
    + feapply ax_eq_elem. fapply ax_refl. feapply ax_sym. fapply H1. fapply "H". ctx.
  - fapply ax_refl.
Qed.
Next Obligation.
  unfold ZF_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
  destruct P.
  - change (ZF_pred_ar elem) with 2 in t, t0; repeat dependent elimination t0; repeat dependent elimination t.
    cbn in H1. split.
    + intros H2. feapply ax_eq_elem. 3: apply H2. all: apply H1.
    + intros H2. feapply ax_eq_elem. 3: apply H2. all: fapply ax_sym; apply H1.
  - change (ZF_pred_ar equal) with 2 in t, t0; repeat dependent elimination t0; repeat dependent elimination t.
    cbn in H1. split.
    + intros H2. feapply ax_trans. feapply ax_sym. apply H1. feapply ax_trans.
      apply H2. apply H1.
    + intros H2. feapply ax_trans. apply H1. feapply ax_trans. apply H2.
      fapply ax_sym. apply H1.
Qed.



Lemma ZF_sub_pair' x y x' y' :
  ZF ⊢ (x ≡ x' → y ≡ y'→ sub ({x; y}) ({x'; y'})).
Proof.
  fstart. fintros "H1" "H2" "z". fintros "H3".
  fapply ax_pair. frewrite <- "H1". frewrite <- "H2".
  fapply ax_pair. ctx.
Qed.

Lemma ZF_eq_pair' x y x' y' :
  ZF ⊢ (x ≡ x' → y ≡ y'→ {x; y} ≡ {x'; y'}).
Proof.
  fstart. fintros "H1" "H2". fapply ax_ext.
  - fapply ZF_sub_pair'; ctx.
  - fapply ZF_sub_pair'; fapply ax_sym; ctx.
Qed.

Lemma ZF_union_el' x y z :
  ZF ⊢ (y ∈ x ∧ z ∈ y → z ∈ ⋃ x).
Proof.
  fstart. fintros "[H1 H2]". fapply ax_union. fexists y. fsplit; ctx. 
Qed.

Lemma ZF_sub_union x y :
  ZF ⊢ (x ≡ y → (⋃ x) ⊆ (⋃ y)).
Proof.
  fstart. fintros "H" "z". frewrite "H". fintros; ctx.
Qed.

Lemma ZF_eq_union x y :
  ZF ⊢ (x ≡ y → ⋃ x ≡ ⋃ y).
Proof.
  fstart. fintros "H". frewrite "H". fapply ax_refl.
Qed.

Lemma ZF_bunion_el' x y z :
  ZF ⊢ ((z ∈ x ∨ z ∈ y) → z ∈ x ∪ y).
Proof.
  fstart. fintros "[H|H]".
  - fapply ax_union. fexists x. fsplit. fapply ax_pair. fleft. fapply ax_refl. ctx.
  - fapply ax_union. fexists y. fsplit. fapply ax_pair. fright. fapply ax_refl. ctx.
Qed.

Lemma ZF_bunion_inv' x y z :
  ZF ⊢ (z ∈ x ∪ y → z ∈ x ∨ z ∈ y).
Proof.
  fstart. fintros "H". fapply ax_union in "H" as "[a [H1 H2]]".
  feapply ax_pair in "H1" as "[H1|H1]".
  - fleft. frewrite <- "H1". ctx.
  - fright. frewrite <- "H1". ctx.
Qed.

Lemma ZF_eq_bunion x y x' y' :
  ZF ⊢ (x ≡ x' → y ≡ y' → x ∪ y ≡ x' ∪ y').
Proof.
  fstart. fintros "H1" "H2". frewrite "H1". frewrite "H2". fapply ax_refl.
Qed.

Lemma ZF_sig_el x :
   ZF ⊢ (x ∈ σ x).
Proof.
  fapply ZF_bunion_el'. fright. fapply ax_pair. fleft. fapply ax_refl.
Qed.

Lemma ZF_eq_sig x y :
  ZF ⊢ (x ≡ y → σ x ≡ σ y).
Proof.
  fstart. fintros "H". frewrite "H". fapply ax_refl.
Qed.

Lemma ZF_bunion_el1 x y z :
  ZF ⊢ (z ∈ x → z ∈ x ∪ y).
Proof.
  fstart. fintros. fapply ax_union. fexists x. fsplit.
  - fapply ax_pair. fleft. fapply ax_refl.
  - ctx.
Qed.

Lemma ZF_bunion_el2 x y z :
  ZF ⊢ (z ∈ y → z ∈ x ∪ y).
Proof.
  fstart. fintro. fapply ax_union. fexists y. fsplit.
  fapply ax_pair. fright. fapply ax_refl. ctx.
Qed.

Lemma bunion_eset x :
   ZF ⊢ (∅ ∪ x ≡ x).
Proof.
  fstart. fapply ax_ext.
  - fintros "y" "H". fapply ZF_bunion_inv' in "H" as "[|]".
    + fexfalso. feapply ax_eset. ctx.
    + ctx.
  - fintros "y" "H". fapply ZF_bunion_el'. fright. ctx.
Qed.

Lemma bunion_swap x y z :
  ZF ⊢ ((x ∪ y) ∪ z ≡ (x ∪ z) ∪ y).
Proof.
  fstart. fapply ax_ext.
  - fintros "a" "H". fapply ZF_bunion_inv' in "H" as "[|]".
    + fapply ZF_bunion_inv' in "H" as "[H|H]".
      * fapply ZF_bunion_el'. fleft. fapply ZF_bunion_el'. fleft. ctx.
      * fapply ZF_bunion_el'. fright. ctx.
    + fapply ZF_bunion_el'. fleft. fapply ZF_bunion_el'. fright. ctx.
  - fintros "a" "H". fapply ZF_bunion_inv' in "H" as "[|]".
    + fapply ZF_bunion_inv' in "H" as "[H|H]".
      * fapply ZF_bunion_el'. fleft. fapply ZF_bunion_el'. fleft. ctx.
      * fapply ZF_bunion_el'. fright. ctx.
    + fapply ZF_bunion_el'. fleft. fapply ZF_bunion_el'. fright. ctx.
Qed.

End ZF.


