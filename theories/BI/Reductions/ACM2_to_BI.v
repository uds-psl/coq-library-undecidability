(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

From Undecidability.MinskyMachines 
  Require Import ACM2.

From Undecidability.BI
  Require Import BI utils encoding.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Import BI_notations.

Set Implicit Arguments.

Section embed_reduction.

  Let φ (p : nat + bool) :=
    match p with
    | inl n => 2+n
    | inr true => 0
    | inr false => 1
    end.

  Let ψ p :=
    match p with
    | 0 => inr true
    | 1 => inr false
    | S (S n) => inl n
    end.

  Local Fact Hembed : ∀p, ψ (φ p) = p.
  Proof. now intros [ | []]. Qed.

  Hint Resolve Hembed : core.

  Local Theorem embed_reduction_LBI µ cut :
    @BI_SEQ_PROVABLE µ (nat + bool) cut ⪯ @BI_SEQ_PROVABLE µ nat cut.
  Proof.
    apply reduces_dependent; exists.
    intros A.
    exists (BI_form_map µ (λ _ h, h) φ A).
    apply (LBI_embed_correctness φ ψ cut øₐ A); eauto.
  Qed.

  Local Theorem embed_reduction_HBI :
    @BI_HILBERT_PROVABLE (nat + bool) ⪯ @BI_HILBERT_PROVABLE nat.
  Proof.
    apply reduces_dependent; exists.
    intros A.
    exists (BI_form_map _ (λ _ h, h) φ A).
    apply (HBI_embed_correctness φ ψ A); eauto.
  Qed.

End embed_reduction.

Section LBI_Fragment.

  Variables (µ : BI_conn → bool)
            (Hµ1 : µ (BI_impl BI_mult) = true)
            (Hµ2 : µ (BI_impl BI_addi) = true)
            (Hµ3 : µ (BI_conj BI_addi) = true)
            (Hµ4 : µ (BI_unit BI_mult) = true)
            (cut : BI_cut).

  Local Fact Hµ c : BI_fragment_impl_conj_unit c = true → µ c = true.
  Proof using Hµ1 Hµ2 Hµ3 Hµ4. 
    destruct c as [ k | k | k | | ]; try destruct k; simpl; now auto. 
  Qed.

  Local Theorem relative_reduction_LBI loc : @ACM2_ACCEPT loc ⪯ @BI_SEQ_PROVABLE µ (loc + bool) cut.
  Proof using Hµ1 Hµ2 Hµ3 Hµ4.
    apply reduces_dependent; exists.
    intros (Σ & p & (x,y)).
    exists (acm2_to_BI_form Σ x y p µ Hµ); split; intros H.
    + red in H.
      apply acm2_to_HBI_correctness with (Hµ' := Hµ) in H; trivial.
      apply acm2_to_HBI_correctness; trivial.
    + apply acm2_to_HBI_correctness in H.
      red; apply acm2_to_HBI_correctness with (Hµ' := Hµ); trivial. 
  Qed.

  Hint Resolve reduces_transitive embed_reduction_LBI relative_reduction_LBI : core.

  Theorem reduction_LBI : @ACM2_ACCEPT nat ⪯ @BI_SEQ_PROVABLE µ nat cut.
  Proof using Hµ1 Hµ2 Hµ3 Hµ4. eauto. Qed.

End LBI_Fragment.

Check reduction_LBI.

Section HBI.

  Local Theorem relative_reduction_HBI loc : @ACM2_ACCEPT loc ⪯ @BI_HILBERT_PROVABLE (loc + bool).
  Proof.
    apply reduces_dependent; exists.
    intros (Σ & p & (x,y)).
    exists (acm2_to_BI_form Σ x y p (λ _, true) (λ _ _, eq_refl)); split; intros H; red in H |- *.
    + do 3 apply acm2_to_HBI_correctness with (Hµ' := λ _ _, eq_refl) (cut := BI_with_cut) in H; trivial.
    + do 1 apply acm2_to_HBI_correctness with (Hµ' := λ _ _, eq_refl) (cut := BI_with_cut); trivial.
  Qed.

  Hint Resolve reduces_transitive embed_reduction_HBI relative_reduction_HBI : core.

  Theorem reduction_HBI : @ACM2_ACCEPT nat ⪯ @BI_HILBERT_PROVABLE nat.
  Proof. eauto. Qed.

End HBI.

Check reduction_HBI.
