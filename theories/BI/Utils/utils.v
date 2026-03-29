(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Utf8.

From Undecidability.BI
  Require Import BI.

Import ListNotations.

Set Implicit Arguments.

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70).
#[local] Infix "∊" := In (at level 70).
#[local] Infix "~p" := (@Permutation _) (at level 70).

#[local] Hint Constructors Permutation : core.

Fact permutation_in_head {X} (x : X) l : x ∊ l → ∃m, l ~p x::m.
Proof.
  induction l as [ | y l IHl ].
  + intros [].
  + intros [ <- | []%IHl ]; eauto.
Qed.

#[local] Notation "x ≡ y" := (BI_bunch_equiv x y) (at level 70, no associativity, format "x  ≡  y").
#[local] Notation "C [ Δ ]" := (BI_ctx_fill C Δ) (at level 1, no associativity, format "C [ Δ ]").
#[local] Notation "Γ '⊦[' b ']' A" := (LBI_provable b Γ A) (at level 70, no associativity, format "Γ  ⊦[ b ]  A").

#[local] Notation "⟨ A ⟩" := (BI_bunch_atom A) (at level 0, format "⟨ A ⟩"). 

#[local] Notation "'ø[' k ']'" := (BI_bunch_unit _ _ k) (at level 0, no associativity, format "ø[ k ]").
#[local] Notation "Γ '⊛[' k ']' Δ" := (BI_bunch_comp k Γ Δ) (at level 65, left associativity, format "Γ  ⊛[ k ]  Δ").

#[local] Notation øₐ := ø[BI_addi].
#[local] Notation øₘ := ø[BI_mult].
#[local] Notation "Γ '⊛ₐ' Δ" := (Γ ⊛[BI_addi] Δ) (at level 65, left associativity, format "Γ  ⊛ₐ  Δ").
#[local] Notation "Γ '⊛ₘ' Δ" := (Γ ⊛[BI_mult] Δ) (at level 65, left associativity, format "Γ  ⊛ₘ  Δ").

Section BI_list_mult.

  Variable (µ : BI_conn → bool) (prop : Set).

  Definition BI_list_mult : _ → BI_bunch µ prop := fold_right (λ φ Γ, ⟨φ⟩ ⊛ₘ Γ) øₘ.

  Hint Constructors BI_bunch_equiv : core.

  Fact BI_list_mult_perm_bequiv l m :
    l ~p m → BI_list_mult l ≡ BI_list_mult m.
  Proof. induction 1; simpl; eauto. Qed.

  Fact BI_list_mult_app Σ Δ : BI_list_mult (Σ++Δ) ≡ (BI_list_mult Σ) ⊛ₘ (BI_list_mult Δ).
  Proof. induction Σ; simpl; eauto. Qed.

  Fact BI_list_mult_snoc Σ A : (BI_list_mult Σ) ⊛ₘ ⟨A⟩ ≡ BI_list_mult (A::Σ).
  Proof. simpl; apply BI_bequiv_comm. Qed.

End BI_list_mult.

Section BI_map.

  Variables (µ µ' : BI_conn → bool)
            (Hµ : ∀c, µ c = true → µ' c = true)
            (prop prop' : Set)
            (φ : prop → prop').

  Fixpoint BI_form_map (A : BI_form µ prop) : BI_form µ' prop' :=
    match A with
    | BI_form_var _ v      => BI_form_var _ (φ v)
    | BI_form_unit _ _ k h => BI_form_unit _ _ k (Hµ h)
    | BI_form_impl k h A B => BI_form_impl k (Hµ h) (BI_form_map A) (BI_form_map B)
    | BI_form_conj k h A B => BI_form_conj k (Hµ h) (BI_form_map A) (BI_form_map B)
    | BI_form_disj h A B   => BI_form_disj (Hµ h) (BI_form_map A) (BI_form_map B)
    | BI_form_bot _ _ h    => BI_form_bot _ _ (Hµ h)
    end.

  Fixpoint BI_bunch_map Γ :=
    match Γ with
    | BI_bunch_atom A     => BI_bunch_atom (BI_form_map A)
    | BI_bunch_unit _ _ b => BI_bunch_unit _ _ b
    | BI_bunch_comp k Γ Δ => BI_bunch_comp k (BI_bunch_map Γ) (BI_bunch_map Δ)
    end.

  Section BI_bunch_equiv.

    Hint Constructors BI_bunch_equiv : core.
 
    Fact BI_bunch_equiv_map Γ Δ : Γ ≡ Δ → BI_bunch_map Γ ≡ BI_bunch_map Δ.
    Proof. induction 1; simpl; eauto. Qed.

  End BI_bunch_equiv.

  Fixpoint BI_ctx_map C :=
    match C with
    | BI_ctx_hole _ _ => BI_ctx_hole _ _
    | BI_ctx_comp b k Γ C => BI_ctx_comp b k (BI_bunch_map Γ) (BI_ctx_map C)
    end.

  Fact BI_ctx_bunch_map C Γ : BI_bunch_map (C[Γ]) = (BI_ctx_map C)[BI_bunch_map Γ].
  Proof. induction C as [ | [] ]; simpl; f_equal; auto. Qed.

  Hint Constructors LBI_provable : core.
  Hint Resolve BI_bunch_equiv_map : core.

  Theorem BI_map_sound b b' Γ A : 
      (b = BI_with_cut → b' = BI_with_cut) 
    → Γ ⊦[b] A 
    → BI_bunch_map Γ ⊦[b'] BI_form_map A.
  Proof.
    induction 2; simpl; eauto; rewrite BI_ctx_bunch_map in * |- *; simpl in *; eauto.
  Qed.

End BI_map.

Section BI_vars.

  Variables (µ : BI_conn → bool) (prop : Set).

  Fixpoint BI_form_vars (A : BI_form µ prop) :=
    match A with
    | BI_form_var _ v      => [v]
    | BI_form_unit _ _ k h => []
    | BI_form_bot _ _ h    => []
    | BI_form_impl _ _ A B => BI_form_vars A ++ BI_form_vars B
    | BI_form_conj _ _ A B => BI_form_vars A ++ BI_form_vars B
    | BI_form_disj _ A B   => BI_form_vars A ++ BI_form_vars B
    end.

  Fixpoint BI_bunch_vars (Γ : BI_bunch µ prop) :=
    match Γ with
    | BI_bunch_unit _ _ _ => []
    | BI_bunch_atom A     => BI_form_vars A
    | BI_bunch_comp _ Γ Δ => BI_bunch_vars Γ ++ BI_bunch_vars Δ
    end.

  Hint Resolve in_or_app : core.

  Fact BI_form_map_id φ A :
     (∀v, v ∊ BI_form_vars A → φ v = v)
    → BI_form_map µ (λ _ h, h) φ A = A.
  Proof. induction A; simpl; intro; f_equal; eauto. Qed.

  Hint Resolve BI_form_map_id : core.

  Fact BI_bunch_map_id φ Γ :
     (∀v, v ∊ BI_bunch_vars Γ → φ v = v)
    → BI_bunch_map µ (λ _ h, h) φ Γ = Γ.
  Proof. induction Γ; simpl; intros; f_equal; auto. Qed.

End BI_vars.

Section BI_embed.

  Variables (µ : BI_conn → bool)
            (prop prop' : Set)
            (φ : prop → prop')
            (ψ : prop' → prop).

  Hint Resolve in_or_app : core.

  Fact BI_form_map_embed A : 
      (∀v, v ∊ BI_form_vars A → ψ (φ v) = v)
    → BI_form_map µ (λ _ h, h) ψ (BI_form_map µ (λ _ h, h) φ A) = A.
  Proof. induction A; simpl; intro; f_equal; eauto. Qed.

  Hint Resolve BI_form_map_embed : core.

  Fact BI_bunch_map_embed Γ : 
      (∀v, v ∊ BI_bunch_vars Γ → ψ (φ v) = v)
    → BI_bunch_map µ (λ _ h, h) ψ (BI_bunch_map µ (λ _ h, h) φ Γ) = Γ.
  Proof. induction Γ; simpl; intros; f_equal; auto. Qed.

  Theorem BI_embed_correctness b Σ A :
      (∀v, v ∊ BI_form_vars A → ψ (φ v) = v)
    → (∀v, v ∊ BI_bunch_vars Σ → ψ (φ v) = v)
    → Σ ⊦[b] A ↔ BI_bunch_map µ (λ _ h, h) φ Σ ⊦[b] BI_form_map µ (λ _ h, h) φ A.
  Proof.
    intros H1 H2; split.
    + apply BI_map_sound; auto.
    + intros H%(BI_map_sound µ (λ _ h, h) ψ (λ h, h)).
      now rewrite BI_bunch_map_embed, BI_form_map_embed in H.
  Qed.

End BI_embed.

