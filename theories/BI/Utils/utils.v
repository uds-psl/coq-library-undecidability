(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Eqdep_dec Utf8.

From Undecidability.BI
  Require Import BI.

Import BI_notations ListNotations.

Set Implicit Arguments.

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70).
#[local] Infix "∊" := In (at level 70).
#[local] Infix "~p" := (@Permutation _) (at level 70).

#[local] Hint Constructors Permutation : core.

Fact eq_bool_pirr (a b : bool) (e f : a = b) : e = f.
Proof. apply UIP_dec; decide equality. Qed.

Fact eq_bool_pirr' (a : bool) (e : a = a) : e = eq_refl.
Proof. apply eq_bool_pirr. Qed.

#[local] Fact exists_iff_compat X (P Q : X → Prop) : (∀x, P x ↔ Q x) → (∃x, P x) ↔ ∃x, Q x.
Proof. firstorder. Qed.

Fact permutation_in_head {X} (x : X) l : x ∊ l → ∃m, l ~p x::m.
Proof.
  induction l as [ | y l IHl ].
  + intros [].
  + intros [ <- | []%IHl ]; eauto.
Qed.

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

Section list_prod.

  Variables (X Y Z : Type) (p : X → Y → Z).

  Definition list_prod l m := flat_map (fun x => (map (p x) m)) l.

  Fact list_prod_spec l m z :
    z ∊ list_prod l m ↔ ∃ x y, z = p x y ∧ x ∊ l ∧ y ∊ m.
  Proof.
    unfold list_prod.
    rewrite in_flat_map.
    apply exists_iff_compat; intros x.
    rewrite in_map_iff; firstorder.
  Qed.

End list_prod.

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

  Theorem LBI_map_sound b b' (_ : b = BI_with_cut → b' = BI_with_cut)  Γ A :
    Γ L⊦[b] A → BI_bunch_map Γ L⊦[b'] BI_form_map A.
  Proof.
    induction 1; simpl; eauto; rewrite BI_ctx_bunch_map in * |- *; simpl in *; eauto.
  Qed.

End BI_map.

Fact BI_form_map_map (µ µ' µ'' : BI_conn → bool)
            (Hµ : ∀c, µ c = true → µ' c = true)
            (Hµ' : ∀c, µ' c = true → µ'' c = true)
            (prop prop' prop'' : Set)
            (φ : prop → prop') (ψ : prop' → prop'') A : 
    BI_form_map µ'' Hµ' ψ (BI_form_map µ' Hµ φ A)
  = BI_form_map µ'' (fun c h => Hµ' _ (Hµ c h)) (fun p => ψ (φ p)) A.
Proof. induction A; simpl; f_equal; auto. Qed.

#[local] Hint Constructors IL_axiom BI_axiom HBI_deduction : core.

Theorem HBI_map_sound (prop prop' : Set) (φ : prop → prop') A :
   H⊦ A → H⊦ BI_form_map _ (λ _ h, h) φ A.
Proof.
  unfold HBI_provable.
  induction 1 as [ ? [H|H] | | | | ]; simpl; eauto; constructor 1.
  + left; induction H; simpl; eauto.
  + right; induction H; simpl; eauto.
Qed.

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

  Hint Resolve in_or_app eq_bool_pirr : core.

  Fact BI_form_map_id hµ φ A :
     (∀v, v ∊ BI_form_vars A → φ v = v)
    → BI_form_map µ hµ φ A = A.
  Proof. induction A; simpl; intro; f_equal; auto. Qed.

  Hint Resolve BI_form_map_id : core.

  Fact BI_bunch_map_id hµ φ Γ :
     (∀v, v ∊ BI_bunch_vars Γ → φ v = v)
    → BI_bunch_map µ hµ φ Γ = Γ.
  Proof. induction Γ; simpl; intros; f_equal; auto. Qed.

End BI_vars.

Section LBI_embed.

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

  Theorem LBI_embed_correctness cut Σ A :
      (∀v, v ∊ BI_form_vars A → ψ (φ v) = v)
    → (∀v, v ∊ BI_bunch_vars Σ → ψ (φ v) = v)
    → Σ L⊦[cut] A ↔ BI_bunch_map µ (λ _ h, h) φ Σ L⊦[cut] BI_form_map µ (λ _ h, h) φ A.
  Proof.
    intros H1 H2; split.
    + apply LBI_map_sound; auto.
    + intros H%(LBI_map_sound µ (λ _ h, h) ψ (λ h, h)).
      now rewrite BI_bunch_map_embed, BI_form_map_embed in H.
  Qed.

End LBI_embed.

Theorem HBI_embed_correctness (prop prop' : Set) (φ : prop → prop') (ψ : prop' → prop) A :
    (∀v, v ∊ BI_form_vars A → ψ (φ v) = v)
  → H⊦ A ↔ H⊦ BI_form_map _ (λ _ h, h) φ A.
Proof.
  intros H1; split.
  + apply HBI_map_sound.
  + intros H%(HBI_map_sound ψ).
    rewrite BI_form_map_embed in H; auto.
Qed.





