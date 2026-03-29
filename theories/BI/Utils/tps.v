(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

From Undecidability.BI
  Require Import BI utils hbi.

Import ListNotations.

Set Implicit Arguments.

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70).
#[local] Infix "∊" := In (at level 70).

#[local] Notation "x ≡ y" := (BI_bunch_equiv x y) (at level 70, no associativity, format "x  ≡  y").
#[local] Notation "C [ Δ ]" := (BI_ctx_fill C Δ) (at level 1, no associativity, format "C [ Δ ]").

#[local] Notation "£ v" := (@BI_form_var _ _ v) (at level 1, format "£ v").
#[local] Notation "⊤" := (@BI_form_unit _ _ BI_addi _).
#[local] Notation "1" := (@BI_form_unit _ _ BI_mult _).
#[local] Notation "⊥" := (@BI_form_bot _ _ _).

#[local] Notation "A ∗ B" := (@BI_form_conj _ _ BI_mult _ A B) (at level 59, left associativity, format "A ∗ B").
#[local] Notation "A '-∗' B" := (@BI_form_impl _ _ BI_mult _ A B) (at level 63, right associativity, format "A -∗ B").
#[local] Notation "A ⇒ B" := (@BI_form_impl _ _ BI_addi _ A B) (at level 63, right associativity, format "A ⇒ B").
#[local] Notation "A ⩑ B" := (@BI_form_conj _ _ BI_addi _ A B) (at level 59, left associativity, format "A ⩑ B").
#[local] Notation "A ⩒ B" := (@BI_form_disj _ _ _ A B) (at level 61, left associativity, format "A ⩒ B").

#[local] Notation "⟨ A ⟩" := (BI_bunch_atom A) (at level 0, format "⟨ A ⟩"). 
#[local] Notation "'ø[' k ']'" := (BI_bunch_unit _ _ k) (at level 0, no associativity, format "ø[ k ]").
#[local] Notation "Γ '⊛[' k ']' Δ" := (BI_bunch_comp k Γ Δ) (at level 65, left associativity, format "Γ  ⊛[ k ]  Δ").
#[local] Notation øₐ := ø[BI_addi].
#[local] Notation øₘ := ø[BI_mult].
#[local] Notation "Γ '⊛ₐ' Δ" := (Γ ⊛[BI_addi] Δ) (at level 65, left associativity, format "Γ  ⊛ₐ  Δ").
#[local] Notation "Γ '⊛ₘ' Δ" := (Γ ⊛[BI_mult] Δ) (at level 65, left associativity, format "Γ  ⊛ₘ  Δ").

Section TPS.

  Variables (M : Type) (plus : M → M → M) (e : M)
            (neut : ∀x, plus e x = x)
            (comm : ∀ x y, plus x y = plus y x)
            (assoc : ∀ x y z, plus (plus x y) z = plus x (plus y z)).

  Reserved Notation "x -∘ y" (at level 67, right associativity, format "x -∘ y").
  Reserved Notation "x ⊏ y" (at level 67, right associativity, format "x ⊏ y").
  Reserved Notation "x ∘ y"  (at level 64, left associativity, format "x ∘ y").
  Reserved Notation "x ⊓ y"  (at level 62, left associativity, format "x ⊓ y").
  Reserved Notation "x ⊔ y"  (at level 65, left associativity, format "x ⊔ y"). 

  Definition tps_lolipop (X Y : M → Prop) x := ∀a, X a → Y (plus a x).
  Definition tps_impl (X Y : M → Prop) x := X x → Y x.
  Definition tps_tensor (X Y : M → Prop) x := ∃ a b, x = plus a b ∧ X a ∧ Y b. 
  Definition tps_with (X Y : M → Prop) x := X x ∧ Y x.
  Definition tps_union (X Y : M → Prop) x := X x ∨ Y x.

  Infix "-∘" := tps_lolipop.
  Infix "⊏" := tps_impl.
  Infix "∘" := tps_tensor.
  Infix "⊓" := tps_with.
  Infix "⊔" := tps_union.

  Reserved Notation "⟦ x ⟧" (at level 0, format "⟦ x ⟧").
  Reserved Notation "⟦ x ⟧ₗ" (at level 0, format "⟦ x ⟧ₗ").

  Section generic.

    Variables (µ : BI_conn → bool) (prop : Set) (s : prop → M → Prop).
 
    Fixpoint tps_BI_form (A : BI_form µ prop) : M → Prop :=
      match A with
      | £v   => s v
      | ⊤    => λ _, True
      | ⊥    => λ _, False
      | 1    => eq e
      | A⇒B  => ⟦A⟧ ⊏ ⟦B⟧
      | A-∗B => ⟦A⟧ -∘ ⟦B⟧
      | A∗B  => ⟦A⟧ ∘ ⟦B⟧
      | A⩑B  => ⟦A⟧ ⊓ ⟦B⟧
      | A⩒B  => ⟦A⟧ ⊔ ⟦B⟧
      end
    where "⟦ A ⟧" := (tps_BI_form A).

    Fixpoint tps_BI_bunch Γ :=
      match Γ with
      | ⟨A⟩    => ⟦A⟧
      | øₐ     => λ _, True
      | øₘ     => eq e
      | Γ ⊛ₐ Δ => ⟦Γ⟧ₗ ⊓ ⟦Δ⟧ₗ
      | Γ ⊛ₘ Δ => ⟦Γ⟧ₗ ∘ ⟦Δ⟧ₗ
      end
    where "⟦ Γ ⟧ₗ" := (tps_BI_bunch Γ).

    Lemma tps_BI_equiv Γ Δ : Γ ≡ Δ → ∀x, ⟦Γ⟧ₗ x ↔ ⟦Δ⟧ₗ x.
    Proof using neut assoc comm.
      induction 1 as [ | | | [] | [] | [] | [] ]; try (firstorder; fail).
      + intros x; split.
        * intros (? & ? & -> & <- & ?); now rewrite neut.
        * exists e, x; now rewrite neut.
      + intros x; split;
          intros (a & b & -> & []); rewrite comm; now exists b, a.
      + intros x; split.
        * intros (? & c & -> & (a & b & -> & []) & ?).
          exists a, (plus b c); rewrite assoc; repeat split; auto.
          now exists b, c.
        * intros (a & ? & -> & ? & b & c & -> & ? & ?).
          exists (plus a b), c; rewrite assoc; repeat split; auto.
          now exists a, b.
     Qed.

    Fact tps_BI_bunch_list_mult Σ : (∀A, A ∊ Σ → ⟦A⟧ e) → ⟦BI_list_mult Σ⟧ₗ e.
    Proof using neut.
      rewrite <- Forall_forall.
      induction 1; simpl; auto.
      exists e, e; rewrite neut; auto.
    Qed.

    Lemma tps_BI_ctx_mono Σ Γ Δ : ⟦Γ⟧ₗ ⊆ ⟦Δ⟧ₗ → ⟦Σ[Γ]⟧ₗ ⊆ ⟦Σ[Δ]⟧ₗ.
    Proof.
      intros H.
      induction Σ as [ | [] [] Θ ]; simpl; auto.
      1,3: intros x (a & b & -> & ? & ?); exists a, b; auto.
      all: intros ? []; split; auto.
    Qed.

  End generic.

  Section HBI.

    Notation µ := (λ _ : BI_conn, true).

    Variables (prop : Set) (s : prop → M → Prop).

    Implicit Types (A : BI_form µ prop) (Γ : BI_bunch µ prop) (s : prop → M → Prop).

    Notation "⟦ A ⟧" := (tps_BI_form s A).

    Lemma tps_IL_ax_sound A : IL_axiom A → ∀x, ⟦A⟧ x.
    Proof.
      induction 1 as [ A B | A B C | A B | A B | A B
                     | A B | A B | A B C | A | ]; intros x; simpl.
      + now intros ? _.
      + intros H ? ?; apply H; auto.
      + now intros [].
      + now intros [].
      + now split.
      + now left.
      + now right.
      + intros ? ? []; auto.
      + intros [].
      + easy.
    Qed.

    Lemma tps_BI_ax_sound A : BI_axiom A → ∀x, ⟦A⟧ x.
    Proof using neut comm assoc.
      induction 1 as [ A | A | A B | A B C ]; intros x; simpl.
      + intros ?; exists e; eauto.
      + intros (? & ? & ? & ? & ?); subst; now rewrite neut.
      + intros (? & ? & ? & ? & ?); subst; rewrite comm; red; eauto.
      + intros (a & ? & ? & ? & b & c & ? & ? & ?); subst.
        rewrite <- assoc; unfold tps_tensor; exists (plus a b), c.
        repeat split; eauto.
    Qed.

    Hint Resolve tps_IL_ax_sound tps_BI_ax_sound : core.

    (** Soundness for trivial phase semantics wrt
        Hilbert proof system HBI *) 

    Theorem tps_HBI_sound A : HBI_provable A → ∀x, ⟦A⟧ x.
    Proof using assoc comm neut.
      induction 1 as [ ? []
                     | A B _ IH1 _ IH2
                     | A B C D _ IH1 _ IH2
                     | A B C _ IH
                     | A B C _ IH
                     ]; simpl in *; auto; intros x.
      + apply IH2, IH1.
      + intros (a & b & -> & []); exists a, b; repeat split; auto.
        * now apply IH1.
        * now apply IH2.
      + intros (a & b & -> & Ha%IH & Hb%Ha).
        now rewrite comm.
      + intros Hx y Hy; rewrite comm; apply IH; red; eauto.
    Qed.

  End HBI.

  Section LBI.

    Variables (µ : BI_conn → bool) (prop : Set) (s : prop → M → Prop).

    Notation µ' := (λ _ : BI_conn, true).

    Implicit Types (A : BI_form µ prop) (Γ : BI_bunch µ prop) (s : prop → M → Prop).

    Notation "⟦ A ⟧" := (tps_BI_form s A).
    Notation "⟦ Γ ⟧ₗ" := (tps_BI_bunch s Γ).

    Fact sem_BI_form_map_id A : 
      ⟦BI_form_map µ' (λ _ _, eq_refl) (λ x : prop, x) A⟧ = ⟦A⟧.
    Proof. induction A as [ | | [] | [] | | ]; simpl; f_equal; auto. Qed.

    Hint Resolve sem_BI_form_map_id : core.

    Fact sem_BI_bunch_form_map Γ :
      ⟦BI_bunch_form (BI_bunch_map µ' (λ _ _, eq_refl) (λ x : prop, x) Γ)⟧ = ⟦Γ⟧ₗ.
    Proof. induction Γ as [ | [] | [] [] ]; simpl; f_equal; auto. Qed. 

    (** Soundness for trivial phase semantics wrt
        any version of LBI *) 

    Theorem tps_LBI_sound b Γ (A : BI_form µ prop) : LBI_provable b Γ A → ⟦Γ⟧ₗ ⊆ ⟦A⟧.
    Proof using neut comm assoc.
      intros H.
      apply BI_map_sound
        with (b' := BI_with_cut)
             (Hµ := λ _ _, eq_refl)
             (φ := λ x : prop, x),
        LBI_to_HBI in H; auto.
      intros x.
      apply tps_HBI_sound with (s := s) (x := x) in H.
      simpl in H.
      rewrite sem_BI_form_map_id,
              sem_BI_bunch_form_map in H; auto.
    Qed.

  End LBI.

End TPS.

Check tps_HBI_sound.
Check tps_LBI_sound.

