(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8 Permutation.

From Undecidability.BI
  Require Import BI.

Import BI_notations.

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

Arguments BI_ctx_hole {_}.

Section pseudo_exponential.

  Variables prop : Type.

  Implicit Types (φ : BI_form prop) (Γ : BI_bunch prop).

  Definition BI_pseudo_exp γ φ := (⊤-∗((φ-∗γ)⇒γ))⩑1.

  Notation "'![' γ ']' φ" := (BI_pseudo_exp γ φ) (at level 1, format "![ γ ] φ").

  Fact BI_top_weak Γ : Γ ⊦ ⊤.
  Proof.
    change (BI_ctx_hole[Γ] ⊦ ⊤).
    apply BI_spcf_weak, BI_spcf_top_r.
  Qed.

  Fact BI_cntr_all Γ γ : Γ ⊛ₐ Γ ⊦ γ → Γ ⊦ γ.
  Proof.
    intros H.
    change (BI_ctx_hole[Γ] ⊦ γ).
    now apply BI_spcf_cntr.
  Qed.

  Lemma BI_pseudo_exp_weak Γ γ φ ψ :
             Γ ⊦ ψ 
      (*------------------*)
    →    Γ ⊛ₘ ⟨![γ]φ⟩ ⊦ ψ.
  Proof.
    intros H.
    set (Δ := BI_ctx_comp true BI_mult Γ BI_ctx_hole).
    change (Δ[⟨![γ]φ⟩] ⊦ ψ).
    apply BI_spcf_conj_l.
    set (Δ' := BI_ctx_comp true BI_mult Γ (BI_ctx_comp false BI_addi ⟨1⟩ BI_ctx_hole)).
    change (Δ'[⟨⊤-∗(φ-∗γ)⇒γ⟩] ⊦ ψ).
    apply BI_spcf_weak.
    change (Δ[øₐ ⊛ₐ ⟨1⟩] ⊦ ψ).
    apply BI_spcf_equiv with Δ[⟨1⟩].
    1: apply BI_bequiv_congr, BI_bequiv_sym, BI_bequiv_neut.
    apply BI_spcf_unit_l.
    simpl.
    revert H; apply BI_spcf_equiv.
    apply BI_bequiv_sym,
          BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _),
          BI_bequiv_neut.
  Qed.

  Definition BI_list_mult := fold_right (λ φ Γ, ⟨φ⟩ ⊛ₘ Γ) øₘ.

  Hint Constructors BI_bunch_equiv : core.

  Fact BI_list_mult_perm_bequiv l m :
    l ~p m → BI_list_mult l ≡ BI_list_mult m.
  Proof. induction 1; simpl; eauto. Qed.

  Theorem BI_list_mult_weak Σ Γ ψ :
      (∀A, A ∊ Σ → ∃ γ φ, A = ![γ]φ)
    → Γ ⊦ ψ 
    → (BI_list_mult Σ) ⊛ₘ Γ ⊦ ψ.
  Proof.
    intros H1%Forall_forall H; revert H1.
    induction 1 as [ | A Σ (γ & φ & ->) _ IH ]; simpl.
    + revert H; apply BI_spcf_equiv.
      apply BI_bequiv_sym, BI_bequiv_neut.
    + apply BI_spcf_equiv with (1 := BI_bequiv_sym (BI_bequiv_assoc _ _ _ _)),
            BI_spcf_equiv with (1 := BI_bequiv_comm _ _ _),
            BI_pseudo_exp_weak; trivial.
  Qed.

  Fact BI_first_idea Γ γ φ : Γ ⊛ₘ ⟨φ⟩ ⊦ γ → Γ ⊛ₐ ⟨(φ-∗γ)⇒γ⟩ ⊦ γ.
  Proof.
    intros H.
    change (BI_ctx_hole[Γ ⊛ₐ ⟨(φ-∗γ)⇒γ⟩] ⊦ γ).
    apply BI_spcf_imp_l.
    + now apply BI_spcf_wand_r.
    + simpl; apply BI_spcf_axiom.
  Qed.

  Fact BI_second_idea Γ γ φ :
    (Γ ⊛ₘ ⟨(⊤-∗φ)⩑1⟩) ⊛ₐ ⟨φ⟩ ⊦ γ → Γ ⊛ₘ ⟨(⊤-∗φ)⩑1⟩ ⊦ γ.
  Proof.
    set (Δ := Γ ⊛ₘ ⟨(⊤-∗φ)⩑1⟩).
    intros H.
    apply BI_cntr_all.
    unfold Δ at 2.
    set (Δ' := BI_ctx_comp true BI_addi Δ
              (BI_ctx_comp true BI_mult Γ BI_ctx_hole)).
    change (Δ'[⟨(⊤-∗φ)⩑1⟩] ⊦ γ).
    apply BI_spcf_conj_l.
    set (Δ'' := BI_ctx_comp true BI_addi Δ
               (BI_ctx_comp true BI_mult Γ 
               (BI_ctx_comp true BI_addi ⟨⊤-∗φ⟩
                BI_ctx_hole))).
    change (Δ''[⟨1⟩] ⊦ γ).
    apply BI_spcf_weak.
    change (Δ'[⟨⊤-∗φ⟩ ⊛ₐ øₐ] ⊦ γ).
    apply BI_spcf_equiv with (Δ'[⟨⊤-∗φ⟩]).
    1: apply BI_bequiv_congr, BI_bequiv_congr, BI_bequiv_sym,
             BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _),
             BI_bequiv_neut.
    set (Δ''' := BI_ctx_comp true BI_addi Δ BI_ctx_hole).
    change (Δ'''[Γ ⊛ₘ ⟨⊤-∗φ⟩] ⊦ γ).
    apply BI_spcf_wand_l; auto.
    apply BI_top_weak.
  Qed.

  Lemma BI_pseudo_exp_derilection Γ γ φ :
          Γ ⊛ₘ ⟨![γ]φ⟩ ⊛ₘ ⟨φ⟩ ⊦ γ
        (*-----------------------*)
    →        Γ ⊛ₘ ⟨![γ]φ⟩ ⊦ γ.
  Proof.
    intros H.
    unfold BI_pseudo_exp.
    apply BI_second_idea.
    apply BI_first_idea.
    trivial.
  Qed.

  Check BI_pseudo_exp_weak.
  Check BI_pseudo_exp_derilection.

  Theorem BI_list_mult_derilection Σ γ φ :
      ![γ]φ ∊ Σ
    → (BI_list_mult Σ) ⊛ₘ ⟨φ⟩ ⊦ γ 
    → (BI_list_mult Σ) ⊦ γ.
  Proof.
    intros (Σ' & H'%BI_list_mult_perm_bequiv)%permutation_in_head H.
    apply BI_spcf_equiv with (1 := BI_bequiv_sym H').
    simpl.
    apply BI_spcf_equiv with (1 := BI_bequiv_comm _ _ _).
    apply BI_pseudo_exp_derilection.
    revert H; apply BI_spcf_equiv.
    do 2 apply BI_bequiv_sym, BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _).
    apply BI_bequiv_congr.
    apply BI_bequiv_trans with (1 := H'), BI_bequiv_comm.
  Qed.

  Check BI_list_mult_weak.
  Check BI_list_mult_derilection.

End pseudo_exponential.

#[local] Reserved Notation "x -∘ y" (at level 67, right associativity, format "x -∘ y").
#[local] Reserved Notation "x ⊏ y" (at level 67, right associativity, format "x ⊏ y").
#[local] Reserved Notation "x ∘ y"  (at level 64, left associativity, format "x ∘ y").
#[local] Reserved Notation "x ⊓ y"  (at level 62, left associativity, format "x ⊓ y"). 

Section TPS.

  Variables (M : Type) (plus : M → M → M) (e : M)
            (neut : ∀x, plus e x = x)
            (comm : ∀ x y, plus x y = plus y x)
            (assoc : ∀ x y z, plus (plus x y) z = plus x (plus y z)).

  Local Definition tps_lolipop (X Y : M → Prop) x := ∀a, X a → Y (plus a x).
  Local Definition tps_impl (X Y : M → Prop) x := X x → Y x.
  Local Definition tps_tensor (X Y : M → Prop) x := ∃ a b, x = plus a b ∧ X a ∧ Y b. 
  Local Definition tps_with (X Y : M → Prop) x := X x ∧ Y x.

  Infix "-∘" := tps_lolipop.
  Infix "⊏" := tps_impl.
  Infix "∘" := tps_tensor.
  Infix "⊓" := tps_with.

  Variables (prop : Type) (s : prop → M → Prop).

  Reserved Notation "⟦ x ⟧" (at level 0, format "⟦ x ⟧").
  Reserved Notation "⟦ x ⟧ₗ" (at level 0, format "⟦ x ⟧ₗ").

  Fixpoint tps_BI_form (A : BI_form prop) : M → Prop :=
    match A with
    | £v   => s v
    | ⊤    => λ _, True
    | 1    => eq e
    | A⇒B  => ⟦A⟧ ⊏ ⟦B⟧
    | A-∗B => ⟦A⟧ -∘ ⟦B⟧
    | A⩑B  => ⟦A⟧ ⊓ ⟦B⟧
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

  Lemma tps_BI_ctx_mono Σ Γ Δ : ⟦Γ⟧ₗ ⊆ ⟦Δ⟧ₗ → ⟦Σ[Γ]⟧ₗ ⊆ ⟦Σ[Δ]⟧ₗ.
  Proof.
    intros H.
    induction Σ as [ | [] [] Θ ]; simpl; auto.
    1,3: intros x (a & b & -> & ? & ?); exists a, b; auto.
    all: intros ? []; split; auto.
  Qed.

  (** Soundness for trivial phase semantics wrt 
      cut-free bunched sequent calculus for BI *)
  Theorem tps_BI_sound Γ A : Γ ⊦ A → ⟦Γ⟧ₗ ⊆ ⟦A⟧.
  Proof using assoc comm neut.
    induction 1 as [
                   | Γ Δ A H _ IH
                   | Γ Δ A _ IH
                   | Γ Δ A _ IH
                   | Γ A _ IH
                   |
                   | Γ A _ IH 
                   |
                   | Γ A B C _ IH
                   | Γ Δ A B _ IH1 _ IH2
                   | Γ Δ A B C _ IH1 _ IH2
                   | Γ A B _ IH
                   | Γ Δ A B C _ IH1 _ IH2
                   | Γ A B _ IH
                   ]; simpl; eauto.
    2-6: intros x H; apply IH; revert H; apply tps_BI_ctx_mono; now simpl.
    + intros x ?; apply IH; now apply tps_BI_equiv with (1 := H).
    + intros x []; split; auto.
    + intros x H; apply IH2; revert x H; apply tps_BI_ctx_mono.
      intros ? (?%IH1 & H); now apply H.
    + intros ? ? ?; apply IH; now split.
    + intros x H; apply IH2; revert x H; apply tps_BI_ctx_mono.
      intros ? (? & ? & -> & ?%IH1 & H); apply H; auto.
    + intros x ? y ?; apply IH; exists x, y; now rewrite comm.
  Qed.

End TPS.




