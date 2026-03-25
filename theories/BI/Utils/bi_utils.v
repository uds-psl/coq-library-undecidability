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
  Require Import BI.

Import BI_notations.

Set Implicit Arguments.

Arguments BI_ctx_hole {_}.

Section pseudo_exponential.

  Variables prop : Type.

  Implicit Types (φ : BI_form prop).

  Definition BI_pseudo_exp γ φ := (⊤-∗((φ-∗γ)⇒γ))⩑1.

  Notation "'![' γ ']' φ" := (BI_pseudo_exp γ φ) (at level 1, format "![ γ ] φ").

  Fact BI_pseudo_exp_weak Γ γ φ :
             Γ ⊦ γ 
      (*------------------*)
    →    Γ ⊛ₘ ⟨![γ]φ⟩ ⊦ γ.
  Proof.
    intros H.
    set (Δ := BI_ctx_comp true BI_mult Γ BI_ctx_hole).
    change (Δ[⟨![γ]φ⟩] ⊦ γ).
    apply BI_spcf_conj_l.
    set (Δ' := BI_ctx_comp true BI_mult Γ (BI_ctx_comp false BI_addi ⟨1⟩ BI_ctx_hole)).
    change (Δ'[⟨⊤-∗(φ-∗γ)⇒γ⟩] ⊦ γ).
    apply BI_spcf_weak.
    change (Δ[øₐ ⊛ₐ ⟨1⟩] ⊦ γ).
    apply BI_spcf_equiv with Δ[⟨1⟩].
    1: apply BI_bequiv_congr, BI_bequiv_sym, BI_bequiv_neut.
    apply BI_spcf_unit_l.
    simpl.
    revert H; apply BI_spcf_equiv.
    apply BI_bequiv_sym,
          BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _),
          BI_bequiv_neut.
  Qed.

  Fact BI_pseudo_exp_derilection Γ γ φ :
          Γ ⊛ₘ ⟨![γ]φ⟩ ⊛ₘ ⟨φ⟩ ⊦ γ
        (*-----------------------*)
    →        Γ ⊛ₘ ⟨![γ]φ⟩ ⊦ γ.
  Proof.
    intros H.
    set (Δ₁ := @BI_ctx_hole prop).
    change (Δ₁[Γ ⊛ₘ ⟨![γ]φ⟩] ⊦ γ).
    apply BI_spcf_cntr; simpl.
  Admitted.

End pseudo_exponential.


