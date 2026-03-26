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

  Lemma BI_pseudo_exp_weak Γ γ φ :
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

End pseudo_exponential.


