(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

Set Implicit Arguments.

Section Logic_Bunched_Implications.

  Variable prop : Type.
 
  Inductive BI_kind := BI_mult | BI_addi.

  Inductive BI_form :=
    | BI_form_var  : prop → BI_form
    | BI_form_unit : BI_kind → BI_form
    | BI_form_imp  : BI_kind → BI_form → BI_form → BI_form
    | BI_form_conj : BI_form → BI_form → BI_form.

  Notation "⊤" := (BI_form_unit BI_addi).
  Notation "1" := (BI_form_unit BI_mult).
  Notation "£ v" := (BI_form_var v) (at level 1, format "£ v").
  Notation "A '-∗' B" := (BI_form_imp BI_mult A B) (at level 60, right associativity, format "A -∗ B").
  Notation "A ⇒ B" := (BI_form_imp BI_addi A B) (at level 60, right associativity, format "A ⇒ B").
  Notation "A ⩑ B" := (BI_form_conj A B) (at level 59, left associativity, format "A ⩑ B").

  Inductive BI_bunch :=
    | BI_bunch_atom : BI_form → BI_bunch
    | BI_bunch_unit : BI_kind → BI_bunch
    | BI_bunch_comp : BI_kind → BI_bunch → BI_bunch → BI_bunch.

  Notation "⟨ A ⟩" := (BI_bunch_atom A) (at level 0). 
  Notation "'ø[' k ']'" := (BI_bunch_unit k) (at level 0).
  Notation øₐ := ø[BI_addi].
  Notation øₘ := ø[BI_mult].

  Notation "Γ '⊛[' k ']' Δ" := (BI_bunch_comp k Γ Δ) (at level 65, left associativity, format "Γ  ⊛[ k ]  Δ").
  Notation "Γ '⊛ₐ' Δ" := (BI_bunch_comp BI_addi Γ Δ) (at level 65, left associativity, format "Γ  ⊛ₐ  Δ").
  Notation "Γ '⊛ₘ' Δ" := (BI_bunch_comp BI_mult Γ Δ) (at level 65, left associativity, format "Γ  ⊛ₘ  Δ").

  Reserved Notation "x ≡ y" (at level 70, no associativity, format "x  ≡  y").

  Inductive BI_bunch_equiv : BI_bunch → BI_bunch → Prop :=
    | BI_bequiv_refl Γ : Γ ≡ Γ
    | BI_bequiv_sym Γ Δ : Γ ≡ Δ → Δ ≡ Γ
    | BI_bequiv_trans Γ Δ Θ : Γ ≡ Δ → Δ ≡ Θ → Γ ≡ Θ
    | BI_bequiv_neut k Γ : ø[k] ⊛[k] Γ ≡ Γ
    | BI_bequiv_comm k Γ Δ : Γ ⊛[k] Δ ≡ Δ ⊛[k] Γ
    | BI_bequiv_assoc k Γ Δ Θ : (Γ ⊛[k] Δ) ⊛[k] Θ ≡ Γ ⊛[k] (Δ ⊛[k] Θ)
    | BI_bequiv_congr k Γ Δ Θ : Δ ≡ Θ → Γ ⊛[k] Δ ≡ Γ ⊛[k] Θ
  where "Γ ≡ Δ" := (BI_bunch_equiv Γ Δ).

  Inductive BI_ctx :=
    | BI_ctx_hole : BI_ctx
    | BI_ctx_comp : bool → BI_kind → BI_bunch → BI_ctx → BI_ctx.

  Reserved Notation "C [ Δ ]" (at level 1, no associativity, format "C [ Δ ]").

  Fixpoint BI_ctx_fill C Γ :=
    match C with
    | BI_ctx_hole             => Γ
    | BI_ctx_comp true k Δ C  => Δ ⊛[k] C[Γ]
    | BI_ctx_comp false k Δ C => C[Γ] ⊛[k] Δ
    end
  where "Γ [ Δ ]" := (BI_ctx_fill Γ Δ).

  Reserved Notation "Γ ⊦ A" (at level 70, no associativity, format "Γ  ⊦  A").

  Inductive BI_seq_provable_cut_free : BI_bunch → BI_form → Prop :=
    | BI_spcf_axiom A :       (*-----------------*)
                                    ⟨A⟩ ⊦ A

    | BI_spcf_equiv Γ Δ A :     Γ ≡ Δ   →   Γ ⊦ A
                              (*-----------------*)
                          →           Δ ⊦ A

    | BI_spcf_weak Γ Δ A :          Γ[øₐ] ⊦ A 
                              (*-----------------*)
                         →           Γ[Δ] ⊦ A

    | BI_spcf_cntr Γ Δ A :        Γ[Δ ⊛ₐ Δ] ⊦ A
                              (*-----------------*)
                         →         Γ[Δ] ⊦ A

    | BI_spcf_top_l Γ A :          Γ[øₐ] ⊦ A
                              (*-----------------*)
                        →          Γ[⟨⊤⟩] ⊦ A

    | BI_spcf_top_r :         (*-----------------*)
                                     øₐ ⊦ ⊤

    | BI_spcf_unit_l Γ A :          Γ[øₘ] ⊦ A
                              (*-----------------*) 
                         →         Γ[⟨1⟩] ⊦ A

    | BI_spcf_unit_r :        (*-----------------*)
                                     øₘ ⊦ 1

    | BI_spcf_conj_l Γ A B C :  Γ[⟨A⟩ ⊛ₐ ⟨B⟩] ⊦ C
                              (*-----------------*)
                             →    Γ[⟨A⩑B⟩] ⊦ C

    | BI_spcf_conj_r Γ Δ A B :  Γ ⊦ A   →   Δ ⊦ B 
                              (*-----------------*)
                             →    Γ ⊛ₐ Δ ⊦ A⩑B

    | BI_spcf_imp_l Γ Δ A B C : Δ ⊦ A   →   Γ[⟨B⟩] ⊦ C
                              (*----------------------*)
                             →    Γ[Δ ⊛ₐ ⟨A⇒B⟩] ⊦ C

    | BI_spcf_imp_r Γ A B :         Γ ⊛ₐ ⟨A⟩ ⊦ B
                              (*----------------------*)
                          →           Γ ⊦ A⇒B

    | BI_spcf_wand_l Γ Δ A B C : Δ ⊦ A   →   Γ[⟨B⟩] ⊦ C
                              (*-----------------------*)
                             →    Γ[Δ ⊛ₘ ⟨A-∗B⟩] ⊦ C

    | BI_spcf_wand_r Γ A B :         Γ ⊛ₘ ⟨A⟩ ⊦ B
                              (*----------------------*)
                          →            Γ ⊦ A-∗B 

  where "Γ ⊦ A" := (BI_seq_provable_cut_free Γ A).

  Definition BI_sequent_problem := (BI_bunch * BI_form)%type.

  Definition BI_SEQ_PROVABLE_cut_free (p : BI_sequent_problem) : Prop := 
    match p with (Γ,A) => Γ ⊦ A end.

End Logic_Bunched_Implications.

Module BI_notations.

  Notation "⊤" := (@BI_form_unit _ BI_addi).
  Notation "1" := (@BI_form_unit _ BI_mult).
  Notation "£ v" := (@BI_form_var _ v) (at level 1, format "£ v").
  Notation "A '-∗' B" := (@BI_form_imp _ BI_mult A B) (at level 60, right associativity, format "A -∗ B").
  Notation "A ⇒ B" := (@BI_form_imp _ BI_addi A B) (at level 60, right associativity, format "A ⇒ B").
  Notation "A ⩑ B" := (@BI_form_conj _ A B) (at level 59, left associativity, format "A ⩑ B").

  Notation "⟨ A ⟩" := (@BI_bunch_atom _ A) (at level 0, format "⟨ A ⟩"). 
  Notation "'ø[' k ']'" := (@BI_bunch_unit _ k) (at level 0, format "ø[ k ]").
  Notation øₐ := ø[BI_addi].
  Notation øₘ := ø[BI_mult].

  Notation "Γ '⊛[' k ']' Δ" := (@BI_bunch_comp _ k Γ Δ) (at level 65, left associativity, format "Γ  ⊛[ k ]  Δ").
  Notation "Γ '⊛ₐ' Δ" := (@BI_bunch_comp _ BI_addi Γ Δ) (at level 65, left associativity, format "Γ  ⊛ₐ  Δ").
  Notation "Γ '⊛ₘ' Δ" := (@BI_bunch_comp _ BI_mult Γ Δ) (at level 65, left associativity, format "Γ  ⊛ₘ  Δ").

  Notation "Γ ≡ Δ" := (@BI_bunch_equiv _ Γ Δ) (at level 70, no associativity, format "Γ  ≡  Δ").
  Notation "Γ [ Δ ]" := (@BI_ctx_fill _ Γ Δ) (at level 1, no associativity, format "Γ [ Δ ]").
  Notation "Γ ⊦ A" := (BI_seq_provable_cut_free Γ A) (at level 70).

End BI_notations.


  
   