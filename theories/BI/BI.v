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

Import ListNotations.

#[local] Infix "∊" := In (at level 70).

Section Logic_Bunched_Implications.

  Inductive BI_kind :=
    | BI_mult
    | BI_addi.

  Inductive BI_side :=
    | BI_left
    | BI_right.

  Inductive BI_cut :=
    | BI_with_cut
    | BI_cut_free.

  Inductive BI_conn :=
    | BI_unit : BI_kind → BI_conn  (* 1  or ⊤ *)
    | BI_conj : BI_kind → BI_conn  (* ∗  or ⩑ *)
    | BI_impl : BI_kind → BI_conn  (* -∗ or ⇒ *)
    | BI_bot  : BI_conn            (* ⊥ *)
    | BI_disj : BI_conn            (* ⩒ *)
    .

  Variables (µ : BI_conn → bool)   (* fragment selection *)
            (prop : Set).          (* type for propositional variables *)

  Inductive BI_form :=
    | BI_form_var    : prop → BI_form
    | BI_form_unit k : µ (BI_unit k) = true → BI_form
    | BI_form_conj k : µ (BI_conj k) = true → BI_form → BI_form → BI_form
    | BI_form_impl k : µ (BI_impl k) = true → BI_form → BI_form → BI_form
    | BI_form_bot    : µ BI_bot = true → BI_form
    | BI_form_disj   : µ BI_disj = true → BI_form → BI_form → BI_form
    .

  Definition BI_form_subst (ρ : prop → BI_form) :=
    fix loop A :=
      match A with
      | BI_form_var v => ρ v
      | BI_form_unit hk => BI_form_unit hk
      | BI_form_conj hk A B => BI_form_conj hk (loop A) (loop B)
      | BI_form_impl hk A B => BI_form_impl hk (loop A) (loop B)
      | BI_form_bot h => BI_form_bot h
      | BI_form_disj h A B => BI_form_disj h (loop A) (loop B)
      end.

  Inductive BI_bunch :=
    | BI_bunch_atom : BI_form → BI_bunch
    | BI_bunch_unit : BI_kind → BI_bunch
    | BI_bunch_comp : BI_kind → BI_bunch → BI_bunch → BI_bunch
    .

  Inductive BI_ctx :=
    | BI_ctx_hole : BI_ctx
    | BI_ctx_comp : BI_side → BI_kind → BI_bunch → BI_ctx → BI_ctx.

  Notation "'ø[' k ']'" := (BI_bunch_unit k) (at level 0, no associativity, format "ø[ k ]").
  Notation "Γ '⊛[' k ']' Δ" := (BI_bunch_comp k Γ Δ) (at level 65, left associativity, format "Γ  ⊛[ k ]  Δ").

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

  Reserved Notation "C [ Δ ]" (at level 1, no associativity, format "C [ Δ ]").

  Fixpoint BI_ctx_fill C Γ :=
    match C with
    | BI_ctx_hole                => Γ
    | BI_ctx_comp BI_left k Δ C  => Δ ⊛[k] C[Γ]
    | BI_ctx_comp BI_right k Δ C => C[Γ] ⊛[k] Δ
    end
  where "Γ [ Δ ]" := (BI_ctx_fill Γ Δ).

  Notation "⟨ A ⟩" := (BI_bunch_atom A) (at level 0, format "⟨ A ⟩").
  Notation "'⊥[' h ']'" := (BI_form_bot h) (at level 0, format "⊥[ h ]").
  Notation "'u[' h ']'" := (@BI_form_unit _ h) (at level 0, format "u[ h ]").
  Notation "A '⊙[' h ']' B" := (@BI_form_conj _ h A B) (at level 59, left associativity, format "A ⊙[ h ] B").
  Notation "A '-⊙[' h ']' B" := (@BI_form_impl _ h A B) (at level 62, right associativity, format "A -⊙[ h ] B").
  Notation "A '⩒[' h ']' B" := (BI_form_disj h A B) (at level 61, left associativity, format "A ⩒[ h ] B").

  Abbreviation øₐ := ø[BI_addi].
  Abbreviation øₘ := ø[BI_mult].

  Notation "Γ '⊛ₐ' Δ" := (Γ ⊛[BI_addi] Δ) (at level 65, left associativity, format "Γ  ⊛ₐ  Δ").
  Notation "Γ '⊛ₘ' Δ" := (Γ ⊛[BI_mult] Δ) (at level 65, left associativity, format "Γ  ⊛ₘ  Δ").

  Reserved Notation "Γ ⊦ A" (at level 70, no associativity, format "Γ  ⊦  A").

  Variable with_cut : BI_cut.

  Inductive LBI_provable : BI_bunch → BI_form → Prop :=

    | BI_sp_axiom A :             (*-------*)
                                    ⟨A⟩ ⊦ A

    | BI_sp_cut (_ : with_cut = BI_with_cut) Γ Δ A B :

                              Γ ⊦ A   →   Δ[⟨A⟩] ⊦ B
                            (*----------------------*)
                          →          Δ[Γ] ⊦ B

    | BI_sp_equiv Γ Δ A :
                                Γ ≡ Δ   →   Γ ⊦ A
                              (*-----------------*)
                          →           Δ ⊦ A

    | BI_sp_weak Γ Δ A :
                                   Γ[øₐ] ⊦ A 
                                 (*---------*)
                         →         Γ[Δ] ⊦ A

    | BI_sp_cntr Γ Δ A :
                                  Γ[Δ ⊛ₐ Δ] ⊦ A
                                (*-------------*)
                         →           Γ[Δ] ⊦ A

    | BI_sp_unit_l k (hk : µ (BI_unit k) = true) Γ A :

                                    Γ[ø[k]] ⊦ A
                                (*--------------*) 
                           →      Γ[⟨u[hk]⟩] ⊦ A

    | BI_sp_unit_r k (hk : µ (BI_unit k) = true) :

                              (*------------*)
                                ø[k] ⊦ u[hk]

    | BI_sp_conj_l k (hk : µ (BI_conj k) = true) Γ A B C :

                                Γ[⟨A⟩ ⊛[k] ⟨B⟩] ⊦ C
                              (*-------------------*)
                             →     Γ[⟨A⊙[hk]B⟩] ⊦ C

    | BI_sp_conj_r k (hk : µ (BI_conj k) = true) Γ Δ A B :

                                Γ ⊦ A   →   Δ ⊦ B 
                              (*-------------------*)
                             →   Γ ⊛[k] Δ ⊦ A⊙[hk]B

    | BI_sp_impl_l k (hk : µ (BI_impl k) = true) Γ Δ A B C :

                                Δ ⊦ A   →   Γ[⟨B⟩] ⊦ C
                              (*----------------------*)
                             →    Γ[Δ ⊛[k] ⟨A-⊙[hk]B⟩] ⊦ C


    | BI_sp_impl_r k (hk : µ (BI_impl k) = true) Γ A B :

                                 Γ ⊛[k] ⟨A⟩ ⊦ B
                               (*--------------*)
                          →       Γ ⊦ A-⊙[hk]B

    | BI_sp_bot_l (h : µ BI_bot = true) A :

                                (*--------------*)
                                   ⟨⊥[h]⟩ ⊦ A

    | BI_sp_disj_l (h : µ BI_disj = true) Γ A B C :

                             Γ[⟨A⟩] ⊦ C   →   Γ[⟨B⟩] ⊦ C
                           (*---------------------------*)
                          →        Γ[⟨A⩒[h]B⟩] ⊦ C

    | BI_sp_disj_r1 (h : µ BI_disj = true) Γ A B :

                                     Γ ⊦ A
                                 (*----------*)
                         →         Γ ⊦ A⩒[h]B

    | BI_sp_disj_r2 (h : µ BI_disj = true) Γ A B :

                                     Γ ⊦ B
                                 (*----------*)
                         →         Γ ⊦ A⩒[h]B

  where "Γ ⊦ A" := (LBI_provable Γ A).

  Definition BI_sequent_problem := BI_form.

  Definition BI_SEQ_PROVABLE (A : BI_sequent_problem) : Prop := ø[BI_addi] ⊦ A.

End Logic_Bunched_Implications.

Section Hilbert_Calculus.

  Variables (prop : Set).

  (* We only consider the full fragment for HBI *)
  Abbreviation µ := (λ _ : BI_conn, true).

  Notation "⊤" := (@BI_form_unit µ _ BI_addi eq_refl).
  Notation "1" := (@BI_form_unit µ _ BI_mult eq_refl).
  Notation "⊥" := (@BI_form_bot µ _ eq_refl).

  Notation "A ∗ B" := (@BI_form_conj µ _ BI_mult eq_refl A B) (at level 59, left associativity, format "A ∗ B").
  Notation "A '-∗' B" := (@BI_form_impl µ _ BI_mult eq_refl A B) (at level 62, right associativity, format "A -∗ B").
  Notation "A ⇒ B" := (@BI_form_impl µ _ BI_addi eq_refl A B) (at level 62, right associativity, format "A ⇒ B").
  Notation "A ⩑ B" := (@BI_form_conj µ _ BI_addi eq_refl A B) (at level 59, left associativity, format "A ⩑ B").
  Notation "A ⩒ B" := (@BI_form_disj µ _ eq_refl A B) (at level 61, left associativity, format "A ⩒ B").

  Reserved Notation "'⊦ᴵ' A" (at level 70, format "⊦ᴵ  A").
  Reserved Notation "'⊦ᴮ' A" (at level 70, format "⊦ᴮ  A").

  Inductive IL_axiom : BI_form µ prop → Prop :=
    | IL_axiom_K A B : ⊦ᴵ A⇒B⇒A
    | IL_axiom_S A B C : ⊦ᴵ (A⇒B⇒C)⇒(A⇒B)⇒(A⇒C)
    | IL_axiom_A1 A B : ⊦ᴵ A⩑B⇒A
    | IL_axiom_A2 A B : ⊦ᴵ A⩑B⇒B
    | IL_axiom_A3 A B : ⊦ᴵ A⇒B⇒A⩑B
    | IL_axiom_O1 A B : ⊦ᴵ A⇒A⩒B
    | IL_axiom_O2 A B : ⊦ᴵ B⇒A⩒B
    | IL_axiom_O3 A B C : ⊦ᴵ (A⇒C)⇒(B⇒C)⇒A⩒B⇒C
    | IL_axiom_B A : ⊦ᴵ ⊥⇒A
    | IL_axiom_T : ⊦ᴵ ⊤
  where "⊦ᴵ A" := (IL_axiom A).

  Inductive BI_axiom : BI_form µ prop → Prop :=
    | BI_axiom_1_r A : ⊦ᴮ A⇒1∗A
    | BI_axiom_1_l A : ⊦ᴮ 1∗A⇒A
    | BI_axiom_comm A B : ⊦ᴮ A∗B⇒B∗A
    | BI_axiom_assoc A B C : ⊦ᴮ A∗(B∗C)⇒(A∗B)∗C
  where "⊦ᴮ A" := (BI_axiom A).

  Reserved Notation "Φ I⊦ A" (at level 70, format "Φ  I⊦  A").
  Reserved Notation "Φ ⊦ A" (at level 70, format "Φ  ⊦  A").

  Inductive HIL_deduction Φ : BI_form µ prop → Prop :=
    | HIL_axiom A : Φ A → Φ I⊦ A
    | HIL_modus_ponens A B : Φ I⊦ A → Φ I⊦ A⇒B → Φ I⊦ B
  where "Φ I⊦ A" := (HIL_deduction Φ A).

  Inductive HBI_deduction Φ : BI_form µ prop → Prop :=
    | HBI_axiom A : Φ A → Φ ⊦ A
    | HBI_mp A B : Φ ⊦ A → Φ ⊦ A⇒B → Φ ⊦ B
    | HBI_mult A B C D : Φ ⊦ A⇒C → Φ ⊦ B⇒D → Φ ⊦ (A∗B)⇒(C∗D)
    | HBI_wand_1 A B C : Φ ⊦ A⇒(B-∗C) → Φ ⊦ (A∗B)⇒C
    | HBI_wand_2 A B C : Φ ⊦ (A∗B)⇒C → Φ ⊦ A⇒(B-∗C)
  where "Φ ⊦ A" := (HBI_deduction Φ A).

  Definition HBI_provable := HBI_deduction (λ A, ⊦ᴵ A ∨ ⊦ᴮ A).

  Definition BI_hilbert_problem := BI_form µ prop.

  Definition BI_HILBERT_PROVABLE (p : BI_hilbert_problem) := HBI_provable p.

End Hilbert_Calculus.

Arguments IL_axiom {_}.
Arguments BI_axiom {_}.

Module BI_notations.

  Notation "x ≡ y" := (BI_bunch_equiv x y) (at level 70, no associativity, format "x  ≡  y").
  Notation "C [ Δ ]" := (BI_ctx_fill C Δ) (at level 1, no associativity, format "C [ Δ ]").
  Notation "Γ 'L⊦[' b ']' A" := (LBI_provable b Γ A) (at level 70, no associativity, format "Γ  L⊦[ b ]  A").

  Notation "⟨ A ⟩" := (BI_bunch_atom A) (at level 0, format "⟨ A ⟩"). 

  Notation "'ø[' k ']'" := (BI_bunch_unit _ _ k) (at level 0, no associativity, format "ø[ k ]").
  Notation "Γ '⊛[' k ']' Δ" := (BI_bunch_comp k Γ Δ) (at level 65, left associativity, format "Γ  ⊛[ k ]  Δ").

  Abbreviation øₐ := ø[BI_addi].
  Abbreviation øₘ := ø[BI_mult].
  Notation "Γ '⊛ₐ' Δ" := (Γ ⊛[BI_addi] Δ) (at level 65, left associativity, format "Γ  ⊛ₐ  Δ").
  Notation "Γ '⊛ₘ' Δ" := (Γ ⊛[BI_mult] Δ) (at level 65, left associativity, format "Γ  ⊛ₘ  Δ").

  Notation "'H⊦' A" := (HBI_provable A) (at level 70, no associativity, format "H⊦  A").

(*
  Notation "⊤" := (@BI_form_unit _ BI_addi).
  Notation "1" := (@BI_form_unit _ BI_mult).
  Notation "£ v" := (@BI_form_var _ v) (at level 1, format "£ v").
  Notation "A '-∗' B" := (@BI_form_imp _ BI_mult A B) (at level 60, right associativity, format "A -∗ B").
  Notation "A ⇒ B" := (@BI_form_imp _ BI_addi A B) (at level 60, right associativity, format "A ⇒ B").
  Notation "A ⩑ B" := (@BI_form_conj _ A B) (at level 59, left associativity, format "A ⩑ B").

  Notation "⟨ A ⟩" := (@BI_bunch_atom _ A) (at level 0, format "⟨ A ⟩"). 
  Notation "'ø[' k ']'" := (@BI_bunch_unit _ k) (at level 0, format "ø[ k ]").
  Abbreviation øₐ := ø[BI_addi].
  Abbreviation øₘ := ø[BI_mult].

  Notation "Γ '⊛[' k ']' Δ" := (@BI_bunch_comp _ k Γ Δ) (at level 65, left associativity, format "Γ  ⊛[ k ]  Δ").
  Notation "Γ '⊛ₐ' Δ" := (@BI_bunch_comp _ BI_addi Γ Δ) (at level 65, left associativity, format "Γ  ⊛ₐ  Δ").
  Notation "Γ '⊛ₘ' Δ" := (@BI_bunch_comp _ BI_mult Γ Δ) (at level 65, left associativity, format "Γ  ⊛ₘ  Δ").

  Notation "Γ ≡ Δ" := (@BI_bunch_equiv _ Γ Δ) (at level 70, no associativity, format "Γ  ≡  Δ").
  Notation "Γ [ Δ ]" := (@BI_ctx_fill _ Γ Δ) (at level 1, no associativity, format "Γ [ Δ ]").
  Notation "Γ ⊦ A" := (BI_seq_provable_cut_free Γ A) (at level 70).
  
  *)

End BI_notations.

  
   