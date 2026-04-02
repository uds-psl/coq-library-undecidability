(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Utf8 Eqdep_dec.

From Undecidability.BI
  Require Import BI utils hil.

Import BI_notations.

Set Implicit Arguments.

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70).

Section LBI_full_HBI.

  Variables (prop : Set).

  Abbreviation µ := (λ _ : BI_conn, true).

  Implicit Type (Φ : BI_form µ prop → Prop).

  (** We show that what can be proved in the full fragment of LBI
     (incl. with the cut-rule) can also be proved in HBI *)

  Notation "⊥" := (@BI_form_bot _ _ eq_refl).
  Notation "⊤" := (@BI_form_unit _ _ BI_addi eq_refl).
  Notation "1" := (@BI_form_unit _ _ BI_mult eq_refl).
  Notation "A ⇒ B" := (@BI_form_impl _ _ BI_addi eq_refl A B) (at level 63, right associativity, format "A ⇒ B").
  Notation "A '-∗' B" := (@BI_form_impl _ _ BI_mult eq_refl A B) (at level 63, right associativity, format "A -∗ B").
  Notation "A ∗ B" := (@BI_form_conj _ _ BI_mult eq_refl A B) (at level 59, left associativity, format "A ∗ B").
  Notation "A ⩑ B" := (@BI_form_conj _ _ BI_addi eq_refl A B) (at level 59, left associativity, format "A ⩑ B").
  Notation "A ⩒ B" := (@BI_form_disj _ _ eq_refl A B) (at level 61, left associativity, format "A ⩒ B").

  Implicit Types (A B : BI_form µ prop).

  Hint Constructors HBI_deduction IL_axiom BI_axiom : core.

  Theorem HIL_incl_HBI Φ : HIL_deduction Φ ⊆ HBI_deduction Φ.
  Proof. induction 1; eauto. Qed.

  Notation "Σ 'L⊦wc' A" := (@LBI_provable µ prop BI_with_cut Σ A) (at level 70, format "Σ  L⊦wc  A").

  (* We start by importing the proof theory of HIL into HBI *)

  Tactic Notation "solve" "with" constr(H) :=
     apply HIL_incl_HBI;
     apply HIL_mono with (@IL_axiom _); eauto using H.

  Fact HBI_K' A B : H⊦ A⇒B⇒A.
  Proof. solve with HIL_K. Qed.

  Fact HBI_id A : H⊦ A⇒A.
  Proof. solve with HIL_id. Qed.

  Fact HBI_MP A B : H⊦ A → H⊦ A⇒B → H⊦ B.
  Proof. constructor 2 with A; auto. Qed.

  Fact HBI_S A B C : H⊦ A⇒B⇒C → H⊦ A⇒B → H⊦ A⇒C.
  Proof.
    intros H1 H2.
    apply HBI_MP with (1 := H2),
          HBI_MP with (1 := H1).
    solve with HIL_S. 
  Qed.

  Fact HBI_weak_l A B : H⊦ B → H⊦ A⇒B.
  Proof.
    intros H1.
    apply HBI_MP with (1 := H1).
    solve with HIL_K.
  Qed.

  Hint Resolve HBI_S HBI_id HBI_weak_l : core.

  Fact HBI_S' A B C : H⊦ A⇒B⇒C → H⊦ A⇒B → H⊦ A → H⊦ C.
  Proof.
    intros H1 H2 H3.
    apply HBI_MP with (1 := H3); eauto.
  Qed.

  Hint Resolve HBI_S' : core.

  Fact HBI_trans A B C : H⊦ A⇒B → H⊦ B⇒C → H⊦ A⇒C.
  Proof.
    intros H1 H2.
    apply HBI_MP with (1 := H2),
          HBI_MP with (1 := H1).
    solve with HIL_imp_trans.
  Qed.

  Fact HBI_weak_r A B C : H⊦ A⇒C → H⊦ A⇒B⇒C.
  Proof. 
    intros H.
    apply HBI_MP with (1 := H).
    solve with HIL_weak_r.
  Qed.

  Fact HBI_conj_mono A B C D : H⊦ A⇒C → H⊦ B⇒D → H⊦ A⩑B⇒C⩑D.
  Proof.
    intros H1 H2.
    apply HBI_MP with (1 := H2),
          HBI_MP with (1 := H1).
    solve with HIL_conj_mono.
  Qed.

  Fact HBI_conj_assoc_1 A B C : H⊦ A⩑(B⩑C)⇒(A⩑B)⩑C.
  Proof. solve with HIL_conj_assoc_1. Qed.

  Fact HBI_conj_assoc_2 A B C : H⊦ (A⩑B)⩑C⇒A⩑(B⩑C).
  Proof. solve with HIL_conj_assoc_2. Qed.

  Fact HBI_conj_comm A B : H⊦ A⩑B⇒B⩑A.
  Proof. solve with HIL_conj_comm. Qed.

  Fact HBI_conj_top A : H⊦ A⇒⊤⩑A.
  Proof. solve with HIL_conj_top. Qed.

  Fact HBI_conj_idem A : H⊦ A⇒A⩑A.
  Proof. solve with HIL_conj_idem. Qed.

  Fact HBI_imp_adj_1_form A B C : H⊦ (A⇒B⇒C)⇒(A⩑B⇒C).
  Proof. solve with HIL_imp_adj_1. Qed.

  Fact HBI_imp_adj_2_form A B C : H⊦ (A⩑B⇒C)⇒(A⇒B⇒C).
  Proof. solve with HIL_imp_adj_2. Qed.

  Fact HBI_imp_adj A B : H⊦ (A⩑(A⇒B))⇒B.
  Proof. solve with HIL_imp_adj. Qed.

  Fact HBI_imp_adj_1 A B C : H⊦ A⇒B⇒C → H⊦ (A⩑B⇒C).
  Proof. intros; now apply HBI_MP with (2 := HBI_imp_adj_1_form _ _ _). Qed.

  Fact HBI_imp_adj_2 A B C : H⊦ A⩑B⇒C → H⊦ A⇒B⇒C.
  Proof. intros; now apply HBI_MP with (2 := HBI_imp_adj_2_form _ _ _). Qed.

  Fact HBI_top_conj_1_l A : H⊦ ⊤⩑A⇒A.
  Proof. apply HBI_imp_adj_1, HBI_weak_l, HBI_id. Qed.

  Fact HBI_top_conj_2_l A : H⊦ A⇒⊤⩑A.
  Proof. apply HBI_conj_top. Qed.

  Fact HBI_imp_anti_mono A B C D : H⊦ (A⇒B)⇒(C⇒D)⇒(B⇒C)⇒(A⇒D).
  Proof. solve with HIL_imp_anti_mono. Qed.

  Fact HBI_top_intro : H⊦ (⊤ : BI_form µ prop).
  Proof. solve with HIL_top_r. Qed.

  Fact HBI_bot_elim A : H⊦ ⊥⇒A.
  Proof. solve with HIL_bot_l. Qed.

  Fact HBI_bot_conj_l A : H⊦ ⊥⩑A⇒⊥.
  Proof. solve with HIL_bot_conj_l. Qed.

  Fact HBI_bot_conj_r A : H⊦ A⩑⊥⇒⊥.
  Proof. solve with HIL_bot_conj_r. Qed.

  Fact HBI_disj_lub A B C :
      H⊦ A⇒C
    → H⊦ B⇒C
    → H⊦ A⩒B⇒C.
  Proof. 
    intros H1 H2.
    apply HBI_MP with (1 := H2),
          HBI_MP with (1 := H1).
    solve with HIL_disj_lub.
  Qed.

  Fact HBI_conj_disj_l A B C : H⊦ (B⩒C)⩑A⇒(B⩑A)⩒(C⩑A).
  Proof. solve with HIL_conj_disj_l. Qed.

  Fact HBI_conj_disj_r A B C : H⊦ A⩑(B⩒C)⇒(A⩑B)⩒(A⩑C).
  Proof. solve with HIL_conj_disj_r. Qed.

  Fact HBI_disj_intro_l A B : H⊦ A⇒A⩒B.
  Proof. solve with HIL_disj_l. Qed.

  Fact HBI_disj_intro_r A B : H⊦ B⇒A⩒B.
  Proof. solve with HIL_disj_r. Qed.

  (** We now switch to the multiplicative part
      where we cannot import the proof theory of HIL *)

  (* first rules and axioms *)

  Fact HBI_mult_mono A B C D : H⊦ A⇒C → H⊦ B⇒D → H⊦ (A∗B)⇒(C∗D).
  Proof. constructor 3; auto. Qed.

  Fact HBI_mult_comm A B : H⊦ A∗B⇒B∗A.
  Proof. constructor 1; eauto. Qed.

  Fact HBI_mult_assoc_1 A B C : H⊦ A∗(B∗C)⇒(A∗B)∗C.
  Proof. constructor 1; eauto. Qed.

  Fact HBI_wand_adj_1 A B C : H⊦ A⇒(B-∗C) → H⊦ (A∗B)⇒C.
  Proof. now constructor 4. Qed.

  Fact HBI_wand_adj_2 A B C : H⊦ (A∗B)⇒C → H⊦ A⇒(B-∗C).
  Proof. now constructor 5. Qed.

  Fact HBI_unit_mult_1_l A : H⊦ 1∗A⇒A.
  Proof. constructor 1; auto. Qed.

  Fact HBI_unit_mult_2_l A : H⊦ A⇒1∗A.
  Proof. constructor 1; auto. Qed.

  (* Now derived theorems *)

  Fact HBI_mult_assoc_2 A B C : H⊦ (A∗B)∗C⇒A∗(B∗C).
  Proof.
    apply HBI_trans with (1 := HBI_mult_comm _ _),
          HBI_trans with (1 := HBI_mult_assoc_1 _ _ _),
          HBI_trans with (1 := HBI_mult_comm _ _),
          HBI_trans with (1 := HBI_mult_assoc_1 _ _ _),
          HBI_trans with (1 := HBI_mult_comm _ _),
          HBI_id.
  Qed.

  Fact HBI_unit_mult_1_r A : H⊦ A∗1⇒A.
  Proof. apply HBI_trans with (1 := HBI_mult_comm _ _), HBI_unit_mult_1_l. Qed.

  Fact HBI_unit_mult_2_r A : H⊦ A⇒A∗1.
  Proof. apply HBI_trans with (2 := HBI_mult_comm _ _), HBI_unit_mult_2_l. Qed.

  Fact HBI_wand_adj A B : H⊦ (A∗(A-∗B))⇒B.
  Proof. apply HBI_trans with (1 := HBI_mult_comm _ _), HBI_wand_adj_1, HBI_id. Qed.

  Fact HBI_mult_disj_l A B C : H⊦ (B⩒C)∗A⇒(B∗A)⩒(C∗A).
  Proof. apply HBI_wand_adj_1, HBI_disj_lub; apply HBI_wand_adj_2; constructor 1; auto. Qed.

  Fact HBI_mult_disj_r A B C : H⊦ A∗(B⩒C)⇒(A∗B)⩒(A∗C).
  Proof. 
    apply HBI_trans with (1 := HBI_mult_comm _ _),
          HBI_trans with (1 := HBI_mult_disj_l _ _ _),
          HBI_disj_lub;
    apply HBI_trans with (1 := HBI_mult_comm _ _); constructor 1; auto.
  Qed.

  Fact HBI_bot_mult_l A : H⊦ ⊥∗A⇒⊥.
  Proof. apply HBI_wand_adj_1, HBI_bot_elim. Qed.

  Fact HBI_bot_mult_r A : H⊦ A∗⊥⇒⊥.
  Proof.
    apply HBI_trans with (1 := HBI_mult_comm _ _).
    apply HBI_bot_mult_l.
  Qed.

  Reserved Notation "⟪ Σ ⟫" (at level 0, format "⟪ Σ ⟫").

  Fixpoint BI_bunch_form (Σ : BI_bunch µ prop) : BI_form µ prop :=
    match Σ with
    | ⟨A⟩    => A
    | øₐ     => ⊤
    | øₘ     => 1
    | Γ ⊛ₐ Δ => ⟪Γ⟫⩑⟪Δ⟫
    | Γ ⊛ₘ Δ => ⟪Γ⟫∗⟪Δ⟫
    end
  where "⟪ Σ ⟫" := (BI_bunch_form Σ).

  Hint Resolve HBI_id HBI_mult_mono HBI_conj_mono : core.

  Fact HBI_ctx_bunch_form Δ Γ : H⊦ ⟪Δ[Γ]⟫⇒⟪Δ[⟨⟪Γ⟫⟩]⟫.
  Proof. induction Δ as [ | [] [] ]; simpl; auto. Qed.

  Fact HBI_ctx_bunch_form_rev Δ Γ : H⊦ ⟪Δ[⟨⟪Γ⟫⟩]⟫⇒⟪Δ[Γ]⟫.
  Proof. induction Δ as [ | [] [] ]; simpl; auto. Qed.
 
  Fact HBI_ctx_form_mono Δ A B : H⊦ A⇒B → H⊦ ⟪Δ[⟨A⟩]⟫⇒⟪Δ[⟨B⟩]⟫.
  Proof. intro; induction Δ as [ | [] [] ]; simpl; auto. Qed.

  Fact HBI_ctx_bunch_mono Σ Γ Δ : H⊦ ⟪Γ⟫⇒⟪Δ⟫ → H⊦ ⟪Σ[Γ]⟫⇒⟪Σ[Δ]⟫.
  Proof. intro; induction Σ as [ | [] [] ]; simpl; auto. Qed.

  Section HBI_ctx_equiv. 

    Hint Resolve HBI_unit_mult_1_l HBI_unit_mult_2_l
                 HBI_top_conj_1_l HBI_top_conj_2_l 
                 HBI_mult_comm HBI_conj_comm 
                 HBI_mult_assoc_1 HBI_mult_assoc_2
                 HBI_conj_assoc_1 HBI_conj_assoc_2 : core.

    Fact HBI_ctx_equiv Γ Δ : Γ ≡ Δ → H⊦ ⟪Δ⟫⇒⟪Γ⟫.
    Proof.
      intros H; cut (H⊦ ⟪Γ⟫⇒⟪Δ⟫ ∧ H⊦ ⟪Δ⟫⇒⟪Γ⟫); try tauto.
      induction H as [ | ? ? _ [] | ? ? ? _ [] _ [] | [] | [] | [] | [] ? Δ ? _ [] ];
        simpl; auto.
      split; now apply HBI_trans with (BI_bunch_form Δ).
    Qed.
 
  End HBI_ctx_equiv.

  Fact HBI_ctx_disj Δ A B : H⊦ BI_bunch_form Δ[⟨A⩒B⟩] ⇒ BI_bunch_form Δ[⟨A⟩]⩒BI_bunch_form Δ[⟨B⟩].
  Proof.
    induction Δ as [ | [] [] ]; simpl; auto.
    + apply HBI_trans with (2 := HBI_mult_disj_r _ _ _); auto.
    + apply HBI_trans with (2 := HBI_conj_disj_r _ _ _); auto.
    + apply HBI_trans with (2 := HBI_mult_disj_l _ _ _); auto.
    + apply HBI_trans with (2 := HBI_conj_disj_l _ _ _); auto.
  Qed.

  Section LBI_to_HBI.

    Hint Resolve HBI_ctx_form_mono HBI_ctx_bunch_mono HBI_ctx_equiv
                 HBI_weak_l HBI_top_intro
                 HBI_conj_idem
                 HBI_wand_adj HBI_imp_adj
                 HBI_wand_adj_2 HBI_imp_adj_2
                 HBI_disj_lub
                 HBI_bot_elim 
                 HBI_disj_intro_l HBI_disj_intro_r : core.

    Theorem LBI_full_to_HBI Γ A : Γ L⊦wc A → H⊦ BI_bunch_form Γ⇒A.
    Proof.
      induction 1 as [ 
                     | ? Γ Δ A B _ IH1 _ IH2 
                     | Γ Δ A H _ IH
                     | Γ Δ A _ IH
                     | Γ Δ A _ IH
                     | [] hk Γ A _ IH
                     | [] hk
                     | [] hk Γ A B C _ IH
                     | [] hk Γ Δ A B _ IH1 _ IH2
                     | [] hk Γ Δ A B C _ IH1 _ IH2
                     | [] hk Γ A B _ IH
                     |
                     | Γ Δ A B C _ IH1 _ IH2
                     | ? Γ A B _ IH
                     | ? Γ A B _ IH
                     ];
        try match goal with
        | h : true = true |- _ => rewrite (eq_bool_pirr' h) in *; clear h
        end; auto.
      13: apply HBI_trans with (1 := HBI_ctx_disj _ _ _); auto.
      all: simpl in *; repeat match goal with
           | h : H⊦ ?x⇒_ |- H⊦ ?x⇒_ => apply HBI_trans with (1 := h)
           | h : H⊦ _⇒?x |- H⊦ _⇒?x => apply HBI_trans with (2 := h)
           end; simpl; auto.
      1,2: apply HBI_ctx_bunch_mono; simpl.
      + apply HBI_trans with (2 := HBI_wand_adj A _); auto.
      + apply HBI_trans with (2 := HBI_imp_adj A _); auto.
      + eapply HBI_trans; eauto.
      + eapply HBI_trans; eauto.
    Qed.

  End LBI_to_HBI.

  Corollary LBI_full_to_HBI_form A : øₐ L⊦wc A → H⊦ A.
  Proof. intros H%LBI_full_to_HBI; apply HBI_MP with (2 := H), HBI_top_intro. Qed.

  Arguments BI_ctx_hole { _ _ }.

  Section HBI_to_LBI_wc.
  
    Hint Constructors LBI_provable : core.
    
    Notation "A '-⊙[' h ']' B" := (@BI_form_impl _ _ h eq_refl A B) (at level 62, right associativity, format "A -⊙[ h ] B").

    Fact LBI_wc_impl_left k A B : ⟨A⟩ ⊛[k] ⟨A-⊙[k]B⟩ L⊦wc B.
    Proof. apply BI_sp_impl_l with (Γ := BI_ctx_hole); simpl; auto. Qed.

    Hint Resolve LBI_wc_impl_left : core.

    Fact LBI_wc_impl_inv k Γ A B : Γ L⊦wc A-⊙[k]B → ⟨A⟩ ⊛[k] Γ L⊦wc B.
    Proof.
      intros H.
      apply BI_sp_cut with (Δ := BI_ctx_comp BI_left k _ BI_ctx_hole) (2 := H); simpl; auto.
    Qed.

    Fact LBI_wc_impl_inv' k A B : ø[k] L⊦wc A-⊙[k]B → ⟨A⟩ L⊦wc B.
    Proof.
      intros H%LBI_wc_impl_inv.
      revert H; apply BI_sp_equiv.
      apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_neut.
    Qed.

    Fact LBI_wc_neut_l k Γ A : Γ L⊦wc A → ø[k] ⊛[k] Γ L⊦wc A.
    Proof. apply BI_sp_equiv, BI_bequiv_sym, BI_bequiv_neut. Qed.

    Fact LBI_wc_neut_r k Γ A : Γ L⊦wc A → Γ ⊛[k] ø[k] L⊦wc A.
    Proof. apply BI_sp_equiv, BI_bequiv_sym, BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_neut. Qed.

    Hint Resolve LBI_wc_neut_l LBI_wc_neut_r : core.

    Theorem HBI_to_LBI_full A : H⊦ A → øₐ L⊦wc A.
    Proof.
      induction 1 as [ A [ H | H ] 
                     | A B _ IH1 _ IH2 
                     | A B C D _ IH1 _ IH2 
                     | A B C _ IH
                     | A B C _ IH
                     ].
      + destruct H as [ A B | A B C | A B | A B | A B | A B | A B | A B C | A | ]; eauto.
        * apply BI_sp_impl_r, LBI_wc_neut_l.
          apply BI_sp_impl_r, BI_sp_weak with (Γ := BI_ctx_comp BI_left _ _ BI_ctx_hole); simpl; auto.
        * apply BI_sp_impl_r, BI_sp_equiv with (1 := BI_bequiv_sym (BI_bequiv_neut _ _)).
          do 2 apply BI_sp_impl_r.
          apply BI_sp_cntr with (Γ := BI_ctx_comp BI_left _ _ BI_ctx_hole); simpl.
          apply BI_sp_equiv with ((⟨A⟩ ⊛ₐ ⟨A⇒B⟩) ⊛ₐ (⟨A⟩ ⊛ₐ ⟨A⇒B⇒C⟩)).
          - apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _).
            apply BI_bequiv_trans with (1 := BI_bequiv_assoc _ _ _ _).
            apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _).
            apply BI_bequiv_trans with (1 := BI_bequiv_assoc _ _ _ _).
            apply BI_bequiv_trans with (2 := BI_bequiv_sym (BI_bequiv_assoc _ _ _ _)).
            apply BI_bequiv_congr.
            apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _).
            apply BI_bequiv_trans with (1 := BI_bequiv_sym (BI_bequiv_assoc _ _ _ _)).
            apply BI_bequiv_comm.
          - apply BI_sp_impl_l with (Γ := BI_ctx_comp BI_right _ _ BI_ctx_hole); auto; simpl.
            apply BI_sp_impl_l with (Γ := BI_ctx_comp BI_left _ _ BI_ctx_hole); auto; simpl.
            apply BI_sp_impl_l with (Γ := BI_ctx_hole); simpl; auto.
        * apply BI_sp_impl_r, LBI_wc_neut_l.
          apply BI_sp_conj_l with (Γ := BI_ctx_hole); simpl.
          apply BI_sp_weak with (Γ := BI_ctx_comp BI_left _ _ BI_ctx_hole); simpl; auto.
        * apply BI_sp_impl_r, LBI_wc_neut_l.
          apply BI_sp_conj_l with (Γ := BI_ctx_hole); simpl.
          apply BI_sp_weak with (Γ := BI_ctx_comp BI_right _ _ BI_ctx_hole); simpl; auto.
        * apply BI_sp_impl_r, LBI_wc_neut_l, BI_sp_impl_r, BI_sp_impl_r.
          apply BI_sp_disj_l with (Γ := BI_ctx_comp BI_left _ _ BI_ctx_hole); simpl.
          - apply BI_sp_weak with (Γ := BI_ctx_comp BI_right _ _ (BI_ctx_comp BI_left _ _ BI_ctx_hole)); simpl.
            apply BI_sp_equiv with (⟨A⟩ ⊛ₐ ⟨A⇒C⟩); auto.
            apply BI_bequiv_trans with (2 := BI_bequiv_comm _ _ _), BI_bequiv_congr.
            apply BI_bequiv_trans with (2 := BI_bequiv_comm _ _ _), BI_bequiv_sym, BI_bequiv_neut.
          - apply BI_sp_equiv with (1 := BI_bequiv_sym (BI_bequiv_assoc _ _ _ _)).
            apply BI_sp_weak with (Γ := BI_ctx_comp BI_right _ _ BI_ctx_hole); simpl.
            apply LBI_wc_neut_l.
            apply BI_sp_equiv with (1 := BI_bequiv_comm _ _ _); auto.
      + destruct H as [ A | A | A B | A B C ].
        * apply BI_sp_impl_r, LBI_wc_neut_l.
          apply BI_sp_equiv with (1 := BI_bequiv_neut BI_mult _); auto. 
        * apply BI_sp_impl_r, LBI_wc_neut_l.
          apply BI_sp_conj_l with (Γ := BI_ctx_hole); simpl; auto.
          apply BI_sp_unit_l with (Γ := BI_ctx_comp BI_right _ _ BI_ctx_hole); simpl; auto.
        * apply BI_sp_impl_r, LBI_wc_neut_l.
          apply BI_sp_conj_l with (Γ := BI_ctx_hole); simpl; auto.
          apply BI_sp_equiv with (1 := BI_bequiv_comm _ _ _); auto.
        * apply BI_sp_impl_r, LBI_wc_neut_l.
          apply BI_sp_conj_l with (Γ := BI_ctx_hole); simpl; auto.
          apply BI_sp_conj_l with (Γ := BI_ctx_comp BI_left _ _ BI_ctx_hole); simpl; auto.
          apply BI_sp_equiv with (1 := BI_bequiv_assoc _ _ _ _); auto.
      + apply LBI_wc_impl_inv' in IH2.
        apply BI_sp_cut with (Δ := BI_ctx_hole) (2 := IH1); simpl; auto.
      + apply LBI_wc_impl_inv' in IH1, IH2.
        apply BI_sp_impl_r, BI_sp_equiv with (1 := BI_bequiv_sym (BI_bequiv_neut _ _)).
        now apply BI_sp_conj_l with (Γ := BI_ctx_hole), BI_sp_conj_r.
      + apply LBI_wc_impl_inv', LBI_wc_impl_inv in IH.
        apply BI_sp_impl_r, BI_sp_equiv with (1 := BI_bequiv_sym (BI_bequiv_neut _ _)).
        now apply BI_sp_conj_l with (Γ := BI_ctx_hole), BI_sp_equiv with (1 := BI_bequiv_comm _ _ _).
      + apply LBI_wc_impl_inv' in IH.
        apply BI_sp_impl_r, BI_sp_equiv with (1 := BI_bequiv_sym (BI_bequiv_neut _ _)).
        apply BI_sp_impl_r.
        apply BI_sp_cut with (Δ := BI_ctx_hole) (3 := IH); simpl; auto.
    Qed.

  End HBI_to_LBI_wc.

  Hint Resolve LBI_full_to_HBI_form HBI_to_LBI_full : core.

  Corollary LBI_wc_equiv_HBI A :  øₐ L⊦wc A ↔ H⊦ A.
  Proof. split; auto. Qed.

End LBI_full_HBI.

Theorem LBI_to_HBI_form prop µ c (A : BI_form µ prop) : øₐ L⊦[c] A → H⊦ BI_form_map (λ _, true) (λ _ _, eq_refl) (λ p, p) A.
Proof. now intros H%(LBI_map_sound (λ _, true) (λ _ _, eq_refl) (λ p, p) (λ _, eq_refl))%LBI_full_to_HBI_form. Qed.

Check LBI_to_HBI_form.
