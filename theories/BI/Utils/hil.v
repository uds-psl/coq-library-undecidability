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
  Require Import BI utils.

Import ListNotations.

Set Implicit Arguments.

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70).
#[local] Infix "∊" := In (at level 70).

#[local] Notation "x ≡ y" := (BI_bunch_equiv x y) (at level 70, no associativity, format "x  ≡  y").
#[local] Notation "C [ Δ ]" := (BI_ctx_fill C Δ) (at level 1, no associativity, format "C [ Δ ]").
#[local] Notation "Γ '⊦[' b ']' A" := (LBI_provable b Γ A) (at level 70, no associativity, format "Γ  ⊦[ b ]  A").

Section IL.

  Variables (prop : Set).

  Notation µ := (λ _ : BI_conn, true).

  Notation "⊥" := (@BI_form_bot _ _ eq_refl).
  Notation "⊤" := (@BI_form_unit _ _ BI_addi eq_refl).
  Notation "A ⇒ B" := (@BI_form_impl _ _ BI_addi eq_refl A B) (at level 63, right associativity, format "A ⇒ B").
  Notation "A ⩑ B" := (@BI_form_conj _ _ BI_addi eq_refl A B) (at level 59, left associativity, format "A ⩑ B").
  Notation "A ⩒ B" := (@BI_form_disj _ _ eq_refl A B) (at level 61, left associativity, format "A ⩒ B").

  Arguments IL_axiom {_}.

  Notation "Φ 'I⊦' A" := (@HIL_deduction prop Φ A) (at level 70).
  Notation "'I⊦' A" := (@HIL_deduction prop IL_axiom A) (at level 70).

  Implicit Type (Φ : BI_form µ prop → Prop).

  Hint Constructors IL_axiom HIL_deduction HBI_deduction : core.

  Theorem HIL_incl_HBI Φ : HIL_deduction Φ ⊆ HBI_deduction Φ.
  Proof. induction 1; eauto. Qed.

  Theorem HIL_mono Φ Φ' : Φ ⊆ Φ' → HIL_deduction Φ ⊆ HIL_deduction Φ'.
  Proof. induction 2; eauto. Qed.

  Section deduction_theorem.

    Variables (Φ : _) (HΦ : @IL_axiom prop ⊆ Φ).

    Theorem HIL_deduction_theorem A B : (λ x, Φ x ∨ A = x) I⊦ B → Φ I⊦ A⇒B.
    Proof using HΦ.
      induction 1 as [ B [] | B C _ IH1 _ IH2 ].
      + constructor 2 with B; eauto.
      + subst.
        constructor 2 with (B⇒B⇒B); eauto.
        constructor 2 with (B⇒(B⇒B)⇒B); eauto.
      + constructor 2 with (1 := IH1).
        constructor 2 with (1 := IH2). 
        constructor 1; eauto.
    Qed.

  End deduction_theorem.

  Fact HIL_imp_intro Φ A B :
    IL_axiom ⊆ Φ → (λ x, Φ x ∨ A = x) I⊦ B → Φ I⊦ A⇒B.
  Proof. intros; apply HIL_deduction_theorem; auto. Qed.

  Fact HIL_imp_elim Φ A B C :
      IL_axiom ⊆ Φ
    → Φ I⊦ A⇒B
    → Φ I⊦ A
    → (λ x, Φ x ∨ B = x) I⊦ C
    → Φ I⊦ C.
  Proof.
    intros HΦ H1 H2 H3.
    constructor 2 with B; auto.
    + constructor 2 with A; eauto.
    + apply HIL_imp_intro; eauto.
  Qed.

  Fact HIL_conj_intro Φ A B :
      IL_axiom ⊆ Φ
    → Φ I⊦ A
    → Φ I⊦ B
    → Φ I⊦ A⩑B.
  Proof.
    intros HΦ H1 H2.
    constructor 2 with B; auto.
    constructor 2 with A; auto.
  Qed.
 
  Fact HIL_conj_elim Φ A B C :
      IL_axiom ⊆ Φ
    → Φ I⊦ A⩑B
    → (λ x, Φ x ∨ A = x ∨ B = x) I⊦ C
    → Φ I⊦ C.
  Proof.
    intros HΦ H1 H2.
    constructor 2 with B.
    1: constructor 2 with (A⩑B); eauto.
    constructor 2 with A.
    1: constructor 2 with (A⩑B); eauto.
    do 2 (apply HIL_imp_intro; eauto).
    revert H2; apply HIL_mono; firstorder.
  Qed.

  Fact HIL_top_intro Φ : IL_axiom ⊆ Φ → Φ I⊦ ⊤.
  Proof. constructor 1; auto. Qed.

  Fact HIL_bot_elim Φ A : IL_axiom ⊆ Φ → Φ I⊦ ⊥ → Φ I⊦ A.
  Proof. intros; constructor 2 with ⊥; eauto. Qed.

  Fact HIL_disj_intro_l Φ A B :
    IL_axiom ⊆ Φ → Φ I⊦ A → Φ I⊦ A⩒B.
  Proof. constructor 2 with A; eauto. Qed.

  Fact HIL_disj_intro_r Φ A B :
    IL_axiom ⊆ Φ → Φ I⊦ B → Φ I⊦ A⩒B.
  Proof. constructor 2 with B; eauto. Qed.

  Fact HIL_disj_elim Φ A B C :
      IL_axiom ⊆ Φ
    → Φ I⊦ A⩒B
    → (λ x, Φ x ∨ A = x) I⊦ C
    → (λ x, Φ x ∨ B = x) I⊦ C
    → Φ I⊦ C.
  Proof.
    intros.
    constructor 2 with (A⩒B); auto.
    constructor 2 with (B⇒C); auto.
    1: apply HIL_imp_intro; auto.
    constructor 2 with (A⇒C); auto.
    1: apply HIL_imp_intro; auto.
  Qed.

  (** We can now reason using natural deduction in HIL 
      which is enough for any theorem of IL !! *)

  Fact HIL_K A B : I⊦ A⇒B⇒A.
  Proof. do 2 (apply HIL_imp_intro; eauto). Qed.

  Fact HIL_S A B C : I⊦ (A⇒B⇒C)⇒(A⇒B)⇒A⇒C.
  Proof. 
    do 3 (apply HIL_imp_intro; eauto).
    apply HIL_imp_elim with A (B⇒C); eauto.
    apply HIL_imp_elim with B C; eauto.
    apply HIL_imp_elim with A B; eauto.
  Qed.

  Fact HIL_id A : I⊦ A⇒A.
  Proof. apply HIL_imp_intro; eauto. Qed.

  Fact HIL_weak_r A B C : I⊦ (A⇒C)⇒A⇒B⇒C.
  Proof.
    do 3 (apply HIL_imp_intro; eauto).
    apply HIL_imp_elim with A C; auto.
  Qed.

  Fact HIL_conj_mono A B C D : I⊦ (A⇒C)⇒(B⇒D)⇒(A⩑B⇒C⩑D).
  Proof.
    do 3 (apply HIL_imp_intro; eauto).
    apply HIL_conj_intro; eauto.
    + apply HIL_conj_elim with A B; eauto.
      apply HIL_imp_elim with A C; eauto.
      constructor 1; firstorder.
    + apply HIL_conj_elim with A B; eauto.
      apply HIL_imp_elim with B D; eauto.
  Qed.

  Fact HIL_conj_assoc_1 A B C : I⊦ A⩑(B⩑C)⇒(A⩑B)⩑C.
  Proof.
    apply HIL_imp_intro; auto.
    apply HIL_conj_elim with A (B⩑C); eauto.
    apply HIL_conj_elim with B C; eauto.
    do 2 (apply HIL_conj_intro; auto).
  Qed.

  Fact HIL_conj_assoc_2 A B C : I⊦ (A⩑B)⩑C⇒A⩑(B⩑C).
  Proof.
    apply HIL_imp_intro; auto.
    apply HIL_conj_elim with (A⩑B) C; eauto.
    apply HIL_conj_elim with A B; eauto.
    do 2 (apply HIL_conj_intro; auto).
  Qed.

  Fact HIL_conj_comm A B : I⊦ A⩑B⇒B⩑A.
  Proof.
    apply HIL_imp_intro; auto.
    apply HIL_conj_elim with A B; eauto.
    apply HIL_conj_intro; auto.
  Qed.

  Fact HIL_conj_top A : I⊦ A⇒⊤⩑A.
  Proof.
    apply HIL_imp_intro; auto.
    apply HIL_conj_intro; auto.
  Qed.

  Fact HIL_conj_idem A : I⊦ A⇒A⩑A.
  Proof.
    apply HIL_imp_intro; auto.
    apply HIL_conj_intro; auto.
  Qed.

  Fact HIL_imp_trans A B C : I⊦ (A⇒B)⇒(B⇒C)⇒(A⇒C).
  Proof.
    do 3 (apply HIL_imp_intro; eauto).
    apply HIL_imp_elim with B C; eauto.
    apply HIL_imp_elim with A B; eauto.
  Qed.

  Fact HIL_imp_adj_1 A B C : I⊦ (A⇒B⇒C)⇒(A⩑B⇒C).
  Proof.
    do 2 (apply HIL_imp_intro; eauto).
    apply HIL_conj_elim with A B; eauto.
    apply HIL_imp_elim with A (B⇒C); eauto.
    apply HIL_imp_elim with B C; eauto; firstorder.
  Qed.

  Fact HIL_imp_adj_2 A B C : I⊦ (A⩑B⇒C)⇒(A⇒B⇒C).
  Proof.
    do 3 (apply HIL_imp_intro; eauto).
    apply HIL_imp_elim with (A⩑B) C; eauto.
    apply HIL_conj_intro; eauto.
  Qed.

  Fact HIL_imp_adj A B : I⊦ (A⩑(A⇒B))⇒B.
  Proof.
    apply HIL_imp_intro; eauto.
    apply HIL_conj_elim with A (A⇒B); eauto.
    apply HIL_imp_elim with A B; eauto.
  Qed.

  Fact HIL_imp_anti_mono A B C D : I⊦ (A⇒B)⇒(C⇒D)⇒(B⇒C)⇒(A⇒D).
  Proof.
    do 4 (apply HIL_imp_intro; eauto).
    apply HIL_imp_elim with C D; eauto.
    apply HIL_imp_elim with B C; eauto.
    apply HIL_imp_elim with A B; eauto.
    constructor 1; firstorder.
  Qed.

  Fact HIL_bot_conj_l A : I⊦ ⊥⩑A⇒⊥.
  Proof.
    apply HIL_imp_intro; auto.
    apply HIL_conj_elim with ⊥ A; auto.
  Qed.

  Fact HIL_bot_conj_r A : I⊦ A⩑⊥⇒⊥.
  Proof.
    apply HIL_imp_intro; auto.
    apply HIL_conj_elim with A ⊥; auto.
  Qed.

  Fact HIL_top_r : I⊦ ⊤.
  Proof. apply HIL_top_intro; auto. Qed.

  Fact HIL_bot_l A : I⊦ ⊥⇒A.
  Proof. apply HIL_imp_intro, HIL_bot_elim; auto. Qed.

  Fact HIL_disj_l A B : I⊦ A⇒A⩒B.
  Proof.
    apply HIL_imp_intro; auto.
    apply HIL_disj_intro_l; auto. 
  Qed.

  Fact HIL_disj_r A B : I⊦ B⇒A⩒B.
  Proof. 
    apply HIL_imp_intro; auto.
    apply HIL_disj_intro_r; auto. 
  Qed.

  Fact HIL_disj_lub A B C : I⊦ (A⇒C)⇒(B⇒C)⇒(A⩒B⇒C).
  Proof.
    do 3 (apply HIL_imp_intro; auto).
    apply HIL_disj_elim with A B; auto.
    + apply HIL_imp_elim with A C; eauto; firstorder.
      constructor 1; firstorder.
    + apply HIL_imp_elim with B C; eauto; firstorder.
  Qed.

  Fact HIL_conj_disj_l A B C : I⊦ (B⩒C)⩑A⇒(B⩑A)⩒(C⩑A).
  Proof.
    do 1 (apply HIL_imp_intro; auto).
    apply HIL_conj_elim with (B⩒C) A; auto.
    apply HIL_disj_elim with B C; auto.
    + apply HIL_disj_intro_l; auto.
      apply HIL_conj_intro; auto.
    + apply HIL_disj_intro_r; auto.
      apply HIL_conj_intro; auto.
  Qed.

  Fact HIL_conj_disj_r A B C : I⊦ A⩑(B⩒C)⇒(A⩑B)⩒(A⩑C).
  Proof.
    do 1 (apply HIL_imp_intro; auto).
    apply HIL_conj_elim with A (B⩒C); auto.
    apply HIL_disj_elim with B C; auto.
    + apply HIL_disj_intro_l; auto.
      apply HIL_conj_intro; auto.
    + apply HIL_disj_intro_r; auto.
      apply HIL_conj_intro; auto.
  Qed.

End IL.
