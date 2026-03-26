(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Arith Lia List Utf8 Permutation.

From Undecidability.MinskyMachines
  Require Import ACM2 acm2_utils.

From Undecidability.BI
  Require Import BI.

Import BI_notations ListNotations ACM2_Notations.

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

  Fact BI_simpl_unit_l Γ γ : Γ ⊛ₘ øₘ ⊦ γ → Γ ⊦ γ.
  Proof.
    apply BI_spcf_equiv.
    apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_neut.
  Qed.

  Fact BI_simpl_imp_l Γ A B C : Γ ⊦ A → ⟨B⟩ ⊦ C → Γ ⊛ₐ ⟨A⇒B⟩ ⊦ C.
  Proof. apply BI_spcf_imp_l with (Γ := BI_ctx_hole). Qed.

  Fact BI_simpl_wand_l Γ A B C : Γ ⊦ A → ⟨B⟩ ⊦ C → Γ ⊛ₘ ⟨A-∗B⟩ ⊦ C.
  Proof. apply BI_spcf_wand_l with (Γ := BI_ctx_hole). Qed.

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

  Fact BI_list_mult_app Σ Δ : BI_list_mult (Σ++Δ) ≡ (BI_list_mult Σ) ⊛ₘ (BI_list_mult Δ).
  Proof. induction Σ; simpl; eauto. Qed.

  Fact BI_list_mult_snoc Σ A : (BI_list_mult Σ) ⊛ₘ ⟨A⟩ ≡ BI_list_mult (A::Σ).
  Proof. simpl; apply BI_bequiv_comm. Qed.

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
    apply BI_simpl_imp_l.
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

  Fact BI_FORK Γ φ ψ γ : Γ ⊦ φ → Γ ⊦ ψ → Γ ⊛ₘ ⟨(φ⩑ψ)-∗γ⟩ ⊦ γ.
  Proof.
    intros H1 H2.
    apply BI_simpl_wand_l.
    + now apply BI_cntr_all, BI_spcf_conj_r.
    + apply BI_spcf_axiom.
  Qed.

  Fact BI_INC Γ φ ψ γ : Γ ⊛ₘ ⟨φ⟩ ⊦ ψ → Γ ⊛ₘ ⟨(φ-∗ψ)-∗γ⟩ ⊦ γ.
  Proof.
    intros H.
    apply BI_simpl_wand_l.
    + now apply BI_spcf_wand_r.
    + apply BI_spcf_axiom.
  Qed.

  Fact BI_DEC Γ φ ψ γ : Γ ⊦ ψ → Γ ⊛ₘ ⟨φ⟩ ⊛ₘ ⟨φ-∗ψ-∗γ⟩ ⊦ γ.
  Proof.
    intros H.
    apply BI_spcf_equiv with (1 := BI_bequiv_sym (BI_bequiv_assoc _ _ _ _)).
    set (Δ := BI_ctx_comp true BI_mult Γ BI_ctx_hole).
    change (Δ[⟨φ⟩ ⊛ₘ ⟨φ-∗ψ-∗γ⟩] ⊦ γ).
    apply BI_spcf_wand_l with (1 := BI_spcf_axiom _).
    simpl.
    apply BI_simpl_wand_l; auto.
    apply BI_spcf_axiom.
  Qed.

  Fact BI_STOP Γ γ : Γ ⊦ 1 → Γ ⊛ₘ ⟨1-∗γ⟩ ⊦ γ.
  Proof.
    intros.
    apply BI_simpl_wand_l; auto.
    apply BI_spcf_axiom.
  Qed.

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

  Theorem tps_BI_pseudo_exp γ φ : ⟦φ⟧ e → ∀x, ⟦BI_pseudo_exp γ φ⟧ x ↔ e = x.
  Proof using comm neut.
    intros Hφ x; split.
    1: intros []; auto.
    intros <-.
    split; [ | reflexivity ].
    intros x _ H.
    rewrite comm, neut in H.
    rewrite comm; apply H; auto.
  Qed. 

End TPS.

Section ACM2_to_BI.

  Variables (loc : Set).

  Implicit Type (i : acm2_instr loc).

  Definition acm2_instr_src i :=
    match i with
    | STOPₐ p     => p
    | INCₐ b p q  => p
    | DECₐ b p q  => p
    | FORKₐ p q r => p
    end.

  Variables (Σ : list (@acm2_instr loc))
            (l : list loc)
            (HΣl : ∀i, i ∊ Σ → acm2_instr_src i ∊ l).

  (** Encode 
        FORKₐ p q r --> q⩑r -∗ p
        INCₐ b p q  --> (b -∗ q) -∗ p
        DECₐ b p q  --> b -∗ q -∗ p
        STOPₐ p     --> 1 -∗ p 
   *)

  Definition acm2_instr_to_BI i :=
    match i with
    | STOPₐ p     => 1 -∗ £(inl p)
    | INCₐ b p q  => (£(inr b) -∗ £(inl q)) -∗ £(inl p)
    | DECₐ b p q  => £(inr b) -∗ £(inl q) -∗ £(inl p)
    | FORKₐ p q r => (£(inl q) ⩑ £(inl r)) -∗ £(inl p)
    end.

  Notation α := true.
  Notation β := false.

  Definition acm2_ctx_to_BI x y := 
       repeat £(inr α) x ++ repeat £(inr β) y 
    ++ flat_map (fun p => map (fun i => BI_pseudo_exp £(inl p) (acm2_instr_to_BI i)) Σ) l.

  Fact In_acm2_ctx_to_BI x y i p :
        i ∊ Σ 
     -> p = acm2_instr_src i
     -> BI_pseudo_exp £(inl p) (acm2_instr_to_BI i) ∊ acm2_ctx_to_BI x y.
  Proof using HΣl.
    intros H1 H2.
    unfold acm2_ctx_to_BI; rewrite !in_app_iff, in_flat_map; do 2 right.
    exists p; split; subst; auto.
    apply in_map_iff; eauto.
  Qed.

  Fact acm2_ctx_to_BI_x x y Δ : 
      BI_list_mult (acm2_ctx_to_BI (1+x) y) ⊛ₘ Δ 
    ≡ BI_list_mult (acm2_ctx_to_BI x y) ⊛ₘ ⟨£(inr α)⟩ ⊛ₘ Δ.
  Proof. 
    do 2 apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_sym.
    apply BI_bequiv_congr, BI_bequiv_comm.
  Qed.

  Fact acm2_ctx_to_BI_y x y Δ : 
      BI_list_mult (acm2_ctx_to_BI x (1+y)) ⊛ₘ Δ 
    ≡ BI_list_mult (acm2_ctx_to_BI x y) ⊛ₘ ⟨£(inr β)⟩ ⊛ₘ Δ.
  Proof. 
    do 2 apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_sym.
    apply BI_bequiv_congr.
    apply BI_bequiv_sym, 
          BI_bequiv_trans with (1 := BI_list_mult_snoc _ _),
          BI_list_mult_perm_bequiv.
    unfold acm2_ctx_to_BI.
    apply perm_trans with (2 := Permutation_app_swap_app _ _ _).
    simpl; apply perm_skip, Permutation_app_swap_app.
  Qed.

  Hint Resolve In_acm2_ctx_to_BI : core.

  Lemma acm2_encode_sound x y p :
      acm2_accept Σ x y p
    → BI_list_mult (acm2_ctx_to_BI x y) ⊦ £(inl p).
  Proof using HΣl.
    induction 1 as [ p H 
                   | x y p q r H _ IH1 _ IH2
                   | x y p q H _ IH
                   | x y p q H _ IH
                   | 
                   | 
                   ];
        match goal with
        | _ : ?i ∊ Σ |- _ => apply BI_list_mult_derilection with (φ := acm2_instr_to_BI i)
        end; auto; simpl acm2_instr_to_BI.
    + apply BI_STOP.
      unfold acm2_ctx_to_BI; simpl.
      apply BI_simpl_unit_l, BI_list_mult_weak.
      2: apply BI_spcf_unit_r.
      intros A; rewrite in_flat_map.
      intros (k & ? & (i & <- & ?)%in_map_iff); eauto.
    + apply BI_FORK; auto.
    + apply BI_INC.
      revert IH; apply BI_spcf_equiv.
      apply BI_bequiv_sym, 
            BI_bequiv_trans with (1 := BI_list_mult_snoc _ _),
            BI_list_mult_perm_bequiv; auto.
    + apply BI_INC.
      revert IH; apply BI_spcf_equiv.
      apply BI_bequiv_sym, 
            BI_bequiv_trans with (1 := BI_list_mult_snoc _ _),
            BI_list_mult_perm_bequiv.
      unfold acm2_ctx_to_BI.
      apply perm_trans with (2 := Permutation_app_swap_app _ _ _).
      simpl; apply perm_skip, Permutation_app_swap_app.
    + apply BI_spcf_equiv with (1 := BI_bequiv_sym (acm2_ctx_to_BI_x _ _ _)).
      now apply BI_DEC.
    + apply BI_spcf_equiv with (1 := BI_bequiv_sym (acm2_ctx_to_BI_y _ _ _)).
      now apply BI_DEC.
  Qed.

  Section completeness.

    Let s (v : loc + bool) :=
      match v with
      | inl p => fun '(x,y) => acm2_accept Σ x y p
      | inr α => eq (1,0)%nat 
      | inr β => eq (0,1)%nat
      end.

    Notation sem := (tps_BI_form pair_add (0,0) s).

    Hint Constructors acm2_accept : core.

    Local Lemma sem_complete_instr i : In i Σ -> sem (acm2_instr_to_BI i) (0, 0).
    Proof.
      intros Hi.
      destruct i as [ | [] p q | [] p q | ]; simpl.
      + intros ? <-; simpl; eauto.
      + intros [] ?; rewrite pair_add_zero_right.
        constructor 3 with q; auto; apply (H _ eq_refl).
      + intros [] ?; rewrite pair_add_zero_right.
        constructor 4 with q; auto; apply (H _ eq_refl).
      + intros ? <-; simpl.
        intros []; rewrite pair_add_comm; simpl.
        now constructor 5 with q.
      + intros ? <-; simpl.
        intros []; rewrite pair_add_comm; simpl.
        now constructor 6 with q.
      + intros [] []; rewrite pair_add_zero_right; eauto.
    Qed.

    Variables (x y : nat) (p : loc)
              (H : BI_list_mult (acm2_ctx_to_BI x y) ⊦ £(inl p)).

    Hint Resolve pair_add_zero_left pair_add_comm pair_add_assoc : core.

    Lemma acm2_encode_complete : acm2_accept Σ x y p.
    Proof using H.
      apply tps_BI_sound with (plus := pair_add) (e := (0,0)) (s := s) (m := (x,y)) in H; auto.
      apply tps_BI_equiv with (BI_list_mult (repeat £(inr α) x)
                            ⊛ₘ (BI_list_mult (repeat £(inr β) y) 
                            ⊛ₘ BI_list_mult (flat_map (fun p => map (fun i => BI_pseudo_exp £(inl p) (acm2_instr_to_BI i)) Σ) l)));
        auto.
      + unfold acm2_ctx_to_BI.
        do 2 apply BI_bequiv_trans with (1 := BI_list_mult_app _ _), BI_bequiv_congr.
        apply BI_bequiv_refl.
      + exists (x,0), (0,y); split; simpl; auto; split.
        * clear H.
          induction x as [ | n IHn ]; simpl; auto.
          exists (1,0)%nat, (n,0); auto.
        * exists (0,y), (0,0); split; simpl; auto; split.
          - clear H.
            induction y as [ | n IHn ]; simpl; auto.
            exists (0,1)%nat, (0,n); auto.
          - apply tps_BI_bunch_list_mult; auto.
            intros A; rewrite in_flat_map.
            intros (k & ? & (i & <- & ?)%in_map_iff).
            apply tps_BI_pseudo_exp; auto.
            now apply sem_complete_instr.
    Qed.

  End completeness.

End ACM2_to_BI.

#[local] Hint Resolve acm2_encode_sound acm2_encode_complete in_map : core.

(** This establishes the correctness of the reduction ACM2 -> BI *)
Theorem acm2_to_BI_correctness (loc : Set) Σ x y (p : loc) :
  acm2_accept Σ x y p ↔ BI_list_mult (acm2_ctx_to_BI Σ (map (@acm2_instr_src _) Σ) x y) ⊦ £(inl p).
Proof. split; eauto. Qed.

Check acm2_to_BI_correctness.

Section BI_map.

  Variables (prop prop' : Set)
            (φ : prop → prop').

  Fixpoint BI_form_map (A : BI_form prop) :=
    match A with
    | BI_form_var v => BI_form_var (φ v)
    | BI_form_unit _ k => BI_form_unit _ k
    | BI_form_imp k A B => BI_form_imp k (BI_form_map A) (BI_form_map B)
    | BI_form_conj A B => BI_form_conj (BI_form_map A) (BI_form_map B)
    end.

  Fixpoint BI_bunch_map Γ :=
    match Γ with
    | BI_bunch_atom A => BI_bunch_atom (BI_form_map A)
    | BI_bunch_unit _ b => BI_bunch_unit _ b
    | BI_bunch_comp k Γ Δ => BI_bunch_comp k (BI_bunch_map Γ) (BI_bunch_map Δ)
    end.

  Section BI_bunch_equiv.

    Hint Constructors BI_bunch_equiv : core.
 
    Fact BI_bunch_equiv_map Γ Δ : Γ ≡ Δ → BI_bunch_map Γ ≡ BI_bunch_map Δ.
    Proof. induction 1; simpl; eauto. Qed.

  End BI_bunch_equiv.

  Fixpoint BI_ctx_map C :=
    match C with
    | BI_ctx_hole => BI_ctx_hole
    | BI_ctx_comp b k Γ C => BI_ctx_comp b k (BI_bunch_map Γ) (BI_ctx_map C)
    end.

  Fact BI_ctx_bunch_map C Γ : BI_bunch_map (C[Γ]) = (BI_ctx_map C)[BI_bunch_map Γ].
  Proof. induction C as [ | [] ]; simpl; f_equal; auto. Qed.

  Hint Constructors BI_seq_provable_cut_free : core.
  Hint Resolve BI_bunch_equiv_map : core.

  Theorem BI_map_sound Γ A : Γ ⊦ A → BI_bunch_map Γ ⊦ BI_form_map A.
  Proof.
    induction 1; simpl; eauto; rewrite BI_ctx_bunch_map in * |- *; simpl in *; eauto.
  Qed.

End BI_map.

Section BI_embed.

  Variables (prop prop' : Set)
            (φ : prop → prop')
            (ψ : prop' → prop)
            (Hφψ : ∀p, ψ (φ p) = p).

  Fact BI_form_map_embed A : BI_form_map ψ (BI_form_map φ A) = A.
  Proof using Hφψ. induction A; simpl; f_equal; auto. Qed.

  Hint Resolve BI_form_map_embed : core.

  Fact BI_bunch_map_embed Γ : BI_bunch_map ψ (BI_bunch_map φ Γ) = Γ.
  Proof using Hφψ. induction Γ; simpl; f_equal; auto. Qed.

  Theorem BI_embed_correctness Σ A :
    Σ ⊦ A ↔ BI_bunch_map φ Σ ⊦ BI_form_map φ A.
  Proof using Hφψ.
    split.
    + apply BI_map_sound.
    + intros H%(BI_map_sound ψ).
      now rewrite BI_bunch_map_embed, BI_form_map_embed in H.
  Qed.

End BI_embed.



