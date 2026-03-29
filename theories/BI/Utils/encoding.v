(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Utf8 .

From Undecidability.MinskyMachines
  Require Import ACM2 acm2_utils.

From Undecidability.BI
  Require Import BI utils tps.

Import ListNotations ACM2_Notations.

Set Implicit Arguments.

#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70).
#[local] Infix "∊" := In (at level 70).
#[local] Infix "~p" := (@Permutation _) (at level 70).

#[local] Notation "x ≡ y" := (BI_bunch_equiv x y) (at level 70, no associativity, format "x  ≡  y").
#[local] Notation "C [ Δ ]" := (BI_ctx_fill C Δ) (at level 1, no associativity, format "C [ Δ ]").

#[local] Notation "⟨ A ⟩" := (BI_bunch_atom A) (at level 0, format "⟨ A ⟩"). 
#[local] Notation "'ø[' k ']'" := (BI_bunch_unit _ _ k) (at level 0, no associativity, format "ø[ k ]").
#[local] Notation "Γ '⊛[' k ']' Δ" := (BI_bunch_comp k Γ Δ) (at level 65, left associativity, format "Γ  ⊛[ k ]  Δ").
#[local] Notation øₐ := ø[BI_addi].
#[local] Notation øₘ := ø[BI_mult].
#[local] Notation "Γ '⊛ₐ' Δ" := (Γ ⊛[BI_addi] Δ) (at level 65, left associativity, format "Γ  ⊛ₐ  Δ").
#[local] Notation "Γ '⊛ₘ' Δ" := (Γ ⊛[BI_mult] Δ) (at level 65, left associativity, format "Γ  ⊛ₘ  Δ").

#[local] Notation "£ v" := (@BI_form_var _ _ v) (at level 1, format "£ v").
#[local] Notation "⊥" := (@BI_form_bot _ _ eq_refl).
#[local] Notation "1" := (@BI_form_unit _ _ BI_mult eq_refl).
#[local] Notation "A ⇒ B" := (@BI_form_impl _ _ BI_addi eq_refl A B) (at level 63, right associativity, format "A ⇒ B").
#[local] Notation "A '-∗' B" := (@BI_form_impl _ _ BI_mult eq_refl A B) (at level 63, right associativity, format "A -∗ B").
#[local] Notation "A ∗ B" := (@BI_form_conj _ _ BI_mult eq_refl A B) (at level 59, left associativity, format "A ∗ B").
#[local] Notation "A ⩑ B" := (@BI_form_conj _ _ BI_addi eq_refl A B) (at level 59, left associativity, format "A ⩑ B").
#[local] Notation "A ⩒ B" := (@BI_form_disj _ _ eq_refl A B) (at level 61, left associativity, format "A ⩒ B").

Arguments BI_ctx_hole {_ _}.

#[local] Reserved Notation "'![' γ ']' φ" (at level 1, format "![ γ ] φ").
#[local] Reserved Notation "Γ ⊦ A" (at level 70, no associativity, format "Γ  ⊦  A").
#[local] Reserved Notation "⟦ A ⟧" (at level 0, format "⟦ A ⟧").

(* The (-∗,⇒,⩑,1) fragment of LBI *)
Definition BI_fragment_impl_conj_unit c :=
  match c with
  | BI_unit BI_mult => true   (* 1 *)
  | BI_impl _       => true   (* -∗ and ⇒ *)
  | BI_conj BI_addi => true   (* ⩑ *)
  | _               => false  (* no other connective *)
  end.

#[local] Notation µ := BI_fragment_impl_conj_unit.

#[local] Notation "⨂ₘ" := BI_list_mult.

(* We work in cut-free fragments of LBI *)
#[local] Notation "Γ ⊦ A" := (LBI_provable BI_cut_free Γ A).

Section pseudo_exponential.

  Variable (prop : Set).

  (* We work in the (-∗,⇒,⩑,1) fragment of BI *)
  Implicit Types (φ : BI_form µ prop) (Γ : BI_bunch µ prop).

  (* We simulate ⊤ using 1⇒1 *)
  Notation "⊤" := (1⇒1).

  (** This is the "major breakthrought" that allows for the encoding
      of the dereliction rule in BI, see BI_pseudo_exp_derilection below,
      see 
          The logic of bunched implications is undecidable 
          Galatos, Jipsen, Knudstorp & Ramanayake. arXiv 2026  *)

  Definition BI_pseudo_exp γ φ := (⊤-∗((φ-∗γ)⇒γ))⩑1.
  Notation "![ γ ] φ" := (BI_pseudo_exp γ φ).

  (** We study the LBI proof theory of the pseudo-exponential ![γ]φ, 
      restricted to the (-∗,⇒,⩑,1) cut-free fragment of LBI. *)

  (** First some tools to facilitate LBI proofs *)

  Local Fact BI_unit_right_l k Γ γ :
             Γ ⊦ γ 
    → (*-----------------*)
         ø[k] ⊛[k] Γ ⊦ γ.
  Proof.
    apply BI_sp_equiv,
          BI_bequiv_sym,
          BI_bequiv_neut.
  Qed.

  Local Fact BI_unit_left_r k Γ γ :
          Γ ⊛[k] ø[k] ⊦ γ
    →  (*-----------------*)
             Γ ⊦ γ.
  Proof.
    apply BI_sp_equiv,
          BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _),
          BI_bequiv_neut.
  Qed.

  Local Fact BI_top_weak Γ : Γ ⊦ ⊤.
  Proof.
    change (BI_ctx_hole[Γ] ⊦ ⊤).
    apply BI_sp_weak,
          BI_sp_impl_r,
          BI_unit_right_l,
          BI_sp_axiom.
  Qed.

  Local Fact BI_cntr_all Γ γ : Γ ⊛ₐ Γ ⊦ γ → Γ ⊦ γ.
  Proof.
    intro.
    change (BI_ctx_hole[Γ] ⊦ γ).
    now apply BI_sp_cntr.
  Qed.

  Local Fact BI_simpl_imp_l Γ A B C :
          Γ ⊦ A    →     ⟨B⟩ ⊦ C
    →  (*------------------------*)
             Γ ⊛ₐ ⟨A⇒B⟩ ⊦ C.
  Proof. apply BI_sp_impl_l with (Γ := BI_ctx_hole). Qed.

  Local Fact BI_simpl_wand_l Γ A B C :
          Γ ⊦ A    →     ⟨B⟩ ⊦ C
    →  (*------------------------*)
             Γ ⊛ₘ ⟨A-∗B⟩ ⊦ C.
  Proof. apply BI_sp_impl_l with (Γ := BI_ctx_hole). Qed.

  (** Now the "weakening" rule for ![γ]φ *)

  Proposition BI_pseudo_exp_weak Γ γ φ ψ :
             Γ ⊦ ψ 
      (*------------------*)
    →    Γ ⊛ₘ ⟨![γ]φ⟩ ⊦ ψ.
  Proof.
    intros H.

    set (Σ := BI_ctx_comp BI_left BI_mult Γ BI_ctx_hole).
    change (Σ[⟨![γ]φ⟩] ⊦ ψ).
    apply BI_sp_conj_l.

    set (Σ' := BI_ctx_comp BI_left BI_mult Γ (BI_ctx_comp BI_right BI_addi ⟨1⟩ BI_ctx_hole)).
    change (Σ'[⟨⊤-∗(φ-∗γ)⇒γ⟩] ⊦ ψ).
    apply BI_sp_weak.

    change (Σ[øₐ ⊛ₐ ⟨1⟩] ⊦ ψ).
    apply BI_sp_equiv with Σ[⟨1⟩].
    1: apply BI_bequiv_congr, BI_bequiv_sym, BI_bequiv_neut.

    apply BI_sp_unit_l.
    simpl.

    revert H; apply BI_sp_equiv.
    apply BI_bequiv_sym,
          BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _),
          BI_bequiv_neut.
  Qed.

  Check BI_pseudo_exp_weak.

  (* We generalize the weakening rule to lists of ![γ]φ 

     Notice that ⨂ₘ[A₁;...;Aₙ] := A₁ ⊛ₘ (... ⊛ₘ (Aₙ ⊛ₘ 1)...) *)
  Lemma BI_list_mult_weak Σ Γ ψ (HΣ : ∀A, A ∊ Σ → ∃ γ φ, A = ![γ]φ) :
             Γ ⊦ ψ 
    →  (*---------------*)
          ⨂ₘ Σ ⊛ₘ Γ ⊦ ψ.
  Proof.
    rewrite <- Forall_forall in HΣ.
    intros H.
    induction HΣ as [ | A Σ (γ & φ & ->) _ IH ]; simpl.
    + revert H.
      apply BI_sp_equiv,
            BI_bequiv_sym,
            BI_bequiv_neut.
    + apply BI_sp_equiv with (1 := BI_bequiv_sym (BI_bequiv_assoc _ _ _ _)),
            BI_sp_equiv with (1 := BI_bequiv_comm _ _ _),
            BI_pseudo_exp_weak; trivial.
  Qed.

  (** Now we explain the "dereliction" rule as the combination of
      two ideas 1) & 2), leading to 3) when combined:
      1) recover φ in multiplicative context 
         from φ-∗γ)⇒γ in additive context
      2) extract of "copy" of φ in additive context 
         from (⊤-∗φ)⩑1 in multiplicative context
      3) Hence combined, we can extract a copy in multiplicative
         context. *)

  Local Proposition BI_first_idea Γ γ φ :
            Γ ⊛ₘ ⟨φ⟩ ⊦ γ
    → (*---------------------*)
         Γ ⊛ₐ ⟨(φ-∗γ)⇒γ⟩ ⊦ γ.
  Proof.
    intro.
    apply BI_simpl_imp_l.
    + now apply BI_sp_impl_r.
    + simpl; apply BI_sp_axiom.
  Qed.

  Local Proposition BI_second_idea Γ γ φ :
         (Γ ⊛ₘ ⟨(⊤-∗φ)⩑1⟩) ⊛ₐ ⟨φ⟩ ⊦ γ
    → (*------------------------------*)
            Γ ⊛ₘ ⟨(⊤-∗φ)⩑1⟩ ⊦ γ.
  Proof.
    set (Δ := Γ ⊛ₘ ⟨(⊤-∗φ)⩑1⟩).
    intros H.
    apply BI_cntr_all.
    unfold Δ at 2.

    set (Σ := BI_ctx_comp BI_left BI_addi Δ
             (BI_ctx_comp BI_left BI_mult Γ BI_ctx_hole)).
    change (Σ[⟨(⊤-∗φ)⩑1⟩] ⊦ γ).
    apply BI_sp_conj_l.
    simpl.

    set (Σ' := BI_ctx_comp BI_left BI_addi Δ
              (BI_ctx_comp BI_left BI_mult Γ 
              (BI_ctx_comp BI_left BI_addi ⟨⊤-∗φ⟩
               BI_ctx_hole))).
    change (Σ'[⟨1⟩] ⊦ γ).
    apply BI_sp_weak.
    simpl.

    change (Σ[⟨⊤-∗φ⟩ ⊛ₐ øₐ] ⊦ γ).
    apply BI_sp_equiv with (Σ[⟨⊤-∗φ⟩]).
    1: apply BI_bequiv_congr,
             BI_bequiv_congr,
             BI_bequiv_sym,
             BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _),
             BI_bequiv_neut.
    simpl.

    set (Σ'' := BI_ctx_comp BI_left BI_addi Δ BI_ctx_hole).
    change (Σ''[Γ ⊛ₘ ⟨⊤-∗φ⟩] ⊦ γ).
    apply BI_sp_impl_l; auto.

    apply BI_top_weak.
  Qed.

  Proposition BI_pseudo_exp_derilection Γ γ φ :
          Γ ⊛ₘ ⟨![γ]φ⟩ ⊛ₘ ⟨φ⟩ ⊦ γ
    →  (*-------------------------*)
            Γ ⊛ₘ ⟨![γ]φ⟩ ⊦ γ.
  Proof.
    intro.
    unfold BI_pseudo_exp.
    apply BI_second_idea.
    apply BI_first_idea.
    trivial.
  Qed.

  Check BI_pseudo_exp_derilection.

  (* We generalize the dereliction rule to lists 
     containing a pseudo exponential ![γ]φ *)

  Lemma BI_list_mult_derilection Σ γ φ (HΣ : ![γ]φ ∊ Σ) :
         ⨂ₘ Σ ⊛ₘ ⟨φ⟩ ⊦ γ 
    → (*-----------------*)
           ⨂ₘ Σ ⊦ γ.
  Proof.
    revert HΣ; intros (Σ' & H'%BI_list_mult_perm_bequiv)%permutation_in_head H.
    apply BI_sp_equiv with (1 := BI_bequiv_sym H').
    simpl.
    apply BI_sp_equiv with (1 := BI_bequiv_comm _ _ _).
    apply BI_pseudo_exp_derilection.
    revert H; apply BI_sp_equiv.
    do 2 apply BI_bequiv_sym,
               BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _).
    apply BI_bequiv_congr,
          BI_bequiv_trans with (1 := H'),
          BI_bequiv_comm.
  Qed.

  (** Now we recall the encoding of 2-ACM counter machines,
      (ie with FORK, INC, DEC and STOP but no zero test)
      in the (⩑,-∗) linear fragment of BI. *)

  Local Fact BI_FORK Γ φ ψ γ :
         Γ ⊦ φ    →    Γ ⊦ ψ 
    → (*---------------------*)
         Γ ⊛ₘ ⟨(φ⩑ψ)-∗γ⟩ ⊦ γ.
  Proof.
    intros.
    apply BI_simpl_wand_l.
    + now apply BI_cntr_all, BI_sp_conj_r.
    + apply BI_sp_axiom.
  Qed.

  Local Fact BI_INC Γ φ ψ γ :
             Γ ⊛ₘ ⟨φ⟩ ⊦ ψ
    → (*----------------------*)
         Γ ⊛ₘ ⟨(φ-∗ψ)-∗γ⟩ ⊦ γ.
  Proof.
    intros.
    apply BI_simpl_wand_l.
    + now apply BI_sp_impl_r.
    + apply BI_sp_axiom.
  Qed.

  Local Fact BI_DEC Γ φ ψ γ :
                Γ ⊦ ψ
    → (*---------------------------*)
         Γ ⊛ₘ ⟨φ⟩ ⊛ₘ ⟨φ-∗ψ-∗γ⟩ ⊦ γ.
  Proof.
    intros H.
    apply BI_sp_equiv with (1 := BI_bequiv_sym (BI_bequiv_assoc _ _ _ _)).

    set (Σ := BI_ctx_comp BI_left BI_mult Γ BI_ctx_hole).
    change (Σ[⟨φ⟩ ⊛ₘ ⟨φ-∗ψ-∗γ⟩] ⊦ γ).
    apply BI_sp_impl_l with (1 := BI_sp_axiom _ _).
    simpl.

    apply BI_simpl_wand_l; auto.
    apply BI_sp_axiom.
  Qed.

  Local Fact BI_STOP Γ γ :
              Γ ⊦ 1
    → (*-----------------*)
         Γ ⊛ₘ ⟨1-∗γ⟩ ⊦ γ.
  Proof.
    intros.
    apply BI_simpl_wand_l; auto.
    apply BI_sp_axiom.
  Qed.

  (** We finish with study the TPS semantics 
      of the pseudo-exponential ![γ]φ *)

  Variables (M : Type) (plus : M → M → M) (e : M)
            (neut : ∀x, plus e x = x)
            (comm : ∀ x y, plus x y = plus y x)
            (assoc : ∀ x y z, plus (plus x y) z = plus x (plus y z))

            (s : prop → M → Prop).

  Notation "⟦ A ⟧" := (tps_BI_form plus e s A).

  (* Semantically, ![γ]φ behaves much like φ⩑1 wrt TPS, hence
     irrelevant of the choice of γ *)
  Proposition tps_BI_pseudo_exp γ φ : ⟦φ⟧ e → ∀x, ⟦![γ]φ⟧ x ↔ e = x.
  Proof using comm neut.
    intros Hφ x; split.
    1: intros []; auto.
    intros <-.
    split; [ | reflexivity ].
    intros x _ H.
    rewrite comm, neut in H.
    rewrite comm; apply H; auto.
  Qed. 

End pseudo_exponential.

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

  (** We start from a list of instructions Σ
      and a list of location over approximating
      the source location of instructions 
      occuring in Σ *)

  Variables (Σ : list (@acm2_instr loc))
            (l : list loc)
            (HΣl : ∀i, i ∊ Σ → acm2_instr_src i ∊ l).

  (** This is a "positive" encoding of 2-ACM in
      the (⩑,-∗) linear fragment of ILL/BI
        FORKₐ p q r --> q⩑r -∗ p
        INCₐ α p q  --> (α -∗ q) -∗ p
        DECₐ β p q  --> β -∗ q -∗ p
        STOPₐ p     --> 1 -∗ p

      Notice that locations in loc are encoded into
      variables in the left part of loc+bool
      while the right part is used from the two
      counters α/β *)

  Notation α := true.
  Notation β := false.

  Definition acm2_instr_to_BI i : BI_form µ (loc+bool) :=
    match i with
    | FORKₐ p q r => (£(inl q) ⩑ £(inl r)) -∗ £(inl p)
    | INCₐ c p q  => (£(inr c) -∗ £(inl q)) -∗ £(inl p)
    | DECₐ c p q  => £(inr c) -∗ £(inl q) -∗ £(inl p)
    | STOPₐ p     => 1 -∗ £(inl p)
    end.

  Notation encᵢ := acm2_instr_to_BI.

  Notation "![ γ ] φ" := (BI_pseudo_exp γ φ).

  Check list_prod.

  Definition acm2_ctx_to_BI x y :=
       repeat £(inr α) x
    ++ repeat £(inr β) y 
    ++ list_prod (λ p i, ![£(inl p)](encᵢ i)) l Σ.

  Notation enc := acm2_ctx_to_BI.

  (* enc x y collects all encodings of instruction 
     ![p](encᵢ i) for any location that might occur
     in any computation *)
  Local Fact In_acm2_ctx_to_BI x y i p :
      i ∊ Σ 
    → p = acm2_instr_src i
    → ![£(inl p)](encᵢ i) ∊ enc x y.
  Proof using HΣl.
    intros H1 H2.
    unfold acm2_ctx_to_BI.
    rewrite !in_app_iff; do 2 right.
    apply list_prod_spec.
    exists p, i; split; subst; auto.
  Qed.

  (** enc x y also contains x copies of £α and y copies of £β *)

  Local Fact acm2_ctx_to_BI_x x y Δ : 
    ⨂ₘ (enc (1+x) y) ⊛ₘ Δ ≡ ⨂ₘ (enc x y) ⊛ₘ ⟨£(inr α)⟩ ⊛ₘ Δ.
  Proof. 
    do 2 apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _), BI_bequiv_sym.
    apply BI_bequiv_congr, BI_bequiv_comm.
  Qed.

  Local Fact acm2_ctx_to_BI_y x y Δ : 
    ⨂ₘ (enc x (1+y)) ⊛ₘ Δ ≡ ⨂ₘ (enc x y) ⊛ₘ ⟨£(inr β)⟩ ⊛ₘ Δ.
  Proof. 
    do 2 apply BI_bequiv_trans with (1 := BI_bequiv_comm _ _ _),
               BI_bequiv_sym.
    apply BI_bequiv_congr,
          BI_bequiv_sym, 
          BI_bequiv_trans with (1 := BI_list_mult_snoc _ _),
          BI_list_mult_perm_bequiv,
          perm_trans with (2 := Permutation_app_swap_app _ _ _),
          perm_skip,
          Permutation_app_swap_app.
  Qed.

  Hint Resolve In_acm2_ctx_to_BI : core.

  (** We can now show that our positive encoding is sound
      wrt to cut-free provability in the (-∗,⇒,⩑,1) fragment *)

  Local Lemma acm2_encode_sound x y p :
      acm2_accept Σ x y p
    → ⨂ₘ (enc x y) ⊦ £(inl p).
  Proof using HΣl.
    induction 1 as [ p H 
                   | x y p q r H _ IH1 _ IH2
                   | x y p q H _ IH
                   | x y p q H _ IH
                   | 
                   | 
                   ];
        match goal with
        | _ : ?i ∊ Σ |- _ => apply BI_list_mult_derilection
                               with (φ := acm2_instr_to_BI i)
        end; auto; simpl acm2_instr_to_BI.
    + apply BI_STOP.
      unfold acm2_ctx_to_BI; simpl.
      apply BI_unit_left_r with (k := BI_mult),
            BI_list_mult_weak.
      2: apply BI_sp_unit_r.
      intros A (k & i & -> & [])%list_prod_spec; eauto.
    + apply BI_FORK; auto.
    + apply BI_INC.
      revert IH; apply BI_sp_equiv.
      apply BI_bequiv_sym, 
            BI_bequiv_trans with (1 := BI_list_mult_snoc _ _),
            BI_list_mult_perm_bequiv; auto.
    + apply BI_INC.
      revert IH; apply BI_sp_equiv.
      apply BI_bequiv_sym, 
            BI_bequiv_trans with (1 := BI_list_mult_snoc _ _),
            BI_list_mult_perm_bequiv.
      unfold acm2_ctx_to_BI.
      apply perm_trans with (2 := Permutation_app_swap_app _ _ _),
            perm_skip,
            Permutation_app_swap_app.
    + apply BI_sp_equiv with (1 := BI_bequiv_sym (acm2_ctx_to_BI_x _ _ _)).
      now apply BI_DEC.
    + apply BI_sp_equiv with (1 := BI_bequiv_sym (acm2_ctx_to_BI_y _ _ _)).
      now apply BI_DEC.
  Qed.

  Section completeness.

    (** For the completeness, we use the soundness of
        TPS semantics for LBI. We use nat² as a model
        where (x,y) in nat² represents the value of
        α/β. *)

    Let s (v : loc + bool) :=
      match v with
      | inl p => λ '(x,y), acm2_accept Σ x y p
      | inr α => eq (1,0)%nat 
      | inr β => eq (0,1)%nat
      end.

    Notation "⟦ A ⟧" := (tps_BI_form pair_add (0,0) s A).

    Hint Constructors acm2_accept : core.

    (* the semantics of instructions contains the unit of nat² *)
    Local Lemma tps_instr_sound i : i ∊ Σ → ⟦encᵢ i⟧ (0,0).
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

    Variables (x y : nat) (p : loc) (Hxyp : ⨂ₘ (enc x y) ⊦ £(inl p)).

    Hint Resolve pair_add_zero_left pair_add_comm pair_add_assoc : core.

    Lemma acm2_encode_complete : acm2_accept Σ x y p.
    Proof using Hxyp.
      (* TPS is sound for LBI *)
      apply tps_LBI_sound with (plus := pair_add) (e := (0,0)) (s := s) (m := (x,y)) in Hxyp; auto.
      (* We reorder ⨂ₘ (enc x y) *)
      apply tps_BI_equiv with (⨂ₘ (repeat £(inr α) x)
                           ⊛ₘ (⨂ₘ (repeat £(inr β) y) 
                           ⊛ₘ  ⨂ₘ (list_prod (λ p i, ![£(inl p)](encᵢ i)) l Σ)));
        auto.
      + (* This is a reordering *)
        do 2 apply BI_bequiv_trans with (1 := BI_list_mult_app _ _),
                   BI_bequiv_congr; auto using BI_bequiv_refl.
      + (* (x,0) belongs to ⟦⨂ₘ (repeat £(inr α) x)⟧
           (0,y) belongs to ⟦⨂ₘ (repeat £(inr β) y)⟧
           (0,0) belongs to the rest ⟦⨂ₘ (map ![_](_) l⨯Σ)⟧ 
           so their sum (x,y) = (x,0)+(0,y)+(0,0) 
           belongs to the semantics of this bunch *)
        exists (x,0), (0,y); split; simpl; auto; split;
          [ | exists (0,y), (0,0); split; simpl; auto; split ].
        * clear Hxyp.
          induction x as [ | n ]; simpl; auto.
          exists (1,0)%nat, (n,0); auto.
        * clear Hxyp.
          induction y as [ | n ]; simpl; auto.
          exists (0,1)%nat, (0,n); auto.
        * apply tps_BI_bunch_list_mult; auto.
          intros ? (? & ? & -> & [])%list_prod_spec.
          apply tps_BI_pseudo_exp; auto.
          now apply tps_instr_sound.
    Qed.

  End completeness.

End ACM2_to_BI.

#[local] Hint Resolve acm2_encode_sound acm2_encode_complete in_map : core.

(** This establishes the correctness of the reduction 2-ACM ~~> LBI *)
Theorem acm2_to_BI_correctness (loc : Set) Σ x y (p : loc) :
    acm2_accept Σ x y p
  ↔ LBI_provable BI_cut_free (BI_list_mult (acm2_ctx_to_BI Σ (map (@acm2_instr_src _) Σ) x y)) £(inl p).
Proof. split; eauto. Qed.

Check acm2_to_BI_correctness.




