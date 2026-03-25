(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Arith Lia List Utf8.

From Undecidability.MinskyMachines 
  Require Import ndMM2 ACM2.

Import ACM2_Notations ndMM2_Notations ListNotations.

Section TPS_sem.

  (** Trivial phase semantics for linear logic over nat² *)

  Local Definition pair_add '(x₁,y₁) '(x₂,y₂) := (x₁+x₂,y₁+y₂).
  Infix "+ₐ" := pair_add (at level 61).

  Local Fact pair_add_zero_left p : (0,0) +ₐ p = p.
  Proof. now destruct p. Qed.

  Local Fact pair_add_comm p q : p +ₐ q = q +ₐ p.
  Proof. revert p q; intros [] []; simpl; f_equal; lia. Qed.

  Local Fact pair_add_zero_right p : p +ₐ (0,0) = p.
  Proof. now rewrite pair_add_comm, pair_add_zero_left. Qed.

  Local Fact pair_add_one_left x y : (1+x,y) = (x,y) +ₐ (1,0).
  Proof. simpl; f_equal; lia. Qed.

  Local Fact pair_add_one_right x y : (x,1+y) = (x,y) +ₐ (0,1).
  Proof. simpl; f_equal; lia. Qed.

  Local Fact pair_add_assoc p q r : (p +ₐ q) +ₐ r = p +ₐ (q +ₐ r).
  Proof. revert p q r; intros [] [] []; simpl; f_equal; lia. Qed.

  Local Definition tps_lolipop (X Y : _ → Prop) m := ∀a, X a → Y (a +ₐ m).
  Local Definition tps_tensor (X Y : _ → Prop) m := ∃ a b, m = a +ₐ b ∧ X a ∧ Y b. 
  Local Definition tps_with (X Y : nat*nat → Prop) m := X m ∧ Y m.

End TPS_sem.

#[local] Notation α := true.
#[local] Notation β := false.

#[local] Infix "-∘" := tps_lolipop (at level 65, right associativity).
#[local] Infix "∘" := tps_tensor (at level 64, left associativity).
#[local] Infix "⊓" := tps_with (at level 62, left associativity). 
#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70).
#[local] Infix "∊" := In (at level 70).

Section ACM2_TPS_sound.

  Variables loc : Set.

  Implicit Type (i : acm2_instr loc) (Σ : list (acm2_instr loc)).

  Hint Constructors acm2_accept : core.

  Remark acm2_accept_mono Σ Θ a b u : incl Σ Θ → Σ ⫽ₐ a ⊕ b ⊦ u → Θ ⫽ₐ a ⊕ b ⊦ u.
  Proof. intros H; red in H; induction 1; eauto. Qed.

  (** We have freedom for interpreting locations using TPS *)

  Variable (s : loc → nat*nat → Prop).
  Notation "⟦ p ⟧ₗ" := (s p) (at level 0, format "⟦ p ⟧ₗ").

  (** But the registers α/β are interpreted this way 
      ie ⟦α⟧ = {(1,0)} and ⟦β⟧ = {(0,1)}  *)

  Let v γ :=
    match γ with
    | α => eq (1,0)
    | β => eq (0,1)
    end.

  (** Linear logic TPS semantics for ACM2 instructions *)

  Definition acm2_sem i := 
    match i with
    | STOPₐ p     =>                  ⟦p⟧ₗ  (*             p   *)
    | FORKₐ p q r =>  ⟦q⟧ₗ ⊓ ⟦r⟧ₗ  -∘ ⟦p⟧ₗ  (*  (q & r) -* p   *)
    | DECₐ γ p q  =>  v γ -∘ ⟦q⟧ₗ  -∘ ⟦p⟧ₗ  (*  γ -* q  -* p   *)
    | INCₐ γ p q  => (v γ -∘ ⟦q⟧ₗ) -∘ ⟦p⟧ₗ  (* (γ -* q) -* p   *) 
    end.

  Notation "⟦ i ⟧ᵢ" := (acm2_sem i) (at level 0, format "⟦ i ⟧ᵢ").

  (** Σ = [i₁;...;iₙ] is interpreted as !i₁,...,!iₙ
      and ⟦!i⟧ = ⟦i⟧ ⊓ {(0,0)} in TPS so we directly
      compute

         ⟦Σ⟧ = ⟦i₁⟧ ⊓ ...⊓ ⟦iₙ⟧ ⊓ ⟦i₁⟧ ⊓ {(0,0)}  *)

  Definition acm2_list_sem := fold_right (λ i c, ⟦i⟧ᵢ ⊓ c) (eq (0,0)).
  Notation "⟦ Σ ⟧𞁞" := (acm2_list_sem Σ) (at level 0, format "⟦ Σ ⟧𞁞").

  Fact acm2_list_sem_In_zero Σ : Forall (λ i, ⟦i⟧ᵢ (0,0)) Σ → ⟦Σ⟧𞁞 (0,0).
  Proof. induction 1; simpl; auto; split; auto. Qed.

  Fact acm2_list_sem_le_zero Σ : ⟦Σ⟧𞁞 ⊆ eq (0,0).
  Proof.
    intro; induction Σ as [ | ? ? IH ].
    + now intros [].
    + now intros [ _ ?%IH ].
  Qed.

  Hint Resolve acm2_list_sem_le_zero : core.

  Fact acm2_list_sem_le_instr i Σ : i ∊ Σ → ⟦Σ⟧𞁞 ⊆ ⟦i⟧ᵢ ⊓ eq (0,0).
  Proof.
    induction Σ as [ | j l IHl ].
    1: now intros [].
    + intros [ <- | Hi ] m; simpl;
        intros []; split; eauto.
      now apply (IHl Hi).
  Qed.

  Theorem acm2_tps_sound Σ x y u : 
       Σ ⫽ₐ x ⊕ y ⊦ u
    → ⟦Σ⟧𞁞 ∘ (eq (x,y)) ⊆ s u.
  Proof.
    induction 1 as [ p H 
                   | x y p q r H _ IHq _ IHr 
                   | x y p q H _ IHq 
                   | x y p q H _ IHq 
                   | x y p q H _ IHq 
                   | x y p q H _ IHq ]; intros ? (m & H1 & -> & H2 & <-);
      destruct acm2_list_sem_le_instr with (1 := H) (2 := H2) as (H1 & <-);
      try rewrite pair_add_comm.
    + apply H1.
    + apply H1; split; [ apply IHq | apply IHr ];
        exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
    + apply H1.
      intros ? <-; simpl.
      apply IHq.
      exists (0,0), (1+x,y); auto.
    + apply H1.
      intros ? <-; simpl.
      apply IHq.
      exists (0,0), (x,1+y); auto.
    + rewrite pair_add_one_left, pair_add_assoc.
      apply H1; simpl; auto.
      apply IHq.
      exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
    + rewrite pair_add_one_right, pair_add_assoc.
      apply H1; simpl; auto.
      apply IHq.
      exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
  Qed.

End ACM2_TPS_sound.

Arguments acm2_sem {_}.

#[local] Notation "Σ ⫽ₙ x ⊕ y ⊦ p" := (@ndmm2_accept _ Σ x y p) (at level 70).

Section ndMM2_reduces_to_ACM2.

  Variables loc : Set.

  Implicit Types (Σ : list (ndmm2_instr loc)) 
                 (i : ndmm2_instr loc)
                 (x y : nat) (p : loc).

  (** The two bool locations in loc' are fresh locations that
      each perform nullification of the other register *)

  Notation loc' := (loc + bool)%type.

  (** All instructions except ZEROₙ are translated as is

      ZEROₙ α p q is encoded as [ FORKₐ p α q ; DECₐ β α α ; STOPₐ α ]
      but [DECₐ β α α ; STOPₐ α] are factored globally *)

  Let base : list (acm2_instr loc') := 
    [ DECₐ β (inr α) (inr α) ; STOPₐ (inr α);
      DECₐ α (inr β) (inr β) ; STOPₐ (inr β) ].

  Definition ndmm2_to_acm2 i : acm2_instr loc' :=
    match i with
    | STOPₙ p     => STOPₐ (inl p)
    | INCₙ b p q  => INCₐ b (inl p) (inl q) 
    | DECₙ b p q  => DECₐ b (inl p) (inl q)
    | ZEROₙ b p q => FORKₐ (inl p) (inr b) (inl q)
    end.

  Definition list_ndmm2_to_acm2 Σ := base ++ map ndmm2_to_acm2 Σ.

  Fact ndmm2_to_acm2_In_map Σ i : i ∊ Σ → ndmm2_to_acm2 i ∊ list_ndmm2_to_acm2 Σ.
  Proof. intros; apply in_or_app; right; now apply in_map. Qed.

  Fact ndmm2_to_acm2_In_base Σ j : j ∊ base → j ∊ list_ndmm2_to_acm2 Σ.
  Proof. intros; now apply in_or_app; left. Qed.

  Hint Constructors acm2_accept : core.
 
  Fact ndmm2_to_acm2_null_α Σ y : list_ndmm2_to_acm2 Σ ⫽ₐ 0 ⊕ y ⊦ inr α.
  Proof.
    (* We can nullify y using DECₐ β α α repeatedly in base
         and then STOPₐ α with y is null *)
    induction y as [ | y IHy ].
    + constructor 1; apply ndmm2_to_acm2_In_base; simpl; eauto.
    + constructor 6 with (inr α); auto.
      apply ndmm2_to_acm2_In_base; simpl; eauto.
  Qed.

  Fact ndmm2_to_acm2_null_β Σ x : list_ndmm2_to_acm2 Σ ⫽ₐ x ⊕ 0 ⊦ inr β.
  Proof.
    (* We can nullify x using DECₐ α β β repeatedly in base
         and then STOPₐ β with x is null *)
    induction x as [ | x IHy ].
    + constructor 1; apply ndmm2_to_acm2_In_base; simpl; eauto.
    + constructor 5 with (inr β); auto.
      apply ndmm2_to_acm2_In_base; simpl; eauto.
  Qed.

  Hint Resolve ndmm2_to_acm2_null_α
               ndmm2_to_acm2_null_β : core.

  Lemma ndmm2_to_acm2_sound Σ x y p :
     Σ ⫽ₙ x ⊕ y ⊦ p → list_ndmm2_to_acm2 Σ ⫽ₐ x ⊕ y ⊦ inl p.
  Proof.
    induction 1;
      match goal with
      | H: _ ∊ Σ |- _ => try apply ndmm2_to_acm2_In_map in H
      end; eauto.
  Qed.

  Section completeness.

    Variables (Σ : _).

    (** To show completeness of the reduction, we exploit the 
        soundness of TPS for ACM2  *)

    (* We interpret location inl _ using Σ ⫽ₙ _ ⊕ _ ⊦ _ 
                         and inr _ using the two axis (0,_) and (_,0) *)
    Let s (k : loc') :=
      match k with
      | inl p => λ '(x,y), Σ ⫽ₙ x ⊕ y ⊦ p
      | inr α => λ '(x,_), x = 0
      | inr β => λ '(_,y), y = 0
      end.

    Hint Constructors ndmm2_accept : core.

    (** We show that TPS for every formula in list_ndmm2_to_acm2 Σ contains (0,0) *)

    Proposition list_ndmm2_to_acm2_zero j : j ∊ list_ndmm2_to_acm2 Σ → acm2_sem s j (0, 0).
    Proof.
      intros [ [<-|[<-|[<-|[<-|[]]]]] 
             | (i & <- & Hi)%in_map_iff]%in_app_iff; simpl; auto.
      + intros m <-; rewrite pair_add_zero_right; now intros [] ->.
      + intros m <-; rewrite pair_add_zero_right; now intros [] ->.
      + destruct i as [ p | b p q | b p q | b p q ]; simpl.
        * now constructor 1.
        * intros [] H; rewrite pair_add_zero_right.
          destruct b.
          - constructor 2 with q; auto; apply (H _ eq_refl).
          - constructor 3 with q; auto; apply (H _ eq_refl).
        * intros m H; destruct b; simpl in H; subst; rewrite pair_add_zero_right.
          - intros [] ?; rewrite <- pair_add_one_left; eauto.
          - intros [] ?; rewrite <- pair_add_one_right; eauto.
        * destruct b; intros [] []; rewrite pair_add_zero_right; subst; eauto.
    Qed.

    Hint Resolve list_ndmm2_to_acm2_zero : core.

    Lemma ndmm2_to_acm2_complete x y p :
      list_ndmm2_to_acm2 Σ ⫽ₐ x ⊕ y ⊦ inl p → Σ ⫽ₙ x ⊕ y ⊦ p.
    Proof.
      intros HΣ.
      (* We use soundness of TPS here *)
      apply (acm2_tps_sound _ s) with (m := (x,y)) in HΣ; auto.
      exists (0,0), (x,y); rewrite pair_add_zero_left; split; [ | split ]; auto.
      (* TPS for list_ndmm2_to_acm2 Σ contains (0,0) *)
      apply acm2_list_sem_In_zero, Forall_forall; auto.
    Qed.

  End completeness.

  Hint Resolve ndmm2_to_acm2_sound ndmm2_to_acm2_complete : core.

  Theorem ndmm2_to_acm2_correctness Σ x y p :
    Σ ⫽ₙ x ⊕ y ⊦ p ↔ list_ndmm2_to_acm2 Σ ⫽ₐ x ⊕ y ⊦ inl p.
  Proof. split; auto. Qed.

End ndMM2_reduces_to_ACM2.

Section ACM2_map.

  Variables (loc loc' : Set)
            (φ : loc → loc').

  Definition acm2_instr_map (i : acm2_instr loc) :=
    match i with
    | STOPₐ p     => STOPₐ (φ p)
    | INCₐ b p q  => INCₐ b (φ p) (φ q) 
    | DECₐ b p q  => DECₐ b (φ p) (φ q)
    | FORKₐ p q r => FORKₐ (φ p) (φ q) (φ r)
    end.

  Hint Constructors acm2_accept : core.

  Hint Resolve in_map : core.

  Theorem acm2_map_sound Σ x y p : 
      Σ ⫽ₐ x ⊕ y ⊦ p
    → map acm2_instr_map Σ ⫽ₐ x ⊕ y ⊦ φ p.
  Proof.
    induction 1; 
      match goal with
      | H: _ ∊ Σ |- _ => apply in_map with (f := acm2_instr_map) in H
      end; eauto.
  Qed.

End ACM2_map.

Arguments acm2_instr_map {_ _}.

Section ACM2_embed.

  Variables (loc loc' : Set)
            (φ : loc → loc')
            (ψ : loc' → loc)
            (Hφψ : ∀p, ψ (φ p) = p).

  Fact acm2_instr_embed i : acm2_instr_map ψ (acm2_instr_map φ i) = i.
  Proof using Hφψ. destruct i; simpl; f_equal; auto. Qed.

  Theorem acm2_embed_correctness Σ x y p :
    Σ ⫽ₐ x ⊕ y ⊦ p ↔ map (acm2_instr_map φ) Σ ⫽ₐ x ⊕ y ⊦ φ p.
  Proof using Hφψ.
    split.
    + apply acm2_map_sound.
    + intros H%(acm2_map_sound _ _ ψ).
      rewrite map_map, Hφψ, map_ext with (g := fun x => x) in H.
      * now rewrite map_id in H.
      * intros []; simpl; now rewrite !Hφψ.
  Qed.

End ACM2_embed.
