(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Arith Lia List Utf8.

From Undecidability.Shared.Libs.DLW 
  Require Import utils pos vec.

From Undecidability.MinskyMachines 
  Require Import ndMM2 ACM2.

Import ACM2_Notations ndMM2_Notations ListNotations.

#[local] Notation α := true.
#[local] Notation β := false.

Section ACM2_sem.

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

  Local Definition acm2_tps_lolipop (X Y : _ → Prop) m := ∀a, X a → Y (a +ₐ m).
  Local Definition acm2_tps_tensor (X Y : _ → Prop) m := ∃ a b, m = a +ₐ b ∧ X a ∧ Y b. 
  Local Definition acm2_tps_with (X Y : nat*nat → Prop) m := X m ∧ Y m.

End ACM2_sem.

#[local] Infix "-∘" := acm2_tps_lolipop (at level 65, right associativity).
#[local] Infix "∘" := acm2_tps_tensor (at level 64, left associativity).
#[local] Infix "⊓" := acm2_tps_with (at level 66, left associativity). 
#[local] Notation "X ⊆ Y" := (∀m, X m → Y m) (at level 70).
#[local] Infix "∊" := In (at level 70).

Section ACM2_utils.

  Variables loc : Set.

  Implicit Type (i : acm2_instr loc) (Σ : list (acm2_instr loc)).

  Hint Constructors acm2_accept : core.

  Remark acm2_accept_mono Σ Θ a b u : incl Σ Θ → Σ ⫽ₐ a ⊕ b ⊦ u → Θ ⫽ₐ a ⊕ b ⊦ u.
  Proof. intros H; red in H; induction 1; eauto. Qed.

  (* We have freedom for interpreting locations *)
  Variables (s : loc → nat*nat → Prop).
  
  (* But this is fixed for the registers α/β *)
  Let v γ :=
    match γ with
    | α => eq (1,0)
    | β => eq (0,1)
    end.

  (** Linear logic semantics for ACM2 instructions *)
  Definition acm2_sem i := 
    match i with
    | STOPₐ p     => s p                  (*             p   *)
    | FORKₐ p q r => (s q ⊓ s r) -∘ s p   (*  (q & r) -* p   *)
    | DECₐ γ p q  => v γ -∘ s q -∘ s p    (*  γ -* q  -* p   *)
    | INCₐ γ p q  => (v γ -∘ s q) -∘ s p  (* (γ -* q) -* p   *) 
    end.

  Notation "⟦ i ⟧ᵢ" := (acm2_sem i) (at level 0, format "⟦ i ⟧ᵢ").

  (** Σ = [i₁;...;iₙ] is interpreted as !i₁,...,!iₙ 
      and ⟦!i⟧ = ⟦i⟧ ⊓ {(0,0)} so we directly
      compute

         ⟦Σ⟧ = ⟦i₁⟧ ⊓ ...⊓ ⟦iₙ⟧ ⊓ ⟦i₁⟧ ⊓ {(0,0)} 
  *)
  Definition acm2_list_sem := fold_right (λ i c, ⟦i⟧ᵢ ⊓ c) (eq (0,0)).

  Notation "⟦ Σ ⟧𞁞" := (acm2_list_sem Σ) (at level 0, format "⟦ Σ ⟧𞁞").

  Fact acm2_list_sem_In_zero Σ : Forall (λ i, ⟦i⟧ᵢ (0,0)) Σ → ⟦Σ⟧𞁞 (0,0).
  Proof. induction 1; simpl; auto; split; auto. Qed.

  Fact acm2_list_sem_zero Σ : ⟦Σ⟧𞁞 ⊆ eq (0,0).
  Proof.
    intro; induction Σ as [ | ? ? IH ].
    + now intros [].
    + now intros [ _ ?%IH ].
  Qed.

  Hint Resolve acm2_list_sem_zero : core.

  Fact acm2_list_sem_In i Σ : i ∊ Σ → ⟦Σ⟧𞁞 ⊆ ⟦i⟧ᵢ ⊓ eq (0,0).
  Proof.
    induction Σ as [ | j l IHl ].
    1: now intros [].
    + intros [ <- | Hi ] m; simpl.
      * intros []; split; eauto.
      * specialize (IHl Hi). 
        intros []; split; eauto; now apply IHl.
  Qed.

  Theorem acm2_tps_sound Σ x y u : 
       Σ ⫽ₐ x ⊕ y ⊦ u
    → ⟦Σ⟧𞁞 ∘ (eq (x,y)) ⊆ s u.
  Proof.
    induction 1 as [ p H 
                   | x y p q r H Hq IHq Hr IHr 
                   | x y p q H Hq IHq 
                   | x y p q H Hq IHq 
                   | x y p q H Hq IHq 
                   | x y p q H Hq IHq ]; intros ? (m & H1 & -> & H2 & <-);
      destruct acm2_list_sem_In with (1 := H) (2 := H2) as (H1 & <-).
    + apply H1.
    + rewrite pair_add_comm; apply H1; split.
      * apply IHq; exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
      * apply IHr; exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
    + rewrite pair_add_comm; apply H1.
      intros ? <-; simpl.
      apply IHq.
      exists (0,0), (1+x,y); auto.
    + rewrite pair_add_comm; apply H1.
      intros ? <-; simpl.
      apply IHq.
      exists (0,0), (x,1+y); auto.
    + rewrite pair_add_comm, pair_add_one_left, pair_add_assoc.
      apply H1; simpl; auto.
      apply IHq.
      exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
    + rewrite pair_add_comm, pair_add_one_right, pair_add_assoc.
      apply H1; simpl; auto.
      apply IHq.
      exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
  Qed.

End ACM2_utils.

#[local] Notation "Σ ⫽ₙ x ⊕ y ⊦ p" := (@ndmm2_accept _ Σ x y p) (at level 70).

Section ndMM2_ACM2.

  Variables loc : Set.

  Implicit Types (Σ : list (ndmm2_instr loc)) (x y : nat) (p : loc).

  (* The two bool locations in loc' are fresh locations that
     each perform nullification of the other register *)
  Let loc' := (loc + bool)%type.

  (* ZEROₙ α p q is encoded as [ FORKₐ p α q ; DECₐ β α α ; STOPₐ α ]
     but [DECₐ β α α ; STOPₐ α] are factored globally *)

  Let base : list (acm2_instr loc') := 
    [ DECₐ β (inr α) (inr α) ; STOPₐ (inr α);
      DECₐ α (inr β) (inr β) ; STOPₐ (inr β) ].

  Definition ndmm2_to_acm2 (i : ndmm2_instr loc) : acm2_instr loc' :=
    match i with
    | STOPₙ p     => STOPₐ (inl p)
    | INCₙ b p q  => INCₐ b (inl p) (inl q) 
    | DECₙ b p q  => DECₐ b (inl p) (inl q)
    | ZEROₙ b p q => FORKₐ (inl p) (inr b) (inl q)
    end.

  Fact ndmm2_to_acm2_In_map Σ i : i ∊ Σ → ndmm2_to_acm2 i ∊ base ++ map ndmm2_to_acm2 Σ.
  Proof. intros; apply in_or_app; right; now apply in_map. Qed.

  Fact ndmm2_to_acm2_In_base Σ i : i ∊ base → i ∊ base ++ map ndmm2_to_acm2 Σ.
  Proof. intros; now apply in_or_app; left. Qed.

  Hint Constructors acm2_accept : core.
  Hint Resolve ndmm2_to_acm2_In_map ndmm2_to_acm2_In_base : core.

  Lemma ndmm2_to_acm2_sound Σ x y p :
     Σ ⫽ₙ x ⊕ y ⊦ p → base ++ map ndmm2_to_acm2 Σ ⫽ₐ x ⊕ y ⊦ inl p.
  Proof.
    induction 1 as [ p H
                   | x y p q H _ IH
                   | x y p q H _ IH
                   | x y p q H _ IH
                   | x y p q H _ IH
                   | y p q H _ IH
                   | x p q H _ IH ]; try apply ndmm2_to_acm2_In_map in H; eauto.
    + constructor 2 with (inr α) (inl q); eauto.
      clear H IH.
      (* We can nullify y using DECₐ β α α repeatedly in base
         and then STOPₐ α with y is null *)
      induction y as [ | y IHy ].
      * constructor 1; apply ndmm2_to_acm2_In_base; simpl; eauto.
      * constructor 6 with (inr α); auto.
        apply ndmm2_to_acm2_In_base; simpl; eauto.
    + constructor 2 with (inr β) (inl q); eauto.
      clear H IH.
      (* We nullify x ... *)
      induction x as [ | x IHy ].
      * constructor 1; apply ndmm2_to_acm2_In_base; simpl; eauto.
      * constructor 5 with (inr β); auto.
        apply ndmm2_to_acm2_In_base; simpl; eauto.
  Qed.

  Section completeness.

    Variables (Σ : _).

    (** To show completeness, we exploit soundness of trivial
        phase semantics for ACM2  *)

    (* We interpret location inl _ using Σ ⫽ₙ _ ⊕ _ ⊦ _ 
                         and inr _ using the two axis (0,_) and (_,0) *)
    Let s (k : loc') :=
      match k with
      | inl p => λ '(x,y), Σ ⫽ₙ x ⊕ y ⊦ p
      | inr α => λ '(x,_), x = 0
      | inr β => λ '(_,y), y = 0
      end.

    Hint Constructors ndmm2_accept : core.

    Lemma ndmm2_to_acm2_complete x y p :
        base ++ map ndmm2_to_acm2 Σ ⫽ₐ x ⊕ y ⊦ inl p
      → Σ ⫽ₙ x ⊕ y ⊦ p.
    Proof.
      intros HΣ.
      apply (acm2_tps_sound _ s) with (m := (x,y)) in HΣ; auto.
      exists (0,0), (x,y); rewrite pair_add_zero_left; split; [ | split ]; auto.
      clear x y p HΣ.
      apply acm2_list_sem_In_zero, Forall_forall.
      intros i [ [<-|[<-|[<-|[<-|[]]]]] | (j & <- & Hj)%in_map_iff]%in_app_iff; simpl; auto.
      + intros m <-; rewrite pair_add_zero_right; now intros [] ->.
      + intros m <-; rewrite pair_add_zero_right; now intros [] ->.
      + destruct j as [ p | b p q | b p q | b p q ]; simpl.
        * now constructor 1.
        * intros [] H; rewrite pair_add_zero_right.
          destruct b.
          - constructor 2 with q; auto; apply (H _ eq_refl).
          - constructor 3 with q; auto; apply (H _ eq_refl).
        * intros m H; destruct b; simpl in H; subst m; rewrite pair_add_zero_right.
          - intros [] ?; rewrite <- pair_add_one_left; eauto.
          - intros [] ?; rewrite <- pair_add_one_right; eauto.
        * intros [] H; destruct b; simpl in H; destruct H; rewrite pair_add_zero_right; subst; eauto.
    Qed.

  End completeness.

  Hint Resolve ndmm2_to_acm2_sound ndmm2_to_acm2_complete : core.

  Theorem ndmm2_to_acm2_correctness Σ x y p :
    Σ ⫽ₙ x ⊕ y ⊦ p ↔ base ++ map ndmm2_to_acm2 Σ ⫽ₐ x ⊕ y ⊦ inl p.
  Proof. split; auto. Qed.

End ndMM2_ACM2.

Print ndmm2_to_acm2.
Check ndmm2_to_acm2_correctness.
