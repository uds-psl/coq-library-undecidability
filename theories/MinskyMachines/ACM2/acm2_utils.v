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

Section ACM2_utils.

  Variables loc : Set.

  Implicit Type (Σ : list (acm2_instr loc)).

  Hint Constructors acm2_accept : core.

  Fact acm2_accept_mono Σ Θ a b u : incl Σ Θ → Σ ⫽ₐ a ⊕ b ⊦ u → Θ ⫽ₐ a ⊕ b ⊦ u.
  Proof. intros H; red in H; induction 1; eauto. Qed.

  Local Definition pair_add '(x1,y1) '(x2,y2) := (x1+x2,y1+y2).
  Infix "+ₐ" := pair_add (at level 61).

  Fact pair_add_zero_left p : (0,0) +ₐ p = p.
  Proof. now destruct p. Qed.

  Fact pair_add_comm p q : p +ₐ q = q +ₐ p.
  Proof. revert p q; intros [] []; simpl; f_equal; lia. Qed.

  Fact pair_add_zero_right p : p +ₐ (0,0) = p.
  Proof. now rewrite pair_add_comm, pair_add_zero_left. Qed.

  Fact pair_add_one_left x y : (1+x,y) = (x,y) +ₐ (1,0).
  Proof. simpl; f_equal; lia. Qed.

  Fact pair_add_one_right x y : (x,1+y) = (x,y) +ₐ (0,1).
  Proof. simpl; f_equal; lia. Qed.

  Fact pair_add_assoc p q r : (p +ₐ q) +ₐ r = p +ₐ (q +ₐ r).
  Proof. revert p q r; intros [] [] []; simpl; f_equal; lia. Qed.

  Definition acm2_tps_lolipop (X Y : nat*nat -> Prop) v := forall x, X x -> Y (x +ₐ v).
  Definition acm2_tps_mult (X Y : nat*nat -> Prop) v := exists a b, v = a +ₐ b /\ X a /\ Y b. 
  Definition acm2_tps_with (X Y : nat*nat -> Prop) v := X v /\ Y v.

  Infix "-∘" := acm2_tps_lolipop (at level 65, right associativity).
  Infix "∘" := acm2_tps_mult (at level 64, left associativity).
  Infix "⊓" := acm2_tps_with (at level 66, left associativity). 

  Variables (s : loc -> nat*nat -> Prop) (v : bool -> loc).

  (** Linear logic semantics for ACM2 instructions *)
  Definition acm2_sem (i : acm2_instr loc) : nat*nat -> Prop := 
    match i with
    | STOPₐ p     => s p                      (* p *)
    | FORKₐ p q r => (s q ⊓ s r) -∘ s p       (* (q & r) -* p    *)
    | DECₐ b p q  => s (v b) -∘ s q -∘ s p    (* b -* q -* p     *)
    | INCₐ b p q  => (s (v b) -∘ s q) -∘ s p  (* (b -* q) -* p   *) 
    end.

  Notation "⟦ i ⟧ᵢ" := (acm2_sem i) (at level 0).

  (** Σ = [i₁;...;iₙ] then ⟦Σ⟧ = ⟦i₁⟧ ⊓ ...⊓ ⟦iₙ⟧ ⊓ ⟦i₁⟧ ⊓ eq (0,0) *)
  Definition acm2_list_sem := fold_right (λ i c, ⟦i⟧ᵢ ⊓ c) (eq (0,0)).

  Notation "⟦ Σ ⟧𞁞" := (acm2_list_sem Σ) (at level 0).

  Notation "X ⊆ Y" := (∀m, X m -> Y m) (at level 70).

  Fact acm2_list_sem_zero Σ : ⟦Σ⟧𞁞 ⊆ eq (0,0).
  Proof.
    intro; induction Σ as [ | ? ? IH ].
    + now intros [].
    + now intros [ _ ?%IH ].
  Qed.

  Hint Resolve acm2_list_sem_zero : core.

  Fact acm2_list_sem_In i Σ : In i Σ → ⟦Σ⟧𞁞 ⊆ ⟦i⟧ᵢ ⊓ eq (0,0).
  Proof.
    induction Σ as [ | j l IHl ].
    1: now intros [].
    + intros [ <- | Hi ] m; simpl.
      * intros []; split; eauto.
      * specialize (IHl Hi). 
        intros []; split; eauto; now apply IHl.
  Qed.

  Variables (Σ : list (acm2_instr loc)).

  Theorem acm2_tps_sound x y u : 
      (∀m, s (v α) m ↔ (1,0) = m)
    → (∀m, s (v β) m ↔ (0,1) = m)
    → Σ ⫽ₐ x ⊕ y ⊦ u
    → ⟦Σ⟧𞁞 ∘ (eq (x,y)) ⊆ s u.
  Proof.
    intros Hα Hβ.
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
      intros m Hm%Hα; subst m; simpl.
      apply IHq.
      exists (0,0), (1+x,y); auto.
    + rewrite pair_add_comm; apply H1.
      intros m Hm%Hβ; subst m; simpl.
      apply IHq.
      exists (0,0), (x,1+y); auto.
    + rewrite pair_add_comm, pair_add_one_left, pair_add_assoc.
      apply H1.
      * now rewrite Hα.
      * apply IHq.
        exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
    + rewrite pair_add_comm, pair_add_one_right, pair_add_assoc.
      apply H1.
      * now rewrite Hβ.
      * apply IHq.
        exists (0,0), (x,y); rewrite pair_add_zero_left; auto.
  Qed.

End ACM2_utils.

Section ndMM2_ACM2.

  Variables loc : Set.

  Notation "Σ ⫽ₙ x ⊕ y ⊦ p" := (@ndmm2_accept loc Σ x y p) (at level 70).

  Local Definition loc' := (loc + bool)%type.

  (* ZEROₙ α p q ->> FORKₐ p α q ; DECₐ β α α ; STOPₐ α *)

  Local Definition base : list (acm2_instr loc') := [ DECₐ β (inr α) (inr α) ; STOPₐ (inr α);
                                                      DECₐ α (inr β) (inr β) ; STOPₐ (inr β) ].

  Definition ndmm2_to_acm2 (i : ndmm2_instr loc) : acm2_instr loc' :=
    match i with
    | STOPₙ p     => STOPₐ (inl p)
    | INCₙ b p q  => INCₐ b (inl p) (inl q) 
    | DECₙ b p q  => DECₐ b (inl p) (inl q)
    | ZEROₙ b p q => FORKₐ (inl p) (inr b) (inl q)
    end.

  Fact ndmm2_to_acm2_In_map Σ i : In i Σ → In (ndmm2_to_acm2 i) (base ++ map ndmm2_to_acm2 Σ).
  Proof. intros; apply in_or_app; right; now apply in_map. Qed.

  Fact ndmm2_to_acm2_In_base Σ i : In i base → In i (base ++ map ndmm2_to_acm2 Σ).
  Proof. intros; now apply in_or_app; left. Qed.

  Hint Constructors acm2_accept : core.
  Hint Resolve ndmm2_to_acm2_In_map ndmm2_to_acm2_In_base : core.

  Theorem ndmm2_to_acm2_sound Σ x y p :
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
      induction y as [ | y IHy ].
      * constructor 1; apply ndmm2_to_acm2_In_base; simpl; eauto.
      * constructor 6 with (inr α); auto.
        apply ndmm2_to_acm2_In_base; simpl; eauto.
    + constructor 2 with (inr β) (inl q); eauto.
      clear H IH.
      induction x as [ | x IHy ].
      * constructor 1; apply ndmm2_to_acm2_In_base; simpl; eauto.
      * constructor 5 with (inr β); auto.
        apply ndmm2_to_acm2_In_base; simpl; eauto.
  Qed.

End ndMM2_ACM2.
