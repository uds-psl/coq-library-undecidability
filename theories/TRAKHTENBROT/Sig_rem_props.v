(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat.

Set Implicit Arguments.

Local Reserved Notation "⟪ A ⟫'" (at level 1, format "⟪ A ⟫'").

Local Notation ø := vec_nil.

Section remove_constants.

  (** Reduction that removes propositional constants from monadic signatures *)

  Variable (Σ : fo_signature) (HΣ : forall r, ar_rels Σ r <= 1).

  Definition Σno_props : fo_signature.
  Proof.
    exists (syms Σ) (rels Σ).
    + apply ar_syms.
    + exact (fun _ => 1).
  Defined.

  Notation Σ' := Σno_props.

  Implicit Type (A : fol_form Σ).

  Let choice : forall a, { a = 0 } + { a = 1 } + { 1 < a }.
  Proof. intros [ | [ | a ] ]; auto; right; lia. Qed.

  Fixpoint Σrem_props (n : nat) A { struct A } : fol_form Σ'.
  Proof.
    refine (match A with
      | ⊥              => ⊥
      | fol_atom r v   => 
      match choice (ar_rels _ r) with
        | inleft (left _)  => @fol_atom Σ' r (£n##ø)
        | inleft (right E) => @fol_atom Σ' r (cast v E)
        | inright H        => _
      end
      | fol_bin b A B  => fol_bin b (Σrem_props n A) (Σrem_props n B)
      | fol_quant q A  => fol_quant q (Σrem_props (S n) A)
    end).
    exfalso.
    abstract (generalize (HΣ r); lia).
  Defined.

  Variable (X : Type).

  Section soundness.

    Variable (M : fo_model Σ X)
             (φ : nat -> X).

    Let M' : fo_model Σ' X.
    Proof.
      split.
      + apply (fom_syms M).
      + simpl; intros r.
        destruct (choice (ar_rels _ r)) as [ [ H | H ] | H ].
        * exact (fun _ => fom_rels M r (cast ø (eq_sym H))).
        * exact (fun v => fom_rels M r (cast v (eq_sym H))).
        * exact (fun _ => False).
    Defined.

    Local Fact Σrem_props_sound n A : fol_sem M φ A <-> fol_sem M' φ (Σrem_props n A).
    Proof.
      revert n φ; induction A as [ | r v | b A HA B HB | q A HA ]; intros n φ.
      + simpl; tauto.
      + simpl.
        case_eq (choice (ar_rels Σ r)); [ intros [ E | E ] | intros E ]; intros HE; 
          simpl; try rewrite HE.
        * apply fol_equiv_ext; f_equal.
          clear n HE; revert E v.
          intros -> v; vec nil v; auto.
        * apply fol_equiv_ext; f_equal.
          clear n HE; revert E v.
          intros -> v; auto.
        * exfalso; generalize (HΣ r); intros. 
          clear v n HE; lia.
      + simpl; apply fol_bin_sem_ext; auto. 
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

    Hypothesis (Xfin : finite_t X)
               (Mdec : fo_model_dec M) 
               (A : fol_form Σ)
               (HA : fol_sem M φ A).

    Local Lemma Σrem_props_soundness : fo_form_fin_dec_SAT_in (Σrem_props 0 A) X.
    Proof.
      exists M', Xfin.
      exists.
      { intros r; simpl; intros v; simpl in *.
        destruct (choice (ar_rels _ r)) as [ [ | ] | ];
          try apply Mdec; tauto. }
      exists φ; apply Σrem_props_sound; auto.
    Qed.

  End soundness.

  Section completeness.

    Variable (M' : fo_model Σ' X)
             (φ : nat -> X).

    Let M : fo_model Σ X.
    Proof.
      split.
      + apply (fom_syms M').
      + simpl; intros r.
        destruct (choice (ar_rels _ r)) as [ [ H | H ] | H ].
        * exact (fun _ => fom_rels M' r (φ 0##ø)).
        * exact (fun v => fom_rels M' r (cast v H)).
        * exact (fun _ => False).
    Defined.

    Local Fact Σrem_props_complete n A ψ : 
           ψ n = φ 0
        -> fol_sem M ψ A <-> fol_sem M' ψ (Σrem_props n A).
    Proof.
      revert n ψ; induction A as [ | r v | b A HA B HB | q A HA ]; intros n ψ H.
      + simpl; tauto.
      + simpl.
        destruct (choice (ar_rels Σ r)) as [ [ E | E ] | E ].
        * apply fol_equiv_ext; simpl; now do 2 f_equal.
        * apply fol_equiv_ext; f_equal.
          clear n H; revert E v.
          intros -> v; auto.
        * exfalso; generalize (HΣ r); intros. 
          clear v n H; lia.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; apply HA; simpl; auto.
    Qed.

    Hypothesis (Xfin : finite_t X)
               (M'dec : fo_model_dec M') 
               (A : fol_form Σ)
               (HA : fol_sem M' φ (Σrem_props 0 A)).

    Local Lemma Σrem_props_completeness : fo_form_fin_dec_SAT_in A X.
    Proof.
      exists M, Xfin.
      exists.
      { intros r v; simpl in *.
        destruct (choice (ar_rels _ r)) as [ [ | ] | ];
          try apply M'dec; tauto. }
      exists φ; revert HA; apply Σrem_props_complete; auto.
    Qed.

  End completeness.

  Theorem Σrem_props_correct A :
             fo_form_fin_dec_SAT_in A X
         <-> fo_form_fin_dec_SAT_in (Σrem_props 0 A) X.
  Proof.
    split.
    + intros (M & H1 & H2 & phi & H3).
      apply Σrem_props_soundness with M phi; auto.
    + intros (M & H1 & H2 & phi & H3).
      apply Σrem_props_completeness with M phi; auto.
  Qed.

End remove_constants.
