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

(** * Signature reduction for symbol free formulas *) 

Local Notation ø := vec_nil.

Section no_syms.

  Variable Σ : fo_signature.

  Definition Σ_empty_syms : fo_signature.
  Proof.
    exists Empty_set (rels Σ).
    + exact (fun _ => 1).
    + exact (ar_rels Σ).
  Defined.

  Notation Σ' := Σ_empty_syms.

  Implicit Types (t : fo_term (ar_syms Σ)) (A : fol_form Σ).

  Local Definition fo_term_no_sym t : incl (fo_term_syms t) nil -> nat.
  Proof.
    refine (match t with
      | in_var i   => fun _ => i
      | in_fot s _ => fun H => False_rect nat _
    end).
    apply (H s (or_introl eq_refl)).
  Defined.

  Local Fact fo_term_no_sym_pirr t H1 H2 : fo_term_no_sym t H1 = fo_term_no_sym t H2.
  Proof.
    revert t H1 H2; intros [ i | s v ] H1 H2; simpl; auto.
    destruct (H1 s).
  Qed. 

  Fixpoint Σ_no_sym (A : fol_form Σ) : incl (fol_syms A) nil -> fol_form Σ'.
  Proof.
    refine (match A with
      | ⊥              => fun _ => ⊥
      | fol_atom r v   => fun H => @fol_atom Σ' r (vec_set_pos (fun p => in_var (fo_term_no_sym (vec_pos v p) _)))
      | fol_bin b A B  => fun H => fol_bin b (Σ_no_sym A _) (Σ_no_sym B _)
      | fol_quant q A  => fun H => fol_quant q (Σ_no_sym A _)
    end).
    + intros s Hs; apply H, in_flat_map; exists (vec_pos v p); split; auto; apply in_vec_list, in_vec_pos.
    + intros ? ?; apply H, in_app_iff; simpl; auto.
    + intros ? ?; apply H, in_app_iff; simpl; auto.
    + apply H.
  Defined.

  Variable (A : fol_form Σ) (HA : incl (fol_syms A) nil).

  Section semantics.

    Variable (X : Type).

    Local Fact fo_term_no_sym_sem t Ht M φ : @fo_term_sem _ X M φ t = φ (@fo_term_no_sym t Ht).
    Proof.
      revert t Ht; intros [ i | s v ] H; simpl; auto; destruct H.
    Qed.

    Section soundness.
 
      Hypothesis (M : fo_model Σ X).

      Let M' : fo_model Σ' X.
      Proof.
        split.
        + intros [].
        + apply (fom_rels M).
      Defined.

      Local Fact Σ_no_sym_sound φ : fol_sem M φ A <-> fol_sem M' φ (Σ_no_sym A HA).
      Proof.
        revert HA φ.
        induction A as [ | r v | b B HB C HC | q B HB ]; intros H φ.
        + simpl; tauto.
        + simpl fol_sem; apply fol_equiv_ext; f_equal.
          apply vec_pos_ext; intros p; rew vec; rew fot.
          apply fo_term_no_sym_sem.
        + apply fol_bin_sem_ext; auto.
        + apply fol_quant_sem_ext; auto.
      Qed.

      Hypothesis (Xf : finite_t X)
                 (Md : fo_model_dec M)
                 (phi : nat -> X)
                 (H : fol_sem M phi A).
 
      Local Fact Σ_no_sym_soundness : fo_form_fin_dec_SAT_in (Σ_no_sym A HA) X.
      Proof.
        exists M', Xf, Md, phi.
        revert H; apply Σ_no_sym_sound.
      Qed.

    End soundness.

    Section completeness.

      Hypothesis (M' : fo_model Σ' X) (phi : nat -> X).

      Let M : fo_model Σ X.
      Proof.
       split.
        + intros _ _; exact (phi 0).
        + apply (fom_rels M').
      Defined.

      Local Fact Σ_no_sym_complete φ : fol_sem M φ A <-> fol_sem M' φ (Σ_no_sym A HA).
      Proof.
        revert HA φ.
        induction A as [ | r v | b B HB C HC | q B HB ]; intros H φ.
        + simpl; tauto.
        + simpl fol_sem; apply fol_equiv_ext; f_equal.
          apply vec_pos_ext; intros p; rew vec; rew fot.
          apply fo_term_no_sym_sem.
        + apply fol_bin_sem_ext; auto.
        + apply fol_quant_sem_ext; auto.
      Qed.

      Hypothesis (Xf : finite_t X)
                 (M'd : fo_model_dec M')
                 (H : fol_sem M' phi (Σ_no_sym A HA)).
 
      Local Fact Σ_no_sym_completeness : fo_form_fin_dec_SAT_in A X.
      Proof.
        exists M, Xf, M'd, phi.
        revert H; apply Σ_no_sym_complete.
      Qed.

    End completeness.

  End semantics.

  Theorem Σ_no_sym_correct : { B : fol_form Σ' | fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT B }.
  Proof.
    exists (Σ_no_sym A HA).
    split.
    + intros (X & M & H1 & H2 & phi & H3); exists X; apply Σ_no_sym_soundness with M phi; auto.
    + intros (X & M & H1 & H2 & phi & H3); exists X; apply Σ_no_sym_completeness with M phi; auto.
  Qed.

End no_syms.
