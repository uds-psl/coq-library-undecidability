(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Arith Lia Max.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations utils decidable
                 fol_ops fo_sig fo_terms fo_logic fo_sat.

Import fol_notations.

Set Implicit Arguments.

(* * Removal of function symbols from propositional signatures *)

Section Σ_Σ0.

  Variable (Σ  : fo_signature)
           (HΣ : forall r, ar_rels Σ r = 0).

  Definition Σ0 : fo_signature.
  Proof using Σ.
    exists Empty_set (rels Σ); exact (fun _ => 0).
  Defined.

  Fixpoint Σ_Σ0 (A : fol_form Σ) :=
    match A with
      |  ⊥            => ⊥
      | fol_atom r _  => @fol_atom Σ0 r vec_nil
      | fol_bin b A B => fol_bin b (Σ_Σ0 A) (Σ_Σ0 B)
      | fol_quant q A => fol_quant q (Σ_Σ0 A)
     end.

  Section soundness.

    Variable (X : Type) (M : fo_model Σ X).

    Let M' : fo_model Σ0 unit.
    Proof.
      split.
      + intros [].
      + intros r _; apply (fom_rels M r).
        rewrite HΣ; exact vec_nil.
    Defined.

    Local Fact Σ_Σ0_sound A φ ψ : fol_sem M φ A <-> fol_sem M' ψ (Σ_Σ0 A).
    Proof.
      revert φ ψ; induction A as [ | r v | b A HA B HB | [] A HA ]; intros φ ψ.
      + simpl; tauto.
      + simpl; fol equiv.
        revert v; rewrite (HΣ r); unfold eq_rect_r; simpl.
        intros v; vec nil v; auto.
      + apply fol_bin_sem_ext; auto.
      + simpl; split.
        * intros (? & H); exists tt; revert H; apply HA.
        * intros (? & H); exists (φ 0); revert H; apply HA.
      + simpl; split.
        * intros H x; generalize (H (φ 0)); apply HA.
        * intros H x; generalize (H tt); apply HA.
    Qed.

    Hypothesis (Mdec : fo_model_dec M)
               (phi : nat -> X)
               (A : fol_form Σ)
               (HA : fol_sem M phi A).

    Local Lemma Σ_Σ0_soundness : fo_form_fin_dec_SAT (Σ_Σ0 A).
    Proof using HΣ Mdec HA.
      exists unit, M', finite_t_unit.
      exists. { intros r v; simpl; apply Mdec. }
      exists (fun _ => tt).
      revert HA; apply Σ_Σ0_sound.
    Qed.

  End soundness.

  Section completeness.

    Variable (X : Type) (M' : fo_model Σ0 X).
  
    Let M : fo_model Σ unit.
    Proof.
      split.
      + intros; exact tt.
      + intros r _; apply (fom_rels M' r vec_nil).
    Defined.

    Local Fact Σ_Σ0_complete A φ ψ : fol_sem M φ A <-> fol_sem M' ψ (Σ_Σ0 A).
    Proof.
      revert φ ψ; induction A as [ | r v | b A HA B HB | [] A HA ]; intros φ ψ.
      + simpl; tauto.
      + simpl; tauto.
      + apply fol_bin_sem_ext; auto.
      + simpl; split.
        * intros (? & H); exists (ψ 0); revert H; apply HA.
        * intros (? & H); exists (φ 0); revert H; apply HA.
      + simpl; split.
        * intros H x; generalize (H (φ 0)); apply HA.
        * intros H x; generalize (H (ψ 0)); apply HA.
    Qed.

    Hypothesis (M'dec : fo_model_dec M')
               (psi : nat -> X)
               (A : fol_form Σ)
               (HA : fol_sem M' psi (Σ_Σ0 A)).

    Local Lemma Σ_Σ0_completeness : fo_form_fin_dec_SAT A.
    Proof using M'dec HA.
      exists unit, M, finite_t_unit.
      exists. { intros r v; simpl; apply M'dec. }
      exists (fun _ => tt).
      revert HA; apply Σ_Σ0_complete.
    Qed.

  End completeness.

  Theorem Σ_Σ0_correct A : fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT (Σ_Σ0 A).
  Proof using HΣ.
    split.
    + intros (X & M & _ & G2 & phi & G3).
      apply Σ_Σ0_soundness with X M phi; auto.
    + intros (X & M & _ & G2 & phi & G3).
      apply Σ_Σ0_completeness with X M phi; auto.
  Qed.

End Σ_Σ0.

Section Σ0_Σ.

  Variable (Σ  : fo_signature)
           (HΣ : forall r, ar_rels Σ r = 0).

  Fixpoint Σ0_Σ (A : fol_form (Σ0 Σ)) :=
    match A with
      |  ⊥            => ⊥
      | fol_atom r _  => @fol_atom Σ r (cast vec_nil (eq_sym (HΣ r)))
      | fol_bin b A B => fol_bin b (Σ0_Σ A) (Σ0_Σ B)
      | fol_quant q A => fol_quant q (Σ0_Σ A)
     end.

  Section soundness.

    Variable (X : Type) (M : fo_model (Σ0 Σ) X).
  
    Let M' : fo_model Σ unit.
    Proof.
      split.
      + intros; exact tt.
      + intros r _; apply (fom_rels M r vec_nil).
    Defined.

    Local Fact Σ0_Σ_sound A φ ψ : fol_sem M' ψ (Σ0_Σ A) <-> fol_sem M φ A.
    Proof.
      revert φ ψ; induction A as [ | r v | b A HA B HB | [] A HA ]; intros φ ψ.
      + simpl; tauto.
      + simpl in *; vec nil v; simpl; tauto.
      + apply fol_bin_sem_ext; auto.
      + simpl; split.
        * intros (? & H); exists (φ 0); revert H; apply HA.
        * intros (? & H); exists (ψ 0); revert H; apply HA.
      + simpl; split.
        * intros H x; generalize (H (ψ 0)); apply HA.
        * intros H x; generalize (H (φ 0)); apply HA.
    Qed.

    Hypothesis (Mdec : fo_model_dec M)
               (φ : nat -> X)
               (A : fol_form (Σ0 Σ))
               (HA : fol_sem M φ A).

    Local Lemma Σ0_Σ_soundness : fo_form_fin_dec_SAT (Σ0_Σ A).
    Proof using Mdec HA.
      exists unit, M', finite_t_unit.
      exists. { intros r v; simpl; apply Mdec. }
      exists (fun _ => tt).
      revert HA; apply Σ0_Σ_sound.
    Qed.

  End soundness.

  Section completeness.

    Variable (X : Type) (M : fo_model Σ X).

    Let M' : fo_model (Σ0 Σ) unit.
    Proof.
      split.
      + intros [].
      + intros r _; apply (fom_rels M r).
        rewrite HΣ; exact vec_nil.
    Defined.

    Local Fact Σ0_Σ_complete A φ ψ : fol_sem M ψ (Σ0_Σ A) <-> fol_sem M' φ A.
    Proof.
      revert φ ψ; induction A as [ | r v | b A HA B HB | [] A HA ]; intros φ ψ.
      + simpl; tauto.
      + simpl; fol equiv.
        revert v; rewrite (HΣ r); unfold eq_rect_r; simpl; auto.
      + apply fol_bin_sem_ext; auto.
      + simpl; split.
        * intros (? & H); exists tt; revert H; apply HA.
        * intros (? & H); exists (ψ 0); revert H; apply HA.
      + simpl; split.
        * intros H x; generalize (H (ψ 0)); apply HA.
        * intros H x; generalize (H tt); apply HA.
    Qed.

    Hypothesis (Mdec : fo_model_dec M)
               (phi : nat -> X)
               (A : fol_form (Σ0 Σ))
               (HA : fol_sem M phi (Σ0_Σ A)).

    Local Lemma Σ0_Σ_completeness : fo_form_fin_dec_SAT A.
    Proof using Mdec HA.
      exists unit, M', finite_t_unit.
      exists. { intros r v; simpl; apply Mdec. }
      exists (fun _ => tt).
      revert HA; apply Σ0_Σ_complete.
    Qed.

  End completeness.

  Theorem Σ0_Σ_correct A : fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT (Σ0_Σ A).
  Proof.
    split.
    + intros (X & M & _ & G2 & phi & G3).
      apply Σ0_Σ_soundness with X M phi; auto.
    + intros (X & M & _ & G2 & phi & G3).
      apply Σ0_Σ_completeness with X M phi; auto.
  Qed.

End Σ0_Σ.

