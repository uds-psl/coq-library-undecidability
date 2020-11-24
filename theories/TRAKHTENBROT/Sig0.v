(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Max.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable
                 fol_ops fo_sig fo_terms fo_logic fo_sat.

Set Implicit Arguments.

(* * Removal of function symbols from propositional signatures *)

Section Σ_Σ0.

  Variable (Σ  : fo_signature)
           (HΣ : forall r, ar_rels Σ r = 0).

  Definition Σ0 : fo_signature.
  Proof.
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
      + simpl; apply fol_equiv_ext; f_equal.
        revert v; rewrite (HΣ r); unfold eq_rect_r; simpl.
        intros v; vec nil v; auto.
      + apply fol_bin_sem_ext; auto.
      + simpl; split.
        * intros (x & Hx); exists tt; revert Hx; apply HA.
        * intros (x & Hx); exists (φ 0); revert Hx; apply HA.
      + simpl; split.
        * intros H x; generalize (H (φ 0)); apply HA.
        * intros H x; generalize (H tt); apply HA.
    Qed.

    Hypothesis (Mdec : fo_model_dec M)
               (phi : nat -> X)
               (A : fol_form Σ)
               (HA : fol_sem M phi A).

    Local Lemma Σ_Σ0_soundness : fo_form_fin_dec_SAT_in (Σ_Σ0 A) unit.
    Proof.
      exists M', finite_t_unit.
      exists. { intros r v; simpl; apply Mdec. }
      exists (fun _ => tt).
      revert HA; apply Σ_Σ0_sound.
    Qed.

  End soundness.

  Section completeness.

    Variable (M' : fo_model Σ0 unit).
  
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
        * intros (x & Hx); exists tt; revert Hx; apply HA.
        * intros (x & Hx); exists (φ 0); revert Hx; apply HA.
      + simpl; split.
        * intros H x; generalize (H (φ 0)); apply HA.
        * intros H x; generalize (H tt); apply HA.
    Qed.

    Hypothesis (M'dec : fo_model_dec M')
               (psi : nat -> unit)
               (A : fol_form Σ)
               (HA : fol_sem M' psi (Σ_Σ0 A)).

    Local Lemma Σ_Σ0_completeness : fo_form_fin_dec_SAT_in A unit.
    Proof.
      exists M, finite_t_unit.
      exists. { intros r v; simpl; apply M'dec. }
      exists (fun _ => tt).
      revert HA; apply Σ_Σ0_complete.
    Qed.

  End completeness.

  Theorem Σ_Σ0_correct A : fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT_in (Σ_Σ0 A) unit.
  Proof.
    split.
    + intros (X & M & _ & G2 & phi & G3).
      apply Σ_Σ0_soundness with X M phi; auto.
    + intros (M & _ & G2 & phi & G3).
      exists unit; apply Σ_Σ0_completeness with M phi; auto.
  Qed.

End Σ_Σ0.
