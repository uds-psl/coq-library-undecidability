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

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat Sig2_SigSSn1.

Import fol_notations.

Set Implicit Arguments.

(* * Expanding from Σ=({f^n};{P^1}) to any signature *)

Tactic Notation "iff" "equal" := apply fol_equiv_ext.

Local Notation ø := vec_nil.

Section Sig_n1_Sig.

  Variable (n : nat) (Σ' : fo_signature) (f : syms Σ') (p : rels Σ').

  Notation Σ := (Σn1 n).

  Hypothesis (Hf : ar_syms _ f = n).
  Hypothesis (Hp : ar_rels _ p = 1).

  Let Fixpoint convert_t (t : fo_term (ar_syms Σ)) : fo_term (ar_syms Σ').
  Proof.
    refine (match t with
      | in_var i   => in_var i
      | in_fot s v => @in_fot _ (ar_syms Σ') f (vec_map convert_t (cast v _))
    end); now simpl.
  Defined.

  Fixpoint Σn1_Σ (A : fol_form Σ) : fol_form Σ'.
  Proof using Hf Hp.
    refine (match A with
      | ⊥              => ⊥
      | fol_atom   _ v => fol_atom p (vec_map convert_t (cast v _))
      | fol_bin b A B  => fol_bin b (Σn1_Σ A) (Σn1_Σ B)
      | fol_quant q A  => fol_quant q (Σn1_Σ A)
     end); now simpl.
  Defined.

  Notation convert := Σn1_Σ.

  Section soundness.

    Variables (X : Type) (M : fo_model Σ X) (phi : nat -> X).

    Let M' : fo_model Σ' X.
    Proof.
      split.
      + intros s.
        destruct (eq_nat_dec (ar_syms _ s) n) as [ E | D ].
        * intros v; apply (fom_syms M tt); revert v; rewrite E; trivial.
        * intros; apply (phi 0).
      + intros r.
        destruct (eq_nat_dec (ar_rels _ r) 1) as [ E | D ].
        * intros v; apply (fom_rels M tt); revert v; rewrite E; trivial.
        * intros; exact True.
    Defined.

    Let convert_t_sound t φ : fo_term_sem M φ t = fo_term_sem M' φ (convert_t t).
    Proof.
      induction t as [ i | [] v IH ]; simpl; auto.
      destruct (eq_nat_dec (ar_syms Σ' f) n) as [ H | [] ]; auto.
      rewrite vec_map_map; generalize H Hf; intros -> H'.
      unfold eq_rect_r; simpl; f_equal.
      apply vec_pos_ext; intros j; rewrite !vec_pos_map.
      rewrite IH; repeat f_equal.
      rewrite (eq_nat_pirr H' eq_refl); auto.
    Qed.

    Let convert_sound A φ : fol_sem M φ A <-> fol_sem M' φ (convert A).
    Proof.
      revert φ.
      induction A as [ | [] v | b A HA B HB | q A HA ]; intros φ.
      + simpl; tauto.
      + simpl.
        destruct (eq_nat_dec (ar_rels Σ' p) 1) as [ H | [] ]; auto.
        generalize H Hp; intros -> H'.
        unfold eq_rect_r; simpl; f_equal.
        rewrite (eq_nat_pirr H' eq_refl); simpl.
        rewrite !vec_map_map.
        apply fol_equiv_ext; f_equal.
        apply vec_pos_ext; intros j; rewrite !vec_pos_map; auto.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

    Hypothesis (Xfin : finite_t X)
               (Mdec : fo_model_dec M)
               (A : fol_form Σ)
               (HA : fol_sem M phi A).

    Local Fact convert_soundness : fo_form_fin_dec_SAT (convert A).
    Proof using Xfin Mdec HA.
      exists X, M', Xfin.
      exists.
      { intros r v; simpl in *.
        destruct (eq_nat_dec (ar_rels Σ' r) 1); try tauto; apply Mdec. }
      exists phi; apply convert_sound; auto.
    Qed.
        
  End soundness.

  Section completeness.

    Variables (X : Type) (M' : fo_model Σ' X).

    Let M : fo_model Σ X.
    Proof.
      split.
      + intros []; simpl; intros v.
        apply (fom_syms M' f); rewrite Hf; trivial.
      + intros []; simpl; intros v.
        apply (fom_rels M' p); rewrite Hp; trivial.
    Defined.
 
    Let convert_t_complete t φ : fo_term_sem M φ t = fo_term_sem M' φ (convert_t t).
    Proof.
      induction t as [ i | [] v IH ]; simpl; auto.
      f_equal; generalize Hf; intros ->.
      unfold eq_rect_r; simpl; f_equal.
      apply vec_pos_ext; intros j; rewrite !vec_pos_map.
      rewrite IH; repeat f_equal.
    Qed.

    Let convert_complete A φ : fol_sem M φ A <-> fol_sem M' φ (convert A).
    Proof.
      revert φ.
      induction A as [ | [] v | b A HA B HB | q A HA ]; intros φ.
      + simpl; tauto.
      + simpl.
        apply fol_equiv_ext; f_equal; generalize Hp; intros ->.
        unfold eq_rect_r; simpl; f_equal.
        apply vec_pos_ext; intros j; rewrite !vec_pos_map; auto.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

    Hypothesis (Xfin : finite_t X)
               (M'dec : fo_model_dec M')
               (phi : nat -> X)
               (A : fol_form Σ)
               (HA : fol_sem M' phi (convert A)).

    Local Fact convert_completeness : fo_form_fin_dec_SAT A.
    Proof using Xfin M'dec HA.
      exists X, M, Xfin.
      exists.
      { intros [] v; apply M'dec. }
      exists phi; apply convert_complete; auto.
    Qed.

  End completeness.

  Theorem Σn1_Σ_correct A : 
              fo_form_fin_dec_SAT A
          <-> fo_form_fin_dec_SAT (Σn1_Σ A).
  Proof.
    split.
    + intros (X & M & H1 & H2 & phi & H3).
      apply convert_soundness with X M phi; auto.
    + intros (X & M & H1 & H2 & phi & H3).
      apply convert_completeness with X M phi; auto.
  Qed.
 
End Sig_n1_Sig.

