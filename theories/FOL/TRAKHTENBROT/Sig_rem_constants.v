(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat.

Import fol_notations.

Set Implicit Arguments.

(* * Removing constant functions from monadic signatures *)

Local Notation ø := vec_nil.

Section remove_constants.

  Variable (Σ : fo_signature) (HΣ : forall s, ar_syms Σ s <= 1).

  Definition Σno_constants : fo_signature.
  Proof using Σ.
    exists (syms Σ) (rels Σ).
    + exact (fun _ => 1).
    + apply ar_rels.
  Defined.

  Notation Σ' := Σno_constants.

  Implicit Type (t : fo_term (ar_syms Σ))
                (A : fol_form Σ).

  Let choice : forall a, { a = 0 } + { a = 1 } + { 1 < a }.
  Proof. intros [ | [ | a ] ]; auto; right; lia. Qed.

  Let Fixpoint fot_rem_cst (n : nat) t { struct t } : fo_term (ar_syms Σ').
  Proof.
    refine (match t with
      | in_var i   => in_var i
      | in_fot s v =>
      match choice (ar_syms _ s) with
        | inleft (left _)  => @in_fot _ (ar_syms Σ') s (£n##ø)
        | inleft (right E) => @in_fot _ (ar_syms Σ') s (fot_rem_cst n (vec_pos (cast v E) pos0)##ø)
        | inright H        => _
      end
    end).
    exfalso; abstract (generalize (HΣ s); lia).
  Defined.

  Fixpoint Σrem_constants (n : nat) A { struct A } := 
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => @fol_atom Σ' r (vec_map (fot_rem_cst n) v)
      | fol_bin b A B  => fol_bin b (Σrem_constants n A) (Σrem_constants n B)
      | fol_quant q A  => fol_quant q (Σrem_constants (S n) A)
    end.

  Variable (X : Type).

  Section soundness.

    Variable (M : fo_model Σ X).

    Let M' : fo_model Σ' X.
    Proof.
      split.
      + intros s; simpl in *.
        destruct (choice (ar_syms _ s)) as [ [ H | H ] | H ].
        * exact (fun _ => fom_syms M s (cast ø (eq_sym H))).
        * exact (fun v => fom_syms M s (cast v (eq_sym H))).
        * abstract (intros; exfalso; generalize (HΣ s); lia).
      + apply (fom_rels M).
    Defined.

    Let fot_rem_cst_sound n t φ :
            fo_term_sem M φ t = fo_term_sem M' φ (fot_rem_cst n t).
    Proof.
      induction t as [ i | s v IHv ].
      + simpl; auto.
      + simpl.
        case_eq (choice (ar_syms Σ s)); [ intros [ E | E ] | intros E ]; intros HE; 
          simpl; try rewrite HE; clear HE.
        * f_equal.
          clear n IHv; revert E v.
          intros -> v; vec nil v; auto.
        * f_equal; apply vec_pos_ext; intros p; rew vec.
          specialize (IHv p); rewrite IHv; clear IHv.
          revert E p v; intros -> p v.
          analyse pos p; rew vec.
        * exfalso; clear v IHv.
          generalize (HΣ s); lia.
    Qed.

    Local Fact Σrem_constants_sound n A φ : fol_sem M φ A <-> fol_sem M' φ (Σrem_constants n A).
    Proof.
      revert n φ; induction A as [ | r v | b A HA B HB | q A HA ]; intros n φ.
      + simpl; tauto.
      + simpl.
        rewrite vec_map_map.
        apply fol_equiv_ext; f_equal.
        apply vec_pos_ext; intros p; rew vec.
      + simpl; apply fol_bin_sem_ext; auto. 
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

    Hypothesis (Xfin : finite_t X)
               (Mdec : fo_model_dec M)
               (φ : nat -> X) 
               (A : fol_form Σ)
               (HA : fol_sem M φ A).

    Local Lemma Σrem_constants_soundness : fo_form_fin_dec_SAT_in (Σrem_constants 0 A) X.
    Proof using Xfin Mdec HA.
      exists M', Xfin, Mdec, φ.
      apply Σrem_constants_sound; auto.
    Qed.

  End soundness.

  Section completeness.

    Variable (M' : fo_model Σ' X)
             (φ : nat -> X).

    Let M : fo_model Σ X.
    Proof.
      split.
      + simpl; intros s.
        destruct (choice (ar_syms _ s)) as [ [ H | H ] | H ].
        * exact (fun _ => fom_syms M' s (φ 0##ø)).
        * exact (fun v => fom_syms M' s (cast v H)).
        * abstract (intros; exfalso; generalize (HΣ s); lia).
      + apply (fom_rels M').
    Defined.

    Let fot_rem_cst_complete n t ψ :
             ψ n = φ 0
          -> fo_term_sem M ψ t = fo_term_sem M' ψ (fot_rem_cst n t).
    Proof.
      intros H0; induction t as [ i | s v IHv ].
      + simpl; auto.
      + simpl.
        destruct (choice (ar_syms Σ s)) as [ [ E | E ] | E ].
        * simpl; now do 2 f_equal.
        * simpl fo_term_sem; f_equal.
          revert E v IHv; intros -> v IHv. 
          apply vec_pos_ext; intros p; rew vec.
          analyse pos p; simpl; rew vec.
        * exfalso; clear v IHv.
          generalize (HΣ s); lia.
    Qed.

    Local Fact Σrem_constants_complete n A ψ : 
           ψ n = φ 0
        -> fol_sem M ψ A <-> fol_sem M' ψ (Σrem_constants n A).
    Proof.
      revert n ψ; induction A as [ | r v | b A HA B HB | q A HA ]; intros n ψ H.
      + simpl; tauto.
      + simpl; apply fol_equiv_ext; f_equal; rewrite vec_map_map.
        apply vec_pos_ext; intros p; rewrite !vec_pos_map; auto.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; apply HA; simpl; auto.
    Qed.

    Hypothesis (Xfin : finite_t X)
               (M'dec : fo_model_dec M') 
               (A : fol_form Σ)
               (HA : fol_sem M' φ (Σrem_constants 0 A)).

    Local Lemma Σrem_constants_completeness : fo_form_fin_dec_SAT_in A X.
    Proof using Xfin M'dec HA.
      exists M, Xfin, M'dec, φ.
      revert HA; apply Σrem_constants_complete; auto.
    Qed.

  End completeness.

  Theorem Σrem_constants_correct A :
             fo_form_fin_dec_SAT_in A X
         <-> fo_form_fin_dec_SAT_in (Σrem_constants 0 A) X.
  Proof.
    split.
    + intros (M & H1 & H2 & phi & H3).
      apply Σrem_constants_soundness with M phi; auto.
    + intros (M & H1 & H2 & phi & H3).
      apply Σrem_constants_completeness with M phi; auto.
  Qed.

End remove_constants.
