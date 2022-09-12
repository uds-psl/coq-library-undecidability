(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat.

Import fol_notations.

Set Implicit Arguments.

(* * From Σ=(ø;{R^n}) to any signature *)

Tactic Notation "iff" "equal" := apply fol_equiv_ext.

Local Notation ø := vec_nil.

Section Sig_n_Sig.

  Variable (Σ : fo_signature) (r : rels Σ).

  Notation Σn := (Σrel (ar_rels _ r)).

  Local Fixpoint enc (A : fol_form Σn) : fol_form Σ :=
    match A with
      | ⊥              => ⊥
      | fol_atom   _ v => fol_atom r (vec_map (fun x => £(Σrel_var x)) v)
      | fol_bin b A B  => fol_bin b (enc A) (enc B)
      | fol_quant q A  => fol_quant q (enc A)
     end.

  Section M_enc_n.

    Variables (X : Type) (M : fo_model Σ X).

    Local Definition M_enc_n : fo_model Σn X.
    Proof.
      exists; intros [] v.
      exact (fom_rels M r v).
    Defined.

    Notation "⟪ A ⟫" := (fun ψ => fol_sem M ψ A).
    Notation "⟪ A ⟫'" := (fun φ => fol_sem M_enc_n φ A) (at level 1, format "⟪ A ⟫'").

    Local Fact enc_correct_1 A φ : ⟪ A ⟫' φ <-> ⟪ enc A ⟫ φ.
    Proof.
      revert φ.
      induction A as [ | [] v | b A HA B HB | q A HA ]; intros phi.
      + simpl; tauto.
      + unfold M_enc_n; simpl; rewrite vec_map_map.
        iff equal; f_equal; apply vec_pos_ext.
        intros p; do 2 rewrite vec_pos_map; rew fot.
        simpl in v; generalize (vec_pos v p); intros [ i | [] ].
        rew fot; simpl; auto.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

  End M_enc_n.

  Local Lemma SAT_SATn A : fo_form_fin_dec_SAT (enc A)
                        -> fo_form_fin_dec_SAT A.
  Proof.
    intros (X & M & H1 & H2 & phi & H3).
    exists X, (M_enc_n M), H1.
    exists. { intros [] v; apply H2. }
    exists phi.
    revert H3; apply enc_correct_1.
  Qed.

  Section Mn_enc.

    Variables (X : Type) (Mn : fo_model Σn X) (x0 : X).

    Local Definition Mn_enc : fo_model Σ X.
    Proof.
      exists.
      + intros s v; apply x0.
      + intros r' v.
        destruct (eq_nat_dec (ar_rels _ r) (ar_rels _ r')) as [ H | H ].
        * exact (fom_rels Mn tt (eq_rect_r _ v H)).
        * exact False.
    Defined. 

    Notation "⟪ A ⟫" := (fun ψ => fol_sem Mn_enc ψ A).
    Notation "⟪ A ⟫'" := (fun φ => fol_sem Mn φ A) (at level 1, format "⟪ A ⟫'").

    Local Fact enc_correct_2 A φ : ⟪ A ⟫' φ <-> ⟪ enc A ⟫ φ.
    Proof.
      revert φ.
      induction A as [ | [] v | b A HA B HB | q A HA ]; intros phi.
      + simpl; tauto.
      + unfold Mn_enc; simpl; rewrite vec_map_map.
        destruct (eq_nat_dec (ar_rels Σ r) (ar_rels Σ r)) as [ H | [] ]; auto.
        rewrite eq_nat_uniq with (H := H); unfold eq_rect_r; simpl.
        iff equal; f_equal; apply vec_pos_ext.
        intros p; do 2 rewrite vec_pos_map; rew fot.
        simpl in v; generalize (vec_pos v p); intros [ i | [] ].
        rew fot; simpl; auto.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

  End Mn_enc.

  Local Lemma SATn_SAT A : fo_form_fin_dec_SAT A
                        -> fo_form_fin_dec_SAT (enc A).
  Proof.
    intros (X & Mn & H1 & H2 & phi & H3).
    exists X, (Mn_enc Mn (phi 0)), H1.
    exists. 
    { intros r' v; simpl.
      destruct (eq_nat_dec (ar_rels Σ r) (ar_rels Σ r')) as [ H | H ].
      + revert v; rewrite <- H; unfold eq_rect_r; simpl; intro; apply H2.
      + right; tauto. }
    exists phi.
    revert H3; apply enc_correct_2.
  Qed.

  Hint Resolve SATn_SAT SAT_SATn : core.

  Local Theorem SATn_SAT_red : 
       { f : fol_form Σn -> fol_form Σ 
           | forall A, fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT (f A) }.
  Proof. exists enc; split; auto. Qed.

End Sig_n_Sig.
   
Theorem SATn_SAT_reduction (Σ : fo_signature) (n : nat) (r : rels Σ) (Hr : ar_rels _ r = n) :
      { f : fol_form (Σrel n) -> fol_form Σ 
          | forall A, fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT (f A) }.
Proof. subst n; apply SATn_SAT_red. Qed.



  
