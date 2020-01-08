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

Local Notation ø := vec_nil.

Section fot_word_var.

  Variable (X : Type).

  Implicit Type t : fo_term (fun _ : X => 1).

  Fixpoint fot_var t :=
    match t with
      | in_var i   => i
      | in_fot s v => fot_var (vec_pos v pos0)
    end.

  Fixpoint fot_word t :=
    match t with
      | in_var i   => nil
      | in_fot s v => s::fot_word (vec_pos v pos0)
    end.

(*  Fact fot_word_map σ t : fot_word (fo_term_map σ t) = fot_word t. 
  Proof.
    induction t as [ i | s v IHv ]; simpl; f_equal.
    rewrite vec_pos_map; auto.
  Qed. *)

  Fixpoint fot_word_var w i : fo_term (fun _ : X => 1) :=
    match w with
      | nil  => in_var i
      | s::w => in_fot s (fot_word_var w i##ø)
    end.

  Fact fot_word_var_eq t : t = fot_word_var (fot_word t) (fot_var t).
  Proof.
    induction t as [ | s v IH ]; simpl in *; auto; f_equal.
    generalize (IH pos0); clear IH; vec split v with t; vec nil v; clear v; simpl.
    intro; f_equal; auto.
  Qed.

  Fact fot_word_eq w i : fot_word (fot_word_var w i) = w.
  Proof. induction w; simpl; f_equal; auto. Qed.

  Fact fot_var_eq w i : fot_var (fot_word_var w i) = i.
  Proof. induction w; simpl; f_equal; auto. Qed.

End fot_word_var.

Section ΣF1P1_term.

  Variable (X Y : Type).

  Definition ΣF1P1 : fo_signature.
  Proof.
    exists X Y; intros _.
    + exact 1.
    + exact 1.
  Defined.

  Implicit Type t : fo_term (ar_syms ΣF1P1).

  Fact fot_word_map σ t : 
    fot_word (fo_term_map σ t) = fot_word t. 
  Proof.
    induction t as [ i | s v IHv ]; simpl; f_equal.
    rewrite vec_pos_map; auto.
  Qed.

  Fixpoint ΣF1P1_words (A : fol_form ΣF1P1) : list (list X) :=
    match A with 
      | ⊥              => nil
      | fol_atom r v   => (fot_word (vec_pos v pos0))::nil
      | fol_bin _ A B  => ΣF1P1_words A++ΣF1P1_words B
      | fol_quant _ A  => ΣF1P1_words A
    end.

End ΣF1P1_term.

Section Σfull_mon_rem.

  Variable (m n : nat).

  Notation Σ := (ΣF1P1 (pos n) (pos m)).
  Notation Σ' := (ΣF1P1 (pos n) (pos (S m))).

  Variable (r : pos m) (s : pos n) (w : list (pos n)).

  Check list_eq_dec.

  Fixpoint Σfull_mon_rec (A : fol_form Σ) : fol_form Σ' :=
    match A with
      | ⊥              => ⊥
      | fol_atom r' v  => 
      match pos_eq_dec r r' with
        | left E  => 
        match list_eq_dec (@pos_eq_dec n) (fot_word (vec_head v)) (s::w) with
          | left  _ => @fol_atom Σ' pos0 (fot_word_var w (fot_var (vec_head v))##ø)
          | right _ => @fol_atom Σ' (pos_nxt r') v
        end
        | right _ => @fol_atom Σ' (pos_nxt r') v
      end
      | fol_bin b A B => fol_bin b (Σfull_mon_rec A) (Σfull_mon_rec B)
      | fol_quant q A => fol_quant q (Σfull_mon_rec A)
    end.

  Fact Σfull_mon_rec_words_1 A : incl (ΣF1P1_words (Σfull_mon_rec A)) 
                                      (w :: ΣF1P1_words A).
  Proof.
    induction A as [ | r' v | b A HA B HB | q A HA ].
    + simpl; intros ? [].
    + simpl; destruct (pos_eq_dec r r') as [ <- | H1 ].
      2: { simpl; intros ? [ [] | [] ]; right; simpl; auto. }
      simpl in v |- *.
      destruct (list_eq_dec (@pos_eq_dec n) (fot_word (vec_head v)) (s::w))
        as [ H2 | H2 ].
      * revert H2; vec split v with q; vec nil v; clear v; simpl; intros ->.
        simpl; rewrite (fot_word_eq w (fot_var q)).
        simpl; intros ? [ <- | [] ]; left; auto.
      * simpl; intros ? [ [] | [] ]; right; simpl; auto.
    + simpl; intros x; simpl; rewrite !in_app_iff.
      intros [ H | H ]; [ apply HA in H | apply HB in H ]; revert H; simpl; tauto.
    + simpl; intros x Hx; apply HA in Hx; auto.
  Qed.

  Variable (A : fol_form Σ).

  Definition Σfull_mon_red : fol_form Σ' := 
        Σfull_mon_rec A 
      ⟑ ∀ @fol_atom Σ' (pos_nxt r) (@in_fot _ (ar_syms Σ') s (£0##ø)##ø)
        ↔ @fol_atom Σ' pos0 (£0##ø).

  Section soundness.

    Variable (X : Type) (M : fo_model Σ X).

    Let M' : fo_model Σ' X.
    Proof.
      split.
      + exact (fom_syms M).
      + intros r'; simpl in r' |- *.
        invert pos r'.
        * exact (fun v => fom_rels M r (fom_syms M s v##ø)).
        * exact (fom_rels M r').
    Defined.

    Fact Σfull_mon_rec_sound φ : 
      fol_sem M' φ (Σfull_mon_rec A) <-> fol_sem M φ A.
    Proof.
      revert φ; induction A as [ | r' v | b B HB C HC | q B HB ]; intros φ.
      + simpl; tauto.
      + simpl; destruct (pos_eq_dec r r') as [ <- | H1 ].
        2: { simpl; apply fol_equiv_ext; auto. }
        simpl in v |- *.
        destruct (list_eq_dec (@pos_eq_dec n) (fot_word (vec_head v)) (s::w))
          as [ H2 | H2 ].
        * simpl; revert H2; vec split v with q; vec nil v; clear v; simpl; intros H2. 
          simpl; apply fol_equiv_ext; do 2 f_equal.
          rewrite (fot_word_var_eq q) at 2.
          rewrite H2; simpl; auto.
        * simpl; apply fol_equiv_ext; auto.
      + apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; apply HB.
    Qed.

    Variable (t : fo_term (ar_syms Σ))
             (Xfin : finite_t X)
             (Mdec : fo_model_dec M)
             (φ : nat -> X)
             (HA : fol_sem M φ A).

    Theorem Σfull_mon_rem_sound : fo_form_fin_dec_SAT_in Σfull_mon_red X.
    Proof.
      exists M', Xfin.
      exists.
      { intros r'; simpl in r'; invert pos r'; intros v; apply Mdec. }
      exists φ; simpl; split.
      + apply Σfull_mon_rec_sound; auto.
      + intro; auto.
    Qed.

  End soundness.

  Section completeness.

    Variable (X : Type) (M' : fo_model Σ' X).

    Let M : fo_model Σ X.
    Proof.
      split.
      + exact (fom_syms M').
      + exact (fun r' => fom_rels M' (pos_nxt r')).
    Defined.

    Section Σfull_mon_rec_complete.

      Hypothesis HM' : forall x, fom_rels M' pos0 (x##ø)
                             <-> fom_rels M' (pos_nxt r) (fom_syms M s (x##ø)##ø).

      Fact Σfull_mon_rec_complete φ : 
        fol_sem M' φ (Σfull_mon_rec A) <-> fol_sem M φ A.
      Proof.
        revert φ; induction A as [ | r' v | b B HB C HC | q B HB ]; intros φ.
        + simpl; tauto.
        + simpl; destruct (pos_eq_dec r r') as [ <- | H1 ].
          2: { simpl; apply fol_equiv_ext; auto. }
          simpl in v |- *.
          destruct (list_eq_dec (@pos_eq_dec n) (fot_word (vec_head v)) (s::w))
            as [ H2 | H2 ].
          * simpl; revert H2; vec split v with q; vec nil v; clear v; simpl; intros H2.
            rewrite HM'. 
            simpl; apply fol_equiv_ext; do 2 f_equal.
            rewrite (fot_word_var_eq q) at 2.
            rewrite H2; simpl; auto.
          * simpl; apply fol_equiv_ext; auto.
        + apply fol_bin_sem_ext; auto.
        + simpl; apply fol_quant_sem_ext; intro; apply HB.
      Qed.

    End Σfull_mon_rec_complete.

    Variable (Xfin : finite_t X)
             (M'dec : fo_model_dec M')
             (φ : nat -> X)
             (HA : fol_sem M' φ Σfull_mon_red).

    Theorem Σfull_mon_rem_complete : fo_form_fin_dec_SAT_in A X.
    Proof.
      exists M, Xfin.
      exists.
      { intros r'; simpl in r'; intros v; apply M'dec. }
      exists φ; simpl.
      destruct HA as [ H1 H2 ].
      revert H1; apply Σfull_mon_rec_complete.
      intros; simpl in H2; split; apply H2.
    Qed.

  End completeness.

  Theorem Σfull_mon_rem_correct X :
    fo_form_fin_dec_SAT_in A X <-> fo_form_fin_dec_SAT_in Σfull_mon_red X.
  Proof.
    split.
    + intros (M & H1 & H2 & phi & H3).
      apply Σfull_mon_rem_sound with M phi; auto.
    + intros (M' & H1 & H2 & phi & H3).
      apply Σfull_mon_rem_complete with M' phi; auto.
  Qed.

End Σfull_mon_rem.

Check Σfull_mon_rem_correct.
 

          

  


  
  




  
