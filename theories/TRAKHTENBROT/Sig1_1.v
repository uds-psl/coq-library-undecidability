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

Section ΣF1P1_term.

  Variable (X Y : Type).

  Definition ΣF1P1 : fo_signature.
  Proof.
    exists X Y; intros _.
    + exact 1.
    + exact 1.
  Defined.

  Fixpoint ΣF1P1_word (t : fo_term (ar_syms ΣF1P1)) :=
    match t with
      | in_var i   => nil
      | in_fot s v => s::ΣF1P1_word (vec_pos v pos0)
    end.

  Fact ΣF1P1_word_map σ t : 
    ΣF1P1_word (fo_term_map σ t) = ΣF1P1_word t. 
  Proof.
    induction t as [ i | s v IHv ]; simpl; f_equal.
    rewrite vec_pos_map; auto.
  Qed.

  Fixpoint ΣF1P1_words (A : fol_form ΣF1P1) : list (list X) :=
    match A with 
      | ⊥              => nil
      | fol_atom r v   => (ΣF1P1_word (vec_pos v pos0))::nil
      | fol_bin _ A B  => ΣF1P1_words A++ΣF1P1_words B
      | fol_quant _ A  => ΣF1P1_words A
    end.

End ΣF1P1_term.

Section Σfull_mon_rem.

  Variable (n m : nat).

  Notation Σ := (ΣF1P1 (pos n) (pos m)).
  Notation Σ' := (ΣF1P1 (pos n) (pos (S m))).

  Variable (s : pos n) (r : pos m).

  Fixpoint Σfull_mon_rec (t : fo_term (ar_syms Σ)) (A : fol_form Σ) : fol_form Σ' :=
    match A with
      | ⊥              => ⊥
      | fol_atom r' v  => 
      match pos_eq_dec r r' with
        | left E  => 
        match eq_fo_term_dec (@pos_eq_dec n) (vec_head v) (@in_fot _ _ s (t##ø)) with
          | left  _ => @fol_atom Σ' pos0 (t##ø)
          | right _ => @fol_atom Σ' (pos_nxt r') v
        end
        | right _ => @fol_atom Σ' (pos_nxt r') v
      end
      | fol_bin b A B => fol_bin b (Σfull_mon_rec t A) (Σfull_mon_rec t B)
      | fol_quant q A => fol_quant q (Σfull_mon_rec (fo_term_map S t) A)
    end.

  Fact Σfull_mon_rec_words_1 t A : incl (ΣF1P1_words (Σfull_mon_rec t A)) 
                                        (ΣF1P1_word t :: ΣF1P1_words A).
  Proof.
    revert t; induction A as [ | r' v | b A HA B HB | q A HA ]; intros t.
    + simpl; intros ? [].
    + simpl; destruct (pos_eq_dec r r') as [ <- | H1 ].
      2: { simpl; intros ? [ [] | [] ]; right; simpl; auto. }
      simpl in v, t |- *.
      destruct (eq_fo_term_dec (@pos_eq_dec n) (vec_head v) (in_fot s (t##ø)))
        as [ H2 | H2 ].
      * revert H2; vec split v with q; vec nil v; clear v; simpl; intros ->.
        simpl; intros ? [ <- | [] ]; left; auto.
      * simpl; intros ? [ [] | [] ]; right; simpl; auto.
    + simpl; intros x; simpl; rewrite !in_app_iff.
      intros [ H | H ]; [ apply HA in H | apply HB in H ]; revert H; simpl; tauto.
    + simpl; intros x Hx.
      apply HA in Hx.
      simpl in Hx |- *.
      rewrite ΣF1P1_word_map in Hx; auto.
  Qed.

  Let ws t := ΣF1P1_word (Y := pos m) (in_fot s (t##ø)).

  (* If s[t] is a maximal word then ... 
     What diminishes ???
   *)

  Definition Σfull_mon_red t A : fol_form Σ' := 
        Σfull_mon_rec t A 
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

    Fact Σfull_mon_rec_sound t A φ : 
      fol_sem M' φ (Σfull_mon_rec t A) <-> fol_sem M φ A.
    Proof.
      revert t φ; induction A as [ | r' v | b A HA B HB | q A HA ]; intros t φ.
      + simpl; tauto.
      + simpl; destruct (pos_eq_dec r r') as [ <- | H1 ].
        2: { simpl; apply fol_equiv_ext; auto. }
        simpl in v, t |- *.
        destruct (eq_fo_term_dec (@pos_eq_dec n) (vec_head v) (in_fot s (t##ø)))
          as [ H2 | H2 ].
        * simpl; revert H2; vec split v with q; vec nil v; clear v; simpl; intros ->. 
          simpl; apply fol_equiv_ext; auto.
        * simpl; apply fol_equiv_ext; auto.
      + apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; apply HA.
    Qed.

    Variable (t : fo_term (ar_syms Σ))
             (Xfin : finite_t X)
             (Mdec : fo_model_dec M)
             (φ : nat -> X)
             (A : fol_form Σ)
             (HA : fol_sem M φ A).

    Theorem Σfull_mon_rem_sound : fo_form_fin_dec_SAT_in (Σfull_mon_red t A) X.
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

      Fact Σfull_mon_rec_complete t A φ : 
        fol_sem M' φ (Σfull_mon_rec t A) <-> fol_sem M φ A.
      Proof.
        revert t φ; induction A as [ | r' v | b A HA B HB | q A HA ]; intros t φ.
        + simpl; tauto.
        + simpl; destruct (pos_eq_dec r r') as [ <- | H1 ].
          2: { simpl; apply fol_equiv_ext; auto. }
          simpl in v, t |- *.
          destruct (eq_fo_term_dec (@pos_eq_dec n) (vec_head v) (in_fot s (t##ø)))
            as [ H2 | H2 ].
          * simpl; revert H2; vec split v with q; vec nil v; clear v; simpl; intros ->.
            rewrite HM'. 
            simpl; apply fol_equiv_ext; auto.
          * simpl; apply fol_equiv_ext; auto.
        + apply fol_bin_sem_ext; auto.
        + simpl; apply fol_quant_sem_ext; intro; apply HA.
      Qed.

    End Σfull_mon_rec_complete.

    Variable (t : fo_term (ar_syms Σ))
             (Xfin : finite_t X)
             (M'dec : fo_model_dec M')
             (φ : nat -> X)
             (A : fol_form Σ)
             (HA : fol_sem M' φ (Σfull_mon_red t A)).

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

  Variable (X : Type).

  Theorem Σfull_mon_rem_correct t A :
    fo_form_fin_dec_SAT_in A X <-> fo_form_fin_dec_SAT_in (Σfull_mon_red t A) X.
  Proof.
    split.
    + intros (M & H1 & H2 & phi & H3).
      apply Σfull_mon_rem_sound with M phi; auto.
    + intros (M' & H1 & H2 & phi & H3).
      apply Σfull_mon_rem_complete with M' t phi; auto.
  Qed.

End Σfull_mon_rem.

Check Σfull_mon_rem_correct.
 

          

  


  
  




  
