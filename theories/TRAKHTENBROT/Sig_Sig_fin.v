(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec Max.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Section discrete_to_finite_fix.

  Variables (Σ : fo_signature)
            (HΣ1 : discrete (syms Σ))
            (HΣ2 : discrete (rels Σ))

            (ls : list (syms Σ))
            (lr : list (rels Σ)).

  Let Fn s := (if in_dec HΣ1 s ls then true else false) = true.
  Let Re r := (if in_dec HΣ2 r lr then true else false) = true.

  Let HFn s : Fn s <-> In s ls.
  Proof.
    unfold Fn; destruct (in_dec HΣ1 s ls); split; try tauto; discriminate.
  Qed.
 
  Let HRe r : Re r <-> In r lr.
  Proof.
    unfold Re; destruct (in_dec HΣ2 r lr); split; try tauto; discriminate.
  Qed.

  Definition Σ_fin : fo_signature.
  Proof.
    exists (sig Fn) (sig Re).
    + exact (fun s => ar_syms _ (proj1_sig s)).
    + exact (fun r => ar_rels _ (proj1_sig r)).
  Defined.

  Notation Σ' := Σ_fin.

  Fact Σ_fin_discrete_syms : discrete (syms Σ').
  Proof.
    intros (s1 & H1) (s2 & H2).
    destruct (HΣ1 s1 s2) as [ | C ].
    + left; subst; f_equal; apply eq_bool_pirr.
    + right; contradict C; injection C; auto.
  Qed.

  Fact Σ_fin_discrete_rels : discrete (rels Σ').
  Proof.
    intros (r1 & H1) (r2 & H2).
    destruct (HΣ2 r1 r2) as [ | C ].
    + left; subst; f_equal; apply eq_bool_pirr.
    + right; contradict C; injection C; auto.
  Qed.

  Fact Σ_fin_finite_syms : finite_t (syms Σ').
  Proof.
    set (f s Hs := exist Fn s (proj2 (HFn s) Hs)).
    exists (list_in_map ls f).
    intros (s & Hs).
    replace (exist Fn s Hs) with (f s (proj1 (HFn s) Hs)).
    + apply In_list_in_map.
    + unfold f; f_equal; apply eq_bool_pirr.
  Qed. 

  Fact Σ_fin_finite_rels : finite_t (rels Σ').
  Proof.
    set (f r Hr := exist Re r (proj2 (HRe r) Hr)).
    exists (list_in_map lr f).
    intros (r & Hr).
    replace (exist Re r Hr) with (f r (proj1 (HRe r) Hr)).
    + apply In_list_in_map.
    + unfold f; f_equal; apply eq_bool_pirr.
  Qed. 

  Fixpoint fo_term_fin_rev (t : fo_term (ar_syms Σ')) : fo_term (ar_syms Σ) :=
    match t with
      | in_var n   => in_var n
      | in_fot s v => in_fot (proj1_sig s) (vec_map fo_term_fin_rev v)
    end.
  
  Fixpoint Σ_finite_rev (A : fol_form Σ') : fol_form Σ :=
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => fol_atom (proj1_sig r) (vec_map fo_term_fin_rev v)
      | fol_bin b A B  => fol_bin b (Σ_finite_rev A) (Σ_finite_rev B)
      | fol_quant q A  => fol_quant q (Σ_finite_rev A)
    end.

  Section Σ_finite_rev_sem.

    Variable (X : Type) (M' : fo_model Σ' X)
             (M1' : finite_t X)
             (M2' : fo_model_dec M') (x0 : X).

    Local Definition Σ_finite_rev_model1 : fo_model Σ X.
    Proof.
      split.
      + intros s.
        destruct (in_dec HΣ1 s ls) as [ H | H ].
        * apply HFn in H.
          apply (fom_syms M' (exist _ s H)).
        * intro; exact x0.
      + intros r.
        destruct (in_dec HΣ2 r lr) as [ H | H ].
        * apply HRe in H.
          apply (fom_rels M' (exist _ r H)).
        * intro; exact True.
    Defined.

    Notation M := Σ_finite_rev_model1.

    Local Fact fo_term_fin_rev_sound t phi : fo_term_sem M' phi t = fo_term_sem M phi (fo_term_fin_rev t).
    Proof.
      induction t as [ n | (s & Hs) v IHv ]; simpl; auto.
      destruct (in_dec HΣ1 s ls) as [ H | [] ].
      2: { apply HFn; auto. }
      replace (match HFn s with | conj _ x => x end H) with Hs by apply eq_bool_pirr.
      f_equal; apply vec_pos_ext; intros p; rewrite !vec_pos_map; auto.
    Qed.

    Hint Resolve fo_term_fin_rev_sound.

    Local Fact Σ_finite_rev_sound A phi : fol_sem M' phi A <-> fol_sem M phi (Σ_finite_rev A).
    Proof.
      revert phi; induction A as [ | (r & Hr) v | b A HA B HB | q A HA ]; intros phi.
      + simpl; tauto.
      + simpl.
        destruct (in_dec HΣ2 r lr) as [ | [] ].
        2: { apply HRe; auto. }
        replace (match HRe r with | conj _ x => x end i) with Hr.
        2: apply eq_bool_pirr.
        apply fol_equiv_ext; f_equal.
        rewrite vec_map_map; apply vec_pos_ext; intros p.
        rewrite !vec_pos_map; auto.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

  End Σ_finite_rev_sem.

  Section Σ_finite_rev_sem'.

    Variable (X : Type) (M : fo_model Σ X)
             (M1 : finite_t X)
             (M2 : fo_model_dec M).

    Local Definition Σ_finite_rev_model2 : fo_model Σ' X.
    Proof.
      split.
      + intros (s & ?); apply (fom_syms M s).
      + intros (r & ?); apply (fom_rels M r).
    Defined.

    Notation M' := Σ_finite_rev_model2.

    Local Fact fo_term_fin_rev_complete t phi : fo_term_sem M' phi t = fo_term_sem M phi (fo_term_fin_rev t).
    Proof.
      induction t as [ n | (s & Hs) v IHv ]; simpl; auto.
      rewrite vec_map_map; f_equal; apply vec_pos_ext.
      intros p; rewrite !vec_pos_map; auto.
    Qed.

    Hint Resolve fo_term_fin_rev_complete.

    Local Fact Σ_finite_rev_complete A phi : fol_sem M' phi A <-> fol_sem M phi (Σ_finite_rev A).
    Proof.
      revert phi; induction A as [ | (r & Hr) v | b A HA B HB | q A HA ]; intros phi.
      + simpl; tauto.
      + simpl.
        apply fol_equiv_ext; f_equal.
        rewrite vec_map_map; apply vec_pos_ext; intros p.
        rewrite !vec_pos_map; auto.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

  End Σ_finite_rev_sem'.

  Fact Σ_finite_rev_correct A : fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT (Σ_finite_rev A).
  Proof.
    split.
    + intros (X & M' & H1 & H2 & phi & H3).
      exists X, (Σ_finite_rev_model1 M' (phi 0)), H1.
      exists.
      { intros r v; simpl.
        destruct (in_dec HΣ2 r lr).
        + apply H2.
        + tauto. }
      exists phi.
      apply Σ_finite_rev_sound; auto.
    + intros (X & M & H1 & H2 & phi & H3).
      exists X, (Σ_finite_rev_model2 M), H1.
      exists.
      { intros (r & Hr) v; simpl; apply H2. }
      exists phi; apply Σ_finite_rev_complete; auto.
  Qed.

  Definition fo_term_finite (t : fo_term (ar_syms Σ)) : 
              incl (fo_term_syms t) ls -> { t' | t = fo_term_fin_rev t' }.
  Proof.
    induction t as [ n | s v IHv ]; intros H.
    + exists (in_var n); simpl; auto.
    + assert (Hv : forall p, { t | vec_pos v p = fo_term_fin_rev t}).
      { intros p; apply IHv; intros x Hx; apply H; rew fot.
        right; apply in_flat_map; exists (vec_pos v p); split; auto.
        apply in_vec_list, in_vec_pos. }
      apply vec_reif_t in Hv; destruct Hv as (w & Hw).
      assert (Hs : Fn s).
      { apply HFn, H; rew fot; simpl; left; auto. }
      exists (in_fot (exist _ s Hs) w); simpl; f_equal.
      apply vec_pos_ext; intros p.
      rewrite vec_pos_map; auto.
  Qed.

  Local Fact Σ_finite_full (A : fol_form Σ) : incl (fol_syms A) ls 
                                    -> incl (fol_rels A) lr
                                    -> { B | A = Σ_finite_rev B }.
  Proof.
    induction A as [ | r v | b A HA B HB | q A HA ]; intros H1 H2.
    + exists ⊥; simpl; auto.
    + assert (Hr : Re r).
      { apply HRe, H2; simpl; auto. }
      assert (Hv : forall p, { t | vec_pos v p = fo_term_fin_rev t }).
      { intro p; apply fo_term_finite; intros s Hs; apply H1. 
        simpl; apply in_flat_map; exists (vec_pos v p); split; auto.
        apply in_vec_list, in_vec_pos. }
      apply vec_reif_t in Hv; destruct Hv as (w & Hw).
      exists (@fol_atom Σ' (exist _ r Hr) w); simpl; f_equal.
      apply vec_pos_ext; intros p; rewrite vec_pos_map; auto.
    + destruct HA as (A' & HA').
      { intros ? ?; apply H1, in_app_iff; auto. }
      { intros ? ?; apply H2, in_app_iff; auto. }
      destruct HB as (B' & HB').
      { intros ? ?; apply H1, in_app_iff; auto. }
      { intros ? ?; apply H2, in_app_iff; auto. }
      exists (fol_bin b A' B'); simpl; f_equal; auto.
    + destruct HA as (A' & HA').
      { intros ? ?; apply H1; auto. }
      { intros ? ?; apply H2; auto. }
      exists (fol_quant q A'); simpl; f_equal; auto.
  Qed.

End discrete_to_finite_fix.

Section discrete_to_finite.

  Variables (Σ : fo_signature)
            (HΣ1 : discrete (syms Σ))
            (HΣ2 : discrete (rels Σ)).

  Hint Resolve incl_refl.

  Definition Σ_finite (A : fol_form Σ) : 
              { Σ' : fo_signature & 
              { _  : finite_t (syms Σ') &
              { _  : finite_t (rels Σ') &
              { _  : discrete (syms Σ') &
              { _  : discrete (rels Σ') &
              { B  : fol_form Σ'            
              | fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT B } } } } } }.
  Proof.
    exists (Σ_fin Σ HΣ1 HΣ2 (fol_syms A) (fol_rels A)).
    exists. { apply Σ_fin_finite_syms. }
    exists. { apply Σ_fin_finite_rels. }
    exists. { apply Σ_fin_discrete_syms. }
    exists. { apply Σ_fin_discrete_rels. }
    destruct (@Σ_finite_full Σ HΣ1 HΣ2 (fol_syms A) (fol_rels A) A) as (B & HB); auto.
    exists B.
    revert B HB.
    generalize (fol_syms A) (fol_rels A); intros ls lr B ->.
    symmetry; apply  Σ_finite_rev_correct.
  Qed.

End discrete_to_finite.

Check Σ_finite.
Print Assumptions Σ_finite.