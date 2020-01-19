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

  Fact Σ_fin_syms : forall s : syms Σ', In (proj1_sig s) ls.
  Proof. intros (s & Hs); apply HFn, Hs. Qed.
    
  Fact Σ_fin_rels : forall r : rels Σ', In (proj1_sig r) lr.
  Proof. intros (r & Hr); apply HRe, Hr. Qed.

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

  Local Definition Σ_finite (A : fol_form Σ) : 
              { Σ' : fo_signature & 
              { _  : finite_t (syms Σ') &
              { _  : finite_t (rels Σ') &
              { _  : discrete (syms Σ') &
              { _  : discrete (rels Σ') &
              { is : syms Σ' -> syms Σ  & 
              { _  : forall s s', is s = is s' -> s = s' &
              { _  : forall s, ar_syms _ (is s) = ar_syms _ s &
              { _  : forall s, In (is s) (fol_syms A) & 
              { ir : rels Σ' -> rels Σ  & 
              { _  : forall r r', ir r = ir r' -> r = r' &
              { _  : forall r, ar_rels _ (ir r) = ar_rels _ r &
              { _  : forall r, In (ir r) (fol_rels A) & 
              { B  : fol_form Σ'            
              | fo_form_fin_dec_SAT A <-> fo_form_fin_dec_SAT B } } } } } } } } } } } } } }.
  Proof.
    exists (Σ_fin Σ HΣ1 HΣ2 (fol_syms A) (fol_rels A)).
    exists. { apply Σ_fin_finite_syms. }
    exists. { apply Σ_fin_finite_rels. }
    exists. { apply Σ_fin_discrete_syms. }
    exists. { apply Σ_fin_discrete_rels. }
    exists (@proj1_sig _ _).
    exists. { intros (? & ?) (? & ?); simpl; intros ->; f_equal; apply eq_bool_pirr. }
    exists. { intros (? & ?); reflexivity. }
    exists. { apply Σ_fin_syms. }
    exists (@proj1_sig _ _).
    exists. { intros (? & ?) (? & ?); simpl; intros ->; f_equal; apply eq_bool_pirr. }
    exists. { intros (? & ?); reflexivity. }
    exists. { apply Σ_fin_rels. } 
    destruct (@Σ_finite_full Σ HΣ1 HΣ2 (fol_syms A) (fol_rels A) A) as (B & HB); auto.
    exists B.
    revert B HB.
    generalize (fol_syms A) (fol_rels A); intros ls lr B ->.
    symmetry; apply Σ_finite_rev_correct.
  Qed.

End discrete_to_finite.

Check Σ_finite.
Print Assumptions Σ_finite.

Definition Σpos (Σ : fo_signature) n m (js : pos n -> syms Σ) (jr : pos m -> rels Σ) : fo_signature.
Proof.
  exists (pos n) (pos m).
  + exact (fun p => ar_syms _ (js p)).
  + exact (fun p => ar_rels _ (jr p)).
Defined.

Section discr_finite_to_pos.

  (** Strangely this does not lead to transport hell ... I should
      probably rework fol_transport_hell.v ... maybe there is a better way
      like in here *)

  Variables (Σ : fo_signature)
            (H1 : discrete (syms Σ)) (H2 : finite_t (syms Σ))
            (H3 : discrete (rels Σ)) (H4 : finite_t (rels Σ)).

  Let H5 := finite_t_discrete_bij_t_pos H2 H1.

  Let n := projT1 H5.
  Let is : syms Σ -> pos n := projT1 (projT2 H5).
  Let js : pos n -> syms Σ := proj1_sig (projT2 (projT2 H5)).

  Let Hijs p : is (js p) = p.
  Proof. apply (proj2_sig (projT2 (projT2 H5))). Qed.

  Let Hjis s : js (is s) = s.
  Proof. apply (proj2_sig (projT2 (projT2 H5))). Qed.

  Let H6 := finite_t_discrete_bij_t_pos H4 H3.

  Let m := projT1 H6.
  Let ir : rels Σ -> pos m := projT1 (projT2 H6).
  Let jr : pos m -> rels Σ := proj1_sig (projT2 (projT2 H6)).

  Let Hijr p : ir (jr p) = p.
  Proof. apply (proj2_sig (projT2 (projT2 H6))). Qed.

  Let Hjir r : jr (ir r) = r.
  Proof. apply (proj2_sig (projT2 (projT2 H6))). Qed.

  Notation Σ' := (Σpos Σ js jr).

  Local Fixpoint convert_t (t : fo_term (ar_syms Σ)) : fo_term (ar_syms Σ').
  Proof.
    refine (match t with
      | in_var i   => in_var i
      | in_fot s v => @in_fot _ (ar_syms Σ') (is s) (vec_map convert_t (cast v _))
    end).
    simpl; rewrite Hjis; trivial.
  Defined.

  Local Fixpoint convert (A : fol_form Σ) : fol_form Σ'.
  Proof.
    refine (match A with
      | ⊥              => ⊥
      | fol_atom r v   => @fol_atom Σ' (ir r) (vec_map convert_t (cast v _))
      | fol_bin b A B  => fol_bin b (convert A) (convert B)
      | fol_quant q A  => fol_quant q (convert A)
    end).
    simpl; rewrite Hjir; trivial.
  Defined.

  Section soundness.

    Variable (X : Type) (M : fo_model Σ X).

    Let M' : fo_model Σ' X.
    Proof.
      split.
      + apply (fun s => fom_syms M (js s)).
      + apply (fun r => fom_rels M (jr r)).
    Defined.

    Local Fact convert_t_sound t φ : fo_term_sem M φ t = fo_term_sem M' φ (convert_t t).
    Proof.
      induction t as [ i | s v IHv ]; simpl; auto.
      rewrite (Hjis s); simpl; f_equal.
      apply vec_pos_ext; intro; rew vec. 
      rewrite !vec_pos_map; auto.
    Qed.

    Local Fact convert_sound A φ : fol_sem M φ A <-> fol_sem M' φ (convert A).
    Proof.
      revert φ; induction A as [ | r v | b A HA B HB | q A HA ]; intros φ.
      + simpl; tauto.
      + simpl; rewrite Hjir; simpl; rewrite vec_map_map.
        apply fol_equiv_ext; f_equal.
        apply vec_pos_ext; intro; rew vec.
        apply convert_t_sound.
      + apply fol_bin_sem_ext; auto.
      + apply fol_quant_sem_ext; intro; auto.
    Qed.

    Hypothesis (Xfin : finite_t X)
               (Mdec : fo_model_dec M)
               (φ : nat -> X)
               (A : fol_form Σ)
               (HA : fol_sem M φ A).

    Local Fact convert_soundness : fo_form_fin_dec_SAT_in (convert A) X.
    Proof.
      exists M', Xfin.
      exists. { intros ? ?; apply Mdec. }
      exists φ.
      revert HA; apply convert_sound.
    Qed.

  End soundness.

  Section completeness.

    Variable (X : Type) (M' : fo_model Σ' X).

    Let M : fo_model Σ X.
    Proof.
      split.
      + intros s v.
        apply (fom_syms M' (is s)); simpl.
        rewrite Hjis; trivial.
      + intros r v.
        apply (fom_rels M' (ir r)); simpl.
        rewrite Hjir; trivial.
    Defined.

    Local Fact convert_t_complete t φ : fo_term_sem M φ t = fo_term_sem M' φ (convert_t t).
    Proof.
      induction t as [ i | s v IHv ]; simpl; auto.
      f_equal; unfold eq_rect_r.
      generalize (Hjis s); intros ->; simpl.
      apply vec_pos_ext; intro; rew vec.
      rewrite !vec_pos_map; auto.
    Qed.

    Local Fact convert_complete A φ : fol_sem M φ A <-> fol_sem M' φ (convert A).
    Proof.
      revert φ; induction A as [ | r v | b A HA B HB | q A HA ]; intros φ.
      + simpl; tauto.
      + simpl; apply fol_equiv_ext; f_equal; unfold eq_rect_r.
        generalize (Hjir r); intros ->; simpl.
        apply vec_pos_ext; intro; rew vec.
        rewrite vec_pos_map; apply convert_t_complete.
      + apply fol_bin_sem_ext; auto.
      + apply fol_quant_sem_ext; intro; auto.
    Qed.

    Hypothesis (Xfin : finite_t X)
               (M'dec : fo_model_dec M')
               (φ : nat -> X)
               (A : fol_form Σ)
               (HA : fol_sem M' φ (convert A)).

    Local Fact convert_completeness : fo_form_fin_dec_SAT_in A X.
    Proof.
      exists M, Xfin.
      exists. { intros ? ?; apply M'dec. }
      exists φ.
      revert HA; apply convert_complete.
    Qed.

  End completeness.

  Local Definition Σ_finite_to_pos (A : fol_form Σ) : 
              { n : nat & 
              { m : nat &
              { is : pos n -> syms Σ &
              { ir : pos m -> rels Σ &
              { _  : forall s s', is s = is s' -> s = s' &
              { _  : forall s, ar_syms _ (is s) = ar_syms (Σpos Σ is ir) s &
              { _  : forall r r', ir r = ir r' -> r = r' &
              { _  : forall r, ar_rels _ (ir r) = ar_rels (Σpos Σ is ir) r &
              { B  : fol_form (Σpos Σ is ir)            
              | forall X, fo_form_fin_dec_SAT_in A X 
                      <-> fo_form_fin_dec_SAT_in B X } } } } } } } } }.
  Proof.
    exists n, m, js, jr.
    exists. { intros s s' E; rewrite <- (Hijs s), E, Hijs; auto. }
    exists. { simpl; auto. }
    exists. { intros r r' E; rewrite <- (Hijr r), E, Hijr; auto. }
    exists. { simpl; auto. }
    exists (convert A); intros X; split.
    + intros (M & G1 & G2 & phi & G3).
      apply convert_soundness with M phi; auto.
    + intros (M & G1 & G2 & phi & G3).
      apply convert_completeness with M phi; auto.
  Qed.

End discr_finite_to_pos.

Check Σ_finite_to_pos.

Section combine_the_two.

  Variables (Σ : fo_signature)
            (HΣ1 : discrete (syms Σ))
            (HΣ2 : discrete (rels Σ)).

  Local Definition Σ_discrete_to_pos' (A : fol_form Σ) : 
              { n : nat & 
              { m : nat &
              { is : pos n -> syms Σ &
              { ir : pos m -> rels Σ &
              { _  : forall s s', is s = is s' -> s = s' &
              { _  : forall s, ar_syms _ (is s) = ar_syms (Σpos Σ is ir) s &
              { _  : forall s, In (is s) (fol_syms A) & 
              { _  : forall r r', ir r = ir r' -> r = r' &
              { _  : forall r, ar_rels _ (ir r) = ar_rels (Σpos Σ is ir) r &
              { _  : forall r, In (ir r) (fol_rels A) & 
              { B  : fol_form (Σpos Σ is ir)            
              | fo_form_fin_dec_SAT A 
            <-> fo_form_fin_dec_SAT B } } } } } } } } } } }.
  Proof.
    destruct (Σ_finite_full HΣ1 HΣ2 A (incl_refl _) (incl_refl _)) as (B & HB).
    destruct Σ_finite_to_pos with (A := B)
      as (n & m & i & j & F1 & F2 & F3 & F4 & C & HC).
    + apply Σ_fin_discrete_syms.
    + apply Σ_fin_finite_syms.
    + apply Σ_fin_discrete_rels.
    + apply Σ_fin_finite_rels.
    + exists n, m, (fun p => proj1_sig (i p)), (fun p => proj1_sig (j p)).
      exists.
      { intros s s' E; apply F1; revert E; generalize (i s) (i s').
        intros (? & ?) (? & ?); simpl; intros ->; f_equal; apply eq_bool_pirr. }
      exists. { intros; simpl; auto. }
      exists. { intro; apply Σ_fin_syms. }
      exists.
      { intros r r' E; apply F3; revert E; generalize (j r) (j r').
        intros (? & ?) (? & ?); simpl; intros ->; f_equal; apply eq_bool_pirr. }
      exists. { intros; simpl; auto. }
      exists. { intro; apply Σ_fin_rels. }
      exists C.
      transitivity (fo_form_fin_dec_SAT B).
      * clear C HC; revert B HB.
        generalize (fol_syms A) (fol_rels A); intros ls lr B ->.
        symmetry; apply Σ_finite_rev_correct.
      * apply exists_equiv; auto.
  Qed.

  Definition Σ_discrete_to_pos (A : fol_form Σ) : 
              { n : nat & 
              { m : nat &
              { i : pos n -> syms Σ &
              { j : pos m -> rels Σ &
              { B  : fol_form (Σpos Σ i j)
              | fo_form_fin_dec_SAT A 
            <-> fo_form_fin_dec_SAT B } } } } }.
  Proof.
    destruct (Σ_discrete_to_pos' A) as (n & m & i & j & _ & _ & _ & _ & _ & _ & B & HB).
    exists n, m, i, j, B; auto.
  Qed.

End combine_the_two.
