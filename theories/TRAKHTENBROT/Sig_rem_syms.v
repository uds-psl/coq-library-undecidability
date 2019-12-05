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
  Require Import notations fol_ops fo_sig utils fo_terms fo_logic fo_sat.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Section Sig_remove_symbols.

  Variable (Σ : fo_signature).

  (** map every term symbol to a relation symbols of +1 arity
      and add an (interpreted) equality *)

  Definition Σnosyms : fo_signature.
  Proof.
    exists Empty_set (syms Σ + (unit + rels Σ))%type.
    + intros [].
    + intros [ s | [ [] | r ] ].
      * exact (S (ar_syms _ s)).
      * exact 2.
      * exact (ar_rels _ r).
  Defined.

  Notation Σ' := Σnosyms.

  Let e : rels Σ' := inr (inl tt). 

  Local Definition fom_nosyms X : fo_model Σ X -> fo_model Σ' X.
  Proof.
    intros (F,R); split.
    + intros [].
    + intros [s|[[]|r]].
      * exact (fun v => vec_head v = F _ (vec_tail v)).
      * exact (rel2_on_vec eq).
      * exact (R r).
  Defined. 

  Notation 𝕋 := (fol_term Σ).
  Notation 𝔽 := (fol_form Σ).

  Notation 𝕋' := (fol_term Σ').
  Notation 𝔽' := (fol_form Σ').

  Section removing_symbols_from_terms.

    Let f k (p : pos k) n : 𝕋' := match n with 0 => £ (pos2nat p) | S n => £ (n+1+k) end.

    Local Fixpoint fot_rem_syms (t : 𝕋) : 𝔽' :=
      match t with
        | in_var n   => @fol_atom Σ' e (£0##£(S n)##ø)
        | in_fot s v => 
            let A  := @fol_atom Σ' (inl s) (£(ar_syms _ s)##vec_set_pos (fun p => £ (pos2nat p))) in
            let wB := vec_set_pos (fun p => (fot_rem_syms (vec_pos v p))⦃f p⦄) 
            in fol_mquant fol_ex (ar_syms _ s) (A ⟑ fol_vec_fa wB)
      end.

    Local Fact fot_rem_syms_fix0 n : fot_rem_syms (in_var n) = fol_atom e (£0##£(S n)##ø).
    Proof. trivial. Qed.

    Local Fact fot_rem_syms_fix1 s v : 
                 fot_rem_syms (in_fot s v) 
               = let A  := @fol_atom Σ' (inl s) (£(ar_syms _ s)##vec_set_pos (fun p => £ (pos2nat p))) in
                 let wB := vec_set_pos (fun p => (fot_rem_syms (vec_pos v p))⦃f p⦄) 
                 in fol_mquant fol_ex (ar_syms _ s) (A ⟑ fol_vec_fa wB).
    Proof. trivial. Qed.

    Opaque fo_term_syms.

    Local Fact fot_rem_syms_rels t : incl (fol_rels (fot_rem_syms t)) (inr (inl tt)::map inl (fo_term_syms t)).
    Proof.
      induction t as [ n | s v IHv ].
      + rewrite fot_rem_syms_fix0; cbv; tauto.
      + rewrite fot_rem_syms_fix1; simpl.
        rewrite fol_rels_mquant; simpl.
        unfold fol_vec_fa.
        rewrite fol_rels_bigop.
        intros r; simpl.
        rewrite in_app_iff, in_map_iff, in_flat_map.
        intros [ <- | [ H | [] ] ]; auto.
        { right; exists s; auto; rew fot; simpl; auto. } 
        revert H; intros (A & H1 & H2); revert H2.
        apply vec_list_inv in H1.
        destruct H1 as (p & ->); rew vec.
        rewrite fol_rels_subst.
        intros H; apply IHv in H; revert H.
        simpl; rewrite in_map_iff.
        intros [ <- | (s' & <- & Hs') ]; auto.
        right; exists s'; split; auto; rew fot.
        right; rewrite in_flat_map.
        exists (vec_pos v p); split; auto.
        apply in_vec_list, in_vec_pos.
    Qed.
 
    Local Fact fot_rem_syms_spec t X M φ ψ : 
            (forall n, φ n = ψ (S n))
         -> ψ 0 = fo_term_sem M φ t 
        <-> fol_sem (@fom_nosyms X M) ψ (fot_rem_syms t).
    Proof.
      revert X M φ ψ.
      induction t as [ n | s v IHv ]; intros X M phi psi H2.
      + destruct M as (re,sy); simpl; rewrite <- H2; tauto.
      + specialize (fun p => IHv p X M).
        rewrite fot_rem_syms_fix1.
        rewrite fol_sem_mexists.
        split.
        * intros H3.
          exists (vec_set_pos (fun p => fo_term_sem M phi (vec_pos v p))).
          destruct M as (sy,re); simpl; split.
          - simpl. 
            replace (ar_syms _ s) with (0+ar_syms _ s) at 3 by lia.
            rewrite env_vlift_fix1; simpl; f_equal; rewrite H3; simpl; f_equal.
            apply vec_pos_ext; intros p; rew vec; rew fot.
            rewrite env_vlift_fix0; rew vec.
          - simpl.
            rewrite fol_sem_vec_fa; intros p.
            rew vec.
            rewrite fol_sem_subst.
            rewrite <- IHv; auto.
            2: reflexivity.
            simpl; rew fot.
            rewrite env_vlift_fix0; rew vec.
            apply fo_term_sem_ext; intros n Hn.
            replace (n+1+ar_syms _ s) with ((S n)+ar_syms _ s) by lia.
            rewrite env_vlift_fix1; auto.
        * intros (w & Hw1 & Hw2).
          destruct M as (sy,re); simpl.
          simpl in Hw1.
          replace (ar_syms _ s) with (0+ar_syms _ s) in Hw1 at 2 by lia.
          rewrite env_vlift_fix1 in Hw1.
          rewrite Hw1; clear Hw1.
          simpl; f_equal.
          apply vec_pos_ext; intros p; rew vec.
          rew fot.
          rewrite fol_sem_vec_fa in Hw2.
          specialize (Hw2 p); revert Hw2; rew vec; intros Hw2.
          rewrite fol_sem_subst in Hw2.
          rewrite <- IHv with (φ := phi) in Hw2; auto.
          intros n; simpl.
          replace (n+1+ar_syms _ s) with ((S n)+ar_syms _ s) by lia.
          rewrite env_vlift_fix1; auto.
    Qed.

  End removing_symbols_from_terms.

  Section and_now_from_formulas.

    Let f k (p : pos k) n : 𝕋' := match n with 0 => £ (pos2nat p) | S n => £ (n+k) end.

    Local Fixpoint fol_rem_syms A : 𝔽' :=
      match A with
        | ⊥               => ⊥
        | fol_atom r v    => let A  := @fol_atom Σ' (inr (inr r)) (vec_set_pos (fun p => £ (pos2nat p))) in
                             let wB := vec_set_pos (fun p => (fot_rem_syms (vec_pos v p))⦃f p⦄)
                             in  fol_mquant fol_ex (ar_rels _ r) (A ⟑ fol_vec_fa wB)
        | fol_bin c A B   => fol_bin c (fol_rem_syms A) (fol_rem_syms B)
        | fol_quant q A   => fol_quant q (fol_rem_syms A)
      end.

    Local Fact fol_rem_syms_rels A : 
         incl (fol_rels (fol_rem_syms A))
              (inr (inl tt) :: map inl                    (fol_syms A) 
                            ++ map (fun r => inr (inr r)) (fol_rels A)).
    Proof.
      induction A as [ | r v | b A IHA B IHB | q A IHA ].
      + cbv; tauto.
      + simpl.
        rewrite fol_rels_mquant; simpl.
        unfold fol_vec_fa.
        rewrite fol_rels_bigop.
        intros s; simpl; rewrite in_app_iff, in_flat_map, in_app_iff.
        intros [ <- | [ (A & H1 & H2) | [] ] ]; simpl; auto; revert H2.
        apply vec_list_inv in H1; destruct H1 as (p & ->); rew vec; intros H1.
        rewrite fol_rels_subst in H1.
        apply fot_rem_syms_rels in H1; simpl in H1.
        rewrite in_map_iff in H1.
        destruct H1 as [ | (s' & <- & H1) ]; auto.
        right; left; apply in_map_iff.
        exists s'; split; auto.
        apply in_flat_map.
        exists (vec_pos v p); split; auto.
        apply in_vec_list, in_vec_pos.
      + intros r; simpl.
        repeat rewrite map_app.
        repeat rewrite in_app_iff.
        intros [ H | H ].
        * apply IHA in H; revert H; simpl.
          rewrite in_app_iff; tauto.
        * apply IHB in H; revert H; simpl.
          rewrite in_app_iff; tauto.
      + intros r; simpl.
        repeat rewrite map_app.
        repeat rewrite in_app_iff.
        intros H; apply IHA in H; revert H.
        simpl; rewrite in_app_iff; tauto.
    Qed.
    
    Local Fact fol_rem_syms_spec A X M φ : 
           fol_sem M φ A 
       <-> fol_sem (@fom_nosyms X M) φ (fol_rem_syms A).
    Proof.
      revert φ.
      induction A as [ | r v | b A IHA B IHB | q A IHA ]; intros phi.
      + simpl; tauto.
      + simpl; rewrite fol_sem_mexists; split.
        * intros H; simpl in H |- *.
          exists (vec_map (fo_term_sem M phi) v); split.
          - revert H; apply fol_equiv_ext.
            unfold fom_nosyms; destruct M as (re,sy); simpl; f_equal.
            apply vec_pos_ext; intros p; rew vec; rew fot.
            rewrite env_vlift_fix0; rew vec.
          - rewrite fol_sem_vec_fa; intros p; rew vec.
            rewrite fol_sem_subst; simpl.
            rewrite <- fot_rem_syms_spec; auto.
            2: intro; reflexivity.
            simpl.
            rewrite env_vlift_fix0; rew vec.
            apply fo_term_sem_ext.
            intros; rewrite env_vlift_fix1; auto.
        * intros (w & Hw1 & Hw2); revert Hw1.
          simpl; apply fol_equiv_ext.
          unfold fom_nosyms; destruct M as (re,sy); simpl; f_equal.
          apply vec_pos_ext; intros p; rew vec; rew fot.
          rewrite env_vlift_fix0.
          rewrite fol_sem_vec_fa in Hw2.
          specialize (Hw2 p); revert Hw2; rew vec.
          rewrite fol_sem_subst, <- fot_rem_syms_spec; auto.
          2: intro; reflexivity.
          simpl; rewrite env_vlift_fix0.
          intros ->; apply fo_term_sem_ext.
          intros; rewrite env_vlift_fix1; auto.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext.
        intro; auto.
    Qed.

  End and_now_from_formulas.

  Variable (X : Type) (M : fo_model Σ' X) 
           (HM : forall x y, fom_rels M e (x##y##ø) <-> x = y)  (* e is an interpreted equality *)
           .

  Local Definition fol_rel_fun (s : syms Σ) : 𝔽' := 
       let n := ar_syms _ s
       in ∀∀ fol_mquant fol_fa n (   
              @fol_atom Σ' (inl s) (£(S n)##vec_set_pos (fun p => £(pos2nat p))) 
                     ⤑ @fol_atom Σ' (inl s) (£n##vec_set_pos (fun p => £(pos2nat p)))
                     ⤑ @fol_atom Σ' e (£(S n)##£n##ø) ).

  Local Fact fol_rel_fun_spec s φ : 
             fol_sem M φ (fol_rel_fun s) 
         <-> graph_fun (fun v x => fom_rels M (inl s) (x##v)).
  Proof.
    unfold fol_rel_fun; simpl; split.
    + intros H v x y H1 H2.
      specialize (H x y).
      rewrite fol_sem_mforall in H.
      specialize (H v); simpl fol_sem in H.
      rewrite env_vlift_fix1 with (k := 1) in H.
      rewrite env_vlift_fix1 with (k := 0) in H.
      rewrite HM in H; simpl in H.
      apply H.
      * revert H1; apply fol_equiv_ext; do 2 f_equal.
        apply vec_pos_ext; intros p; rew vec; rew fot.
        rewrite env_vlift_fix0; auto.
      * revert H2; apply fol_equiv_ext; do 2 f_equal.
        apply vec_pos_ext; intros p; rew vec; rew fot.
        rewrite env_vlift_fix0; auto.
    + intros H x y.
      rewrite fol_sem_mforall; intros v.
      specialize (H v x y); simpl in H.
      simpl.
      rewrite env_vlift_fix1 with (k := 1).
      rewrite env_vlift_fix1 with (k := 0).
      rewrite HM; simpl.
      intros H1 H2; apply H.
      * revert H1; apply fol_equiv_ext; do 2 f_equal.
        apply vec_pos_ext; intros p; rew vec; rew fot.
        rewrite env_vlift_fix0; auto.
      * revert H2; apply fol_equiv_ext; do 2 f_equal.
        apply vec_pos_ext; intros p; rew vec; rew fot.
        rewrite env_vlift_fix0; auto.
  Qed.
 
  Local Definition fol_rel_tot (s : syms Σ) : 𝔽' := 
        let n := ar_syms _ s
        in fol_mquant fol_fa n (∃ @fol_atom Σ' (inl s) (£0##vec_set_pos (fun p => £(1+pos2nat p)))). 

  Local Fact fol_rel_tot_spec s φ : 
             fol_sem M φ (fol_rel_tot s) 
         <-> graph_tot (fun v x => fom_rels M (inl s) (x##v)).
  Proof.
    unfold fol_rel_tot.
    rewrite fol_sem_mforall.
    apply forall_equiv; intros v; simpl.
    apply exists_equiv; intros x.
    apply fol_equiv_ext; do 2 f_equal.
    apply vec_pos_ext; intros p; rew vec; rew fot.
    simpl; rewrite env_vlift_fix0; auto.
  Qed.

  Local Definition fol_rels_are_functions ls := 
        fol_lconj (map (fun s => fol_rel_fun s ⟑ fol_rel_tot s) ls).

  Local Fact fol_rels_are_functions_spec ls φ : 
             fol_sem M φ (fol_rels_are_functions ls) 
         <-> forall s, In s ls -> is_graph_function (fun v x => fom_rels M (inl s) (x##v)).
  Proof.
    unfold fol_rels_are_functions.
    rewrite fol_sem_lconj; split.
    + intros H s Hs; red.
      rewrite <- fol_rel_tot_spec with (φ := φ).
      rewrite <- fol_rel_fun_spec with (φ := φ).
      apply (H (fol_rel_fun s ⟑ fol_rel_tot s)), in_map_iff.
      exists s; auto.
    + intros H B; rewrite in_map_iff.
      intros (s & <- & Hs); split.
      * apply fol_rel_fun_spec, H; auto.
      * apply fol_rel_tot_spec, H; auto.
  Qed.

  Definition Σsyms_Σnosyms ls A := fol_rels_are_functions ls ⟑ fol_rem_syms A.

End Sig_remove_symbols.

(** And now the reduction soundness and completeness results for Σsyms_Σnosyms 
    The reduction is from FIN_DEC_DISCR_SAT to FIN_DEC_EQ_SAT *)

(** Soundess of Σsyms_Σnosyms *)

Theorem Σsyms_Σnosyms_sound Σ ls A X : 
             @fo_form_fin_discr_dec_SAT_in Σ A X
          -> @fo_form_fin_dec_eq_SAT_in (Σnosyms Σ) (inr (inl tt)) eq_refl (Σsyms_Σnosyms ls A) X.
Proof.
  intros (H0 & M & H1 & H2 & phi & H3).
  exists (fom_nosyms M), H1; destruct M as (sy,re).
  exists.
  { intros [s|[[]|r]]; simpl.
    + intros; apply H0.
    + intros; apply H0.
    + intros; apply H2. }
  exists.
  { intros x y; cbv; tauto. }
  exists phi.
  unfold Σsyms_Σnosyms; split.
  + apply fol_rels_are_functions_spec; auto; simpl; try tauto.
    intros s Hs; split.
    * intros v x y; simpl; intros; subst; auto.
    * intros v; exists (sy s v); simpl; auto.
  + revert H3; apply fol_rem_syms_spec.
Qed.

(** Completeness of Σsyms_Σnosyms *)

Section completeness.

  Variable (Σ : fo_signature) (ls : list (syms Σ)) (A : fol_form Σ) 
           (Hls : forall s, { In s ls } + { ~ In s ls })
           (HAls : incl (fol_syms A) ls).

  Notation Σ' := (Σnosyms Σ).

  Let e : rels Σ' := inr (inl tt).

  Variable (X : Type).

  Section nested.

    Variable (M : fo_model Σ' X)  
             (Xfin : finite_t X) 
             (Mdec : fo_model_dec M) 
             (He : forall x y, fom_rels M e (x##y##ø) <-> x = y)
             (φ : nat -> X) 
             (HM : fol_sem M φ (Σsyms_Σnosyms ls A)).

    Let HF : forall s, In s ls -> is_graph_function (fun v x => fom_rels M (inl s) (x##v)).
    Proof. 
      simpl in HM; apply proj1 in HM. 
      rewrite fol_rels_are_functions_spec in HM; auto.
    Qed.

    Let HA : fol_sem M φ (fol_rem_syms A).
    Proof. simpl in HM; apply proj2 in HM; auto. Qed.

    Let F (s : syms Σ) : In s ls -> { f | forall v x, fom_rels M (inl s) (x##v) <-> x = f v }.
    Proof. intro; apply graph_tot_reif; auto. Qed.

    Local Definition Σsyms_Σnosyms_rev_model : fo_model Σ X.
    Proof.
      split.
      + intros s.
        destruct (Hls s) as [ H | H ].
        * exact (proj1_sig (F s H)).
        * exact (fun _ => φ 0).
      + intros r.
        exact (fom_rels M (inr (inr r))).
    Defined.

    Local Fact Σsyms_Σnosyms_complete_nested : fol_sem Σsyms_Σnosyms_rev_model φ A.
    Proof.
      apply fol_rem_syms_spec.
      revert HA.
      apply fo_model_projection' with (i := fun x => x) (j := fun x => x) (ls := nil) 
             (lr := inr (inl tt) :: map inl (fol_syms A) ++ map (fun r => inr (inr r)) (fol_rels A)); auto.
      + intros s v [].
      + intros r v; simpl In; rewrite in_app_iff, in_map_iff, in_map_iff.
        intros [ <- | [ (s & <- & Hs) | (r' & <- & Hr') ] ]; simpl.
        * vec split v with x; vec split v with y; vec nil v; simpl. 
          fold e; rewrite He; tauto.
        * destruct (Hls s) as [ H | H ]; try tauto.
          vec split v with x; simpl.
          rewrite <- (proj2_sig (F s H) v x).
          apply fol_equiv_ext; f_equal; f_equal.
          apply vec_pos_ext; intro; rew vec.
          destruct H; revert Hs; apply HAls.
        * apply fol_equiv_ext; f_equal; f_equal.
          apply vec_pos_ext; simpl; intros; rew vec.
          rewrite vec_pos_map; auto.
      + intros [].
      + apply fol_rem_syms_rels.
    Qed.

  End nested.

  Theorem Σsyms_Σnosyms_complete : 
          @fo_form_fin_dec_eq_SAT_in (Σnosyms Σ) (inr (inl tt)) eq_refl (Σsyms_Σnosyms ls A) X
       -> @fo_form_fin_discr_dec_SAT_in Σ A X.
  Proof.
    intros (M & H1 & H2 & H3 & phi & H5).
    cbn in H3.
    exists.
    { intros x y.
      generalize (H2 e (x##y##ø)).
      intros []; [ left | right ]; try red; 
        rewrite <- H3; auto. }
    exists (Σsyms_Σnosyms_rev_model H1 H2 H3 H5).
    exists H1.
    exists. { intros r v; simpl; apply H2. }
    exists phi.
    apply Σsyms_Σnosyms_complete_nested.
  Qed.

End completeness.
