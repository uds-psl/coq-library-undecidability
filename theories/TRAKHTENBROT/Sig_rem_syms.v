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
  Require Import notations fol_ops utils fo_terms fo_logic.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Section Sig_remove_symbols.

  Variable (Σ : fo_signature).

  Definition fos_nosyms : fo_signature.
  Proof.
    exists Empty_set (syms Σ + (unit + rels Σ))%type.
    + intros [].
    + intros [ s | [ [] | r ] ].
      * exact (S (ar_syms _ s)).
      * exact 2.
      * exact (ar_rels _ r).
  Defined.

  Notation Σ' := fos_nosyms.

  Let e : rels Σ' := inr (inl tt). 

  Definition fom_nosyms X : fo_model Σ X -> fo_model Σ' X.
  Proof.
    intros (F,R); split.
    + intros [].
    + intros [s|[[]|r]].
      * exact (fun v => vec_head v = F _ (vec_tail v)).
      * exact (rel2_on_vec eq).
      * exact (R r).
  Defined. 

  Notation 𝕋 := (fo_term nat (ar_syms Σ)).
  Notation 𝔽 := (fol_form Σ).

  Notation 𝕋' := (fo_term nat (ar_syms Σ')).
  Notation 𝔽' := (fol_form Σ').

  Section removing_symbols.

    Let rem_syms (t : 𝕋) : 
        { A : 𝔽' | forall X M φ ψ, 
                          (forall n, φ n = ψ (S n))
                       -> ψ 0 = fo_term_sem (fom_syms M) φ t 
                      <-> fol_sem (@fom_nosyms X M) ψ A }.
    Proof.
      induction t as [ n | s v IHv ] using fo_term_pos_rect.
      + exists (fol_atom Σ' e (£0##£(S n)##ø)).
        intros X (sy,re) phi psi H2; simpl.
        rewrite <- H2; tauto.
      + apply vec_reif_t in IHv.
        destruct IHv as (vB & HB).
        set (A := fol_atom Σ' (inl s) (£(ar_syms _ s)##vec_set_pos (fun p => £ (pos2nat p)))).
        set (f (p : pos (ar_syms _ s)) n := match n with 0 => £ (pos2nat p) | S n => £ (n+1+ar_syms _ s) end : 𝕋').
        set (wB := vec_set_pos (fun p => (vec_pos vB p)⦃f p⦄)).
        exists (fol_mquant fol_ex (ar_syms _ s) (A ⟑ fol_vec_fa wB)).
        intros X M phi psi H2; simpl.
        specialize (fun p => HB p X M).
        destruct M as (sy,re).
        rewrite fol_sem_mexists.
        split.
        * intros H3.
          exists (vec_set_pos (fun p => fo_term_sem sy phi (vec_pos v p))); split.
          - unfold A, fom_nosyms; simpl.
            replace (ar_syms _ s) with (0+ar_syms _ s) at 3 by lia.
            rewrite env_vlift_fix1; simpl; f_equal; rewrite H3; simpl; f_equal.
            apply vec_pos_ext; intros p; rew vec; rew fot.
            rewrite env_vlift_fix0; rew vec.
          - rewrite fol_sem_vec_fa; intros p.
            unfold wB; rew vec.
            rewrite fol_sem_subst.
            rewrite <- HB; auto.
            2: reflexivity.
            simpl; rew fot.
            rewrite env_vlift_fix0; rew vec.
            apply fo_term_sem_ext; intros n Hn.
            replace (n+1+ar_syms _ s) with ((S n)+ar_syms _ s) by lia.
            rewrite env_vlift_fix1; auto.
        * intros (w & Hw1 & Hw2).
          unfold A in Hw1; simpl in Hw1.
          replace (ar_syms _ s) with (0+ar_syms _ s) in Hw1 at 2 by lia.
          rewrite env_vlift_fix1 in Hw1.
          rewrite Hw1; clear Hw1.
          simpl; f_equal.
          apply vec_pos_ext; intros p; rew vec.
          rew fot.
          unfold wB in Hw2.
          rewrite fol_sem_vec_fa in Hw2.
          specialize (Hw2 p); revert Hw2; rew vec; intros Hw2.
          rewrite fol_sem_subst in Hw2.
          rewrite <- HB with (φ := phi) in Hw2; auto.
          intros n; simpl.
          replace (n+1+ar_syms _ s) with ((S n)+ar_syms _ s) by lia.
          rewrite env_vlift_fix1; auto.
    Qed.

    Definition fot_rem_syms t := proj1_sig (rem_syms t).

    Fact fot_rem_syms_spec t X M φ ψ : 
            (forall n, φ n = ψ (S n))
         -> ψ 0 = fo_term_sem (fom_syms M) φ t 
        <-> fol_sem (@fom_nosyms X M) ψ (fot_rem_syms t).
    Proof. apply (proj2_sig (rem_syms t)). Qed. 
 
  End removing_symbols.

  Section now_formulas.

    Let rem_syms (A : 𝔽) : 
        { A' : 𝔽' | forall X M φ, 
                          fol_sem M φ A 
                      <-> fol_sem (@fom_nosyms X M) φ A' }.
    Proof.
      induction A as [ | r v | b A (A' & HA') B (B' & HB') | q A (A' & HA') ].
      + exists ⊥; simpl; tauto.
      + set (vB := vec_map fot_rem_syms v).
        set (A := fol_atom Σ' (inr (inr r)) (vec_set_pos (fun p => £ (pos2nat p)))).
        set (f (p : pos (ar_rels _ r)) n := match n with 0 => £ (pos2nat p) | S n => £ (n+ar_rels _ r) end : 𝕋').
        set (wB := vec_set_pos (fun p => (fot_rem_syms (vec_pos v p))⦃f p⦄)).
        exists (fol_mquant fol_ex (ar_rels _ r) (A ⟑ fol_vec_fa wB)).
        intros X (sy,re) phi; rewrite fol_sem_mexists; split.
        * intros H; simpl in H.
          exists (vec_map (fo_term_sem sy phi) v); split.
          - unfold A; simpl.
            revert H; apply fol_equiv_ext; f_equal.
            apply vec_pos_ext; intros p; rew vec; rew fot.
            rewrite env_vlift_fix0; rew vec.
          - rewrite fol_sem_vec_fa; intros p.
            unfold wB; rew vec.
            rewrite fol_sem_subst.
            rewrite <- fot_rem_syms_spec; auto.
            2: intro; reflexivity.
            simpl.
            rewrite env_vlift_fix0; rew vec.
            apply fo_term_sem_ext.
            intros; rewrite env_vlift_fix1; auto.
        * intros (w & Hw1 & Hw2).
          unfold A in Hw1; simpl in Hw1.
          simpl; revert Hw1; apply fol_equiv_ext; f_equal.
          apply vec_pos_ext; intros p; rew vec; rew fot.
          rewrite env_vlift_fix0.
          rewrite fol_sem_vec_fa in Hw2.
          specialize (Hw2 p); revert Hw2; unfold wB; rew vec.
          rewrite fol_sem_subst, <- fot_rem_syms_spec; auto.
          2: intro; reflexivity.
          simpl; rewrite env_vlift_fix0.
          intros ->; apply fo_term_sem_ext.
          intros; rewrite env_vlift_fix1; auto.
      + exists (fol_bin b A' B').  
        intros X M phi; simpl.
        apply fol_bin_sem_ext; auto.
      + exists (fol_quant q A').
        intros X M phi.
        simpl; apply fol_quant_sem_ext.
        intro; auto.
    Qed.

    Definition fol_rem_syms A := proj1_sig (rem_syms A).

    Fact fol_rem_syms_spec A X M φ : 
           fol_sem M φ A 
       <-> fol_sem (@fom_nosyms X M) φ (fol_rem_syms A).
    Proof. apply (proj2_sig (rem_syms A)). Qed.

  End now_formulas.

  Check fol_rem_syms_spec.

End Sig_remove_symbols.