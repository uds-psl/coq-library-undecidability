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
  Require Import notations fol_ops utils fo_terms fo_logic fo_sat.

Set Implicit Arguments.

Local Reserved Notation "⟪ A ⟫'" (at level 1, format "⟪ A ⟫'").

Local Notation ø := vec_nil.

Section remove_constants.

  Variable (Σ : fo_signature) (HΣ : forall s, ar_syms Σ s = 0)
           (ls : list (syms Σ)).

  Definition Σrem_cst : fo_signature.
  Proof.
    exists Empty_set (rels Σ).
    + intros [].
    + apply ar_rels.
  Defined.

  Notation Σ' := Σrem_cst.

  Notation 𝕋 := (fo_term nat (ar_syms Σ)).
  Notation 𝔽 := (fol_form Σ).

  Notation 𝕋' := (fo_term nat (ar_syms Σ')).
  Notation 𝔽' := (fol_form Σ').

  Implicit Type σ : syms Σ -> nat.

  Let convert_t σ (t : 𝕋) : 𝕋' :=
    match t with 
      | in_var n   => in_var n
      | in_fot s _ => in_var (σ s)
    end.

  Local Fixpoint encode σ (A : 𝔽)  : 𝔽' := 
    match A with
      | ⊥              => ⊥
      | fol_atom _ r v => fol_atom Σ' r (vec_map (convert_t σ) v) 
      | fol_bin b A B  => fol_bin b (encode σ A) (encode σ B)
      | fol_quant q A  => fol_quant q (encode (fun s => S (σ s)) A)
    end.

  Section soundness.
    
    Variable (X : Type) (M : fo_model Σ X).

    Definition Σrem_cst_model : fo_model Σ' X.
    Proof.
      split.
      + intros [].
      + apply (fom_rels M).
    Defined.

    Notation M' := Σrem_cst_model.

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).

    Theorem soundness σ (A : 𝔽) φ ψ :
            (forall s, In s ls -> In (σ s) (fol_vars A) -> False)
         -> (forall n, In n (fol_vars A) -> φ n = ψ n)
         -> (forall s, In s ls -> ψ (σ s) = fom_syms M s (cast ø (eq_sym (HΣ s))))
         -> incl (fol_syms A) ls
         ->  ⟪A⟫ φ <-> ⟪encode σ A⟫' ψ.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in σ, φ, ψ |- *; 
        intros H1 H2 H3 H4; simpl; try tauto.
      + rewrite vec_map_map.
        apply fol_equiv_ext; f_equal.
        apply vec_pos_ext; intro p; rew vec.
        cut (incl (fo_term_syms (vec_pos v p)) ls).
        2:{ intros s Hs; apply H4; simpl; apply in_flat_map.
            exists (vec_pos v p); split; auto.
            apply in_vec_list, in_vec_pos. }
        cut (forall n, In n (fo_term_vars (vec_pos v p)) -> φ n = ψ n).
        2:{ intros n Hn; apply H2, in_flat_map.
            exists (vec_pos v p); split; auto.
            apply in_vec_list, in_vec_pos. }
        generalize (vec_pos v p); intros [ n | s w ] H5 H6; simpl.
        - apply H5; simpl; auto.
        - rewrite H3; f_equal; auto.
          2: apply H6; rew fot; simpl; auto.
          clear H5 H6.
          revert w; rewrite HΣ; intros w; auto.
      + apply fol_bin_sem_ext.
        * apply HA; auto.
          - intros s G1 G2; apply (H1 _ G1), in_app_iff; auto.
          - intros; apply H2, in_app_iff; auto.
          - intros ? ?; apply H4, in_app_iff; auto.
        * apply HB; auto.
          - intros s G1 G2; apply (H1 _ G1), in_app_iff; auto.
          - intros; apply H2, in_app_iff; auto.
          - intros ? ?; apply H4, in_app_iff; auto.
      + apply fol_quant_sem_ext; intros x.
        apply HA; auto.
        * intros s G1 G2; apply (H1 _ G1). 
          simpl; apply in_flat_map.
          exists (S (σ s)); simpl; auto.
        * intros [|n] Hn; simpl; auto.
          apply H2; simpl; apply in_flat_map.
          exists (S n); simpl; auto.
    Qed.
      
  End soundness.

  Section completeness.

    Variable (X : Type) (M' : fo_model Σ' X).

    Definition Σadd_cst_model σ (ψ : nat -> X) : fo_model Σ X.
    Proof.
      split.
      + intros s _; exact (ψ (σ s)).
      + apply (fom_rels M').
    Defined.

    Notation M := Σadd_cst_model.

    Theorem completeness σ (A : 𝔽) φ ψ :
            (forall s, In s ls -> In (σ s) (fol_vars A) -> False)
         -> (forall n, In n (fol_vars A) -> φ n = ψ n)
         -> incl (fol_syms A) ls
         -> fol_sem (Σadd_cst_model σ ψ) φ A
        <-> fol_sem M' ψ (encode σ A).
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in σ, φ, ψ |- *; 
      intros H1 H2 H3; simpl; try tauto.
      + rewrite vec_map_map.
        apply fol_equiv_ext; f_equal.
        apply vec_pos_ext; intro p; rew vec.
        cut (incl (fo_term_syms (vec_pos v p)) ls).
        2:{ intros s Hs; apply H3; simpl; apply in_flat_map.
            exists (vec_pos v p); split; auto.
            apply in_vec_list, in_vec_pos. }
        cut (forall n, In n (fo_term_vars (vec_pos v p)) -> φ n = ψ n).
        2:{ intros n Hn; apply H2, in_flat_map.
            exists (vec_pos v p); split; auto.
            apply in_vec_list, in_vec_pos. }
        generalize (vec_pos v p); intros [ n | s w ] H5 H6; simpl; auto.
        apply H5; simpl; auto.
      + apply fol_bin_sem_ext.
        * apply HA; auto.
          - intros s G1 G2; apply (H1 _ G1), in_app_iff; auto.
          - intros; apply H2, in_app_iff; auto.
          - intros ? ?; apply H3, in_app_iff; auto.
        * apply HB; auto.
          - intros s G1 G2; apply (H1 _ G1), in_app_iff; auto.
          - intros; apply H2, in_app_iff; auto.
          - intros ? ?; apply H3, in_app_iff; auto.
      + apply fol_quant_sem_ext; intros x.
        rewrite <- HA with (φ := φ↑x); unfold M; simpl; try tauto.
        * intros s G1 G2; apply (H1 _ G1). 
          simpl; apply in_flat_map.
          exists (S (σ s)); simpl; auto.
        * intros [|n] Hn; simpl; auto.
          apply H2; simpl; apply in_flat_map.
          exists (S n); simpl; auto.
    Qed.

  End completeness.

End remove_constants.

Section reduction.

Check encode.

End reduction.

