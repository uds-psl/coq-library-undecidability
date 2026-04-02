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
  Require Import notations utils decidable fol_ops fo_sig fo_terms fo_logic fo_sat.

Import fol_notations.

Set Implicit Arguments.

(* * From signatures with only constants functions to function symbol free signatures *)

Local Reserved Notation "⟪ A ⟫'" (at level 0, format "⟪ A ⟫'").

Local Abbreviation ø := vec_nil.

Section remove_constants.

  Variable (Σ : fo_signature) (HΣ : forall s, ar_syms Σ s = 0)
           (ls : list (syms Σ)).

  Definition Σrem_cst : fo_signature.
  Proof using Σ.
    exists Empty_set (rels Σ).
    + intros [].
    + apply ar_rels.
  Defined.

  Abbreviation Σ' := Σrem_cst.

  Abbreviation 𝕋 := (fol_term Σ).
  Abbreviation 𝔽 := (fol_form Σ).

  Abbreviation 𝕋' := (fol_term Σ').
  Abbreviation 𝔽' := (fol_form Σ').

  Implicit Type σ : syms Σ -> nat.

  Let convert_t σ (t : 𝕋) : 𝕋' :=
    match t with 
      | in_var n   => in_var n
      | in_fot s _ => in_var (σ s)
    end.

  Local Fixpoint encode σ (A : 𝔽)  : 𝔽' := 
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => @fol_atom Σ' r (vec_map (convert_t σ) v) 
      | fol_bin b A B  => fol_bin b (encode σ A) (encode σ B)
      | fol_quant q A  => fol_quant q (encode (fun s => S (σ s)) A)
    end.

  Section soundness.
    
    Variable (X : Type) (M : fo_model Σ X).

    Definition Σrem_cst_model : fo_model Σ' X.
    Proof using M.
      split.
      + intros [].
      + apply (fom_rels M).
    Defined.

    Abbreviation M' := Σrem_cst_model.

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).

    Local Fact soundness σ (A : 𝔽) φ ψ :
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
          revert w; rewrite HΣ; intros w.
          vec nil w; auto.
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
    Proof using M'.
      split.
      + intros s _; exact (ψ (σ s)).
      + apply (fom_rels M').
    Defined.

    Abbreviation M := Σadd_cst_model.

    Local Fact completeness σ (A : 𝔽) φ ψ :
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
        rewrite <- HA with (φ := x·φ); unfold M; simpl; try tauto.
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

  Variable (Σ  : fo_signature) 
           (Σ0 : forall s, ar_syms Σ s = 0)
           (Σd : discrete (syms Σ)).


  Section syms_map.

    Variable A : fol_form Σ.

    Let ls := fol_syms A.
    Let K := list_discr_pos_n Σd ls.

    Let n := projT1 K.
    Let v : vec _ n := projT1 (projT2 K).
    Let g : _ -> option (pos n) := proj1_sig (projT2 (projT2 K)).

    Let HK := proj2_sig (projT2 (projT2 K)).

    Let H1 x : in_vec x v <-> In x ls.
    Proof. apply (proj1 HK). Qed.

    Let H2 x : In x ls <-> g x <> None.
    Proof. apply (proj1 (proj2 HK)). Qed.

    Let H3 p : g (vec_pos v p) = Some p.
    Proof. apply (proj1 (proj2 (proj2 HK))). Qed.

    Let H4 x p : g x = Some p -> vec_pos v p = x.
    Proof. apply (proj2 (proj2 (proj2 HK))). Qed.

    Let σ s := 
      match g s with 
        | Some p => pos2nat p
        | None   => 0
      end.

    Let f x : option (syms Σ) :=
      match le_lt_dec n x with
        | left _  => None
        | right H => Some (vec_pos v (nat2pos H))
      end.

    Let Hfσ s : In s ls -> f (σ s) = Some s.
    Proof.
      rewrite H2.
      unfold f, σ.
      generalize (H4 s).
      destruct (g s) as [ p | ].
      + intros E _.
        specialize (E _ eq_refl); subst.
        generalize (pos2nat_prop p).
        destruct (le_lt_dec n (pos2nat p)) as [ | H ].
        * intros; exfalso; lia.
        * rewrite nat2pos_pos2nat; auto.
      + intros _ []; auto.
    Qed.

    Local Fact syms_map : { σ  : syms Σ -> nat           & 
                          { f  : nat -> option (syms Σ)  |
                            forall s, In s ls -> f (σ s) = Some s } }.
    Proof using Σd. exists σ, f; auto. Qed.
 
  End syms_map.

  Hint Resolve incl_refl : core.

  Theorem Sig_rem_cst_dep_red A : { B | @fo_form_fin_dec_SAT Σ A <-> @fo_form_fin_dec_SAT (Σrem_cst Σ) B }.
  Proof using Σ0 Σd.
    generalize (fol_vars_max_spec A).
    set (m := fol_vars_max A); intros Hm.
    destruct (syms_map A) as (g & f & Hfg).
    set (σ s := g s + S m).
    exists (encode σ A).
    split.
    + intros (X & M & G1 & G2 & phi & G3).
      exists X, (Σrem_cst_model M), G1.
      exists. { intros r; simpl; apply G2. }
      set (psi n := 
        match le_lt_dec (S m) n with
          | left _  => 
          match f (n - S m) with 
            | Some s => fom_syms M s (cast ø (eq_sym (Σ0 _)))
            | None   => phi 0
          end
          | right _ => phi n 
        end).
      exists psi.
      revert G3; apply soundness with (HΣ := Σ0) (ls := fol_syms A); auto.
      * intros s Hs; unfold σ; intros H.
        apply Hm in H; lia.
      * intros n Hn; apply Hm in Hn.
        unfold psi.
        destruct (le_lt_dec (S m) n); try lia; auto.
      * intros s Hs.
        unfold psi, σ.
        apply Hfg in Hs. 
        replace (g s + S m - S m) with (g s) by lia.
        rewrite Hs.
        destruct (le_lt_dec (S m) (g s + S m)); auto; lia.
    + intros (X & M' & G1 & G2 & psi & G3).
      exists X, (Σadd_cst_model M' σ psi), G1.
      exists. { intros r; simpl; apply G2. }
      exists psi.
      revert G3; apply completeness with (ls := fol_syms A); auto.
      intros s Hs; unfold σ; intros H.
      apply Hm in H; lia.
  Qed.

End reduction.



