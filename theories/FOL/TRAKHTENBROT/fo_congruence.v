(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia Relations.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic.

Import fol_notations.

Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationHints.

Set Implicit Arguments.

Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊑" := incl (at level 70, no associativity). 
Local Abbreviation ø := vec_nil.

(* * First order theory of congruences *)

Section congruence.

  Variables (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
            (X : Type) (M : fo_model Σ X)
            (R : X -> X -> Prop).

  Infix "≈" := R.

  Definition Σ_congruence_wrt :=
          (forall s, s ∊ ls -> forall v w, (forall p, vec_pos v p ≈ vec_pos w p) 
                                          -> fom_syms M s v ≈ fom_syms M s w)
       /\ (forall r, r ∊ lr -> forall v w, (forall p, vec_pos v p ≈ vec_pos w p) 
                                          -> fom_rels M r v <-> fom_rels M r w).

End congruence.

Section fol_congruence.

  Variables (Σ : fo_signature) (e : rels Σ) (H_ae : ar_rels _ e = 2)
            (ls : list (syms Σ)) (lr : list (rels Σ))
            (He : e ∊ lr). 

  Abbreviation 𝕋 := (fol_term Σ).
  Abbreviation 𝔽 := (fol_form Σ).

  Notation "x ≡ y" := (@fol_atom Σ e (cast (x##y##ø) (eq_sym H_ae))) (at level 59).

  Section encode_congruence.

    Variable (X : Type) (M : fo_model Σ X).

    Notation "x ≈ y" := (fom_rels M e (cast (x##y##ø) (eq_sym H_ae))).

    Local Fact fol_sem_e x y φ : fol_sem M φ (x ≡ y) = fo_term_sem M φ x ≈ fo_term_sem M φ y.
    Proof. simpl; f_equal; rewrite H_ae; simpl; auto. Qed.

    Let fol_syms_e x y : fol_syms (x ≡ y) = fo_term_syms x ++ fo_term_syms y.
    Proof. simpl; rewrite H_ae; simpl; auto; rewrite app_nil_r; auto. Qed.

    Let fol_rels_e x y : fol_rels (x ≡ y) = e::nil.
    Proof. auto. Qed.

    Local Definition fol_vec_equiv n := fol_vec_fa (vec_set_pos (fun p : pos n => £(pos2nat p+n) ≡ £(pos2nat p))).

    Local Fact fol_vec_equiv_syms n : fol_syms (fol_vec_equiv n) ⊑ nil.
    Proof. 
      unfold fol_vec_equiv.
      rewrite fol_syms_vec_fa.
      intros x; rewrite in_flat_map.
      intros (D & HD & H); revert H.
      apply vec_list_inv in HD.
      destruct HD as (p & ->). 
      rew vec; rewrite fol_syms_e; simpl; tauto.
    Qed.

    Local Fact fol_vec_equiv_rels n : fol_rels (fol_vec_equiv n) ⊑ e::nil.
    Proof. 
      unfold fol_vec_equiv.
      rewrite fol_rels_vec_fa.
      intros x; rewrite in_flat_map.
      intros (D & HD & H); revert H.
      apply vec_list_inv in HD.
      destruct HD as (p & ->); rew vec.
    Qed.

    Local Fact fol_vec_equiv_sem n φ : 
                fol_sem M φ (fol_vec_equiv n)
            <-> (forall p : pos n, φ (pos2nat p+n) ≈ φ (pos2nat p)).
    Proof.
      unfold fol_vec_equiv.
      rewrite fol_sem_vec_fa.
      fol equiv; intros p; rew vec.
      rewrite fol_sem_e; simpl; tauto.
    Qed.

    Section congr_syms.

      Variable (s : syms Σ).

      Let n := ar_syms _ s.

      Let A := fol_vec_equiv n.
      Let f : 𝕋 := in_fot s (vec_set_pos (fun p => £(pos2nat p))).
      Let g : 𝕋 := in_fot s (vec_set_pos (fun p => £(pos2nat p+n))).
      Let B := g ≡ f.

      Let HrA : fol_syms A ⊑ nil.     Proof. apply fol_vec_equiv_syms. Qed.
      Let HsA : fol_rels A ⊑ e::nil.  Proof. apply fol_vec_equiv_rels. Qed.

      Let HrB : fol_syms B ⊑ s::nil.
      Proof.
        unfold B; simpl.
        rewrite H_ae; unfold eq_rect_r.
        intros x; do 2 (simpl; rewrite in_app_iff).
        do 2 rewrite in_concat_iff.
        intros [ | [ (l & Hx & H) | [ | [ (l & Hx & H) | [] ] ] ] ]; try tauto; revert Hx;
          apply vec_list_inv in H; destruct H as (p & ->); rew vec.
      Qed.

      Let HsB : fol_rels B ⊑ e::nil.
      Proof. simpl; cbv; tauto. Qed.

      Local Definition congr_syms : 𝔽 := fol_mquant fol_fa n (fol_mquant fol_fa n (A ⤑  B)).

      Local Fact congr_syms_syms : fol_syms congr_syms ⊑ s::nil.
      Proof.
        unfold congr_syms.
        do 2 rewrite fol_syms_mquant.
        rewrite fol_syms_bin.
        apply incl_app; auto.
      Qed.

      Local Fact congr_syms_rels : fol_rels congr_syms ⊑ e::nil.
      Proof.
        unfold congr_syms.
        do 2 rewrite fol_rels_mquant.
        rewrite fol_rels_bin.
        apply incl_app; auto.
      Qed.

      Local Definition congr_syms_spec φ : 
               fol_sem M φ congr_syms
           <-> forall v w, (forall p, vec_pos v p ≈ vec_pos w p) -> fom_syms M s v ≈ fom_syms M s w.
      Proof.
        unfold congr_syms.
        rewrite fol_sem_mforall.
        fol equiv; intros v.
        rewrite fol_sem_mforall.
        fol equiv; intros w.
        rewrite fol_sem_bin_fix.
        fol equiv imp.
        + unfold A; rewrite fol_vec_equiv_sem.
          fol equiv; intros p; rew vec; simpl.
          fol equiv; repeat f_equal.
          * rewrite env_vlift_fix1, env_vlift_fix0; auto.
          * rewrite env_vlift_fix0; auto.
        + unfold B.
          rewrite fol_sem_e; simpl. 
          apply fol_equiv_ext; repeat f_equal; 
            apply vec_pos_ext; intros p; rew vec; rew fot.
          * rewrite env_vlift_fix1, env_vlift_fix0; auto.
          * rewrite env_vlift_fix0; auto.
      Qed.

    End congr_syms.

    Section congr_rels.

      Variable (r : rels Σ).

      Let n := ar_rels _ r.

      Let A := fol_vec_equiv n.
      Let B := @fol_atom Σ r (vec_set_pos (fun p => £(pos2nat p))).
      Let C := @fol_atom Σ r (vec_set_pos (fun p => £(pos2nat p+n))).

      Let HsA : fol_syms A ⊑ nil.     Proof. apply fol_vec_equiv_syms. Qed.
      Let HrA : fol_rels A ⊑ e::nil.  Proof. apply fol_vec_equiv_rels. Qed.

      Let HsB : fol_syms B ⊑ nil.
      Proof.
        unfold B; simpl.
        intros x; rewrite in_flat_map.
        intros (t & H & Ht); revert Ht.
        apply vec_list_inv in H; destruct H as (p & ->); rew vec.
      Qed.

      Let HrB : fol_rels B ⊑ r::nil.
      Proof. simpl; cbv; tauto. Qed.

      Let HsC : fol_syms C ⊑ nil.
      Proof. 
        unfold C; simpl.
        intros x; rewrite in_flat_map.
        intros (t & Ht & H); revert H.
        apply vec_list_inv in Ht.
        destruct Ht as (p & ->); rew vec; simpl; tauto.
      Qed.

      Let HrC : fol_rels C ⊑ e::r::nil.
      Proof. simpl; cbv; tauto. Qed.

      Local Definition congr_rels : 𝔽 := fol_mquant fol_fa n (fol_mquant fol_fa n (A ⤑  (C ↔ B))).

      Local Fact congr_rels_syms : fol_syms congr_rels ⊑ nil.
      Proof.
        unfold congr_rels.
        do 2 rewrite fol_syms_mquant.
        repeat rewrite fol_syms_bin.
        repeat (apply incl_app; auto).
      Qed.

      Local Fact congr_rels_rels : fol_rels congr_rels ⊑ e::r::nil.
      Proof.
        unfold congr_rels.
        do 2 rewrite fol_rels_mquant.
        repeat rewrite fol_rels_bin.
        repeat (apply incl_app; auto).
        intros x Hx; destruct (HrA _ Hx); try subst x; simpl; tauto.
      Qed.

      Local Definition congr_rels_spec φ : 
             fol_sem M φ congr_rels
         <-> forall v w, (forall p, vec_pos v p ≈ vec_pos w p) 
                      -> fom_rels M r v <-> fom_rels M r w.
      Proof.
        unfold congr_rels.
        rewrite fol_sem_mforall.
        fol equiv; intros v.
        rewrite fol_sem_mforall.
        fol equiv; intros w.
        simpl fol_sem at 1.
        fol equiv.
        + unfold A; rewrite fol_vec_equiv_sem.
          fol equiv; intros p; rew vec; simpl.
          fol equiv; repeat f_equal.
          * rewrite env_vlift_fix1, env_vlift_fix0; auto.
          * rewrite env_vlift_fix0; auto.
        + fol equiv iff; fol equiv; f_equal;
            apply vec_pos_ext; intros p; rew vec; rew fot.
          * rewrite env_vlift_fix1, env_vlift_fix0; auto.
          * rewrite env_vlift_fix0; auto.
      Qed.

    End congr_rels.

    Local Definition fol_congruent : 𝔽 :=
        fol_lconj (map congr_syms ls) 
      ⟑ fol_lconj (map congr_rels lr).

    Local Fact fol_congruent_syms : fol_syms fol_congruent ⊑ ls.
    Proof.
      unfold fol_congruent.
      rewrite fol_syms_bin.
      repeat rewrite fol_syms_bigop; simpl.
      repeat apply incl_app; try (cbv; tauto).
      + intros s; rewrite in_flat_map.
        intros (A & HA & H); revert HA H.
        rewrite in_map_iff; intros (x & <- & Hx) H.
        apply congr_syms_syms in H; revert H.
        intros [ <- | [] ]; auto.
      + intros r; rewrite in_flat_map.
        intros (A & HA & H); revert HA H.
        rewrite in_map_iff; intros (x & <- & Hx) H.
        apply congr_rels_syms in H; revert H.
        intros [].
    Qed.

    Local Fact fol_congruent_rels : fol_rels fol_congruent ⊑ lr.
    Proof using He.
      unfold fol_congruent.
      rewrite fol_rels_bin.
      repeat rewrite fol_rels_bigop; simpl.
      repeat apply incl_app; try (cbv; tauto).
      + intros s; rewrite in_flat_map.
        intros (A & HA & H); revert HA H.
        rewrite in_map_iff; intros (x & <- & Hx) H.
        apply congr_syms_rels in H; revert H.
        intros [ <- | [] ]; simpl; auto.
      + intros x; simpl.
        rewrite in_flat_map.
        intros (A & HA & H); revert HA H.
        rewrite in_map_iff; intros (y & <- & Hy) H.
        apply congr_rels_rels in H; revert H.
        intros [ | [ <- | [] ] ]; subst; auto.
    Qed.

    (* Σ_eq_congruence_spec encodes that ≈ is a congruence wrt to all
        the symbols in ls and lr *)

    Local Fact fol_congruent_spec φ :
          fol_sem M φ fol_congruent 
      <-> Σ_congruence_wrt ls lr M (fun x y => x ≈ y).
    Proof.
      unfold fol_congruent.
      rewrite fol_sem_bin_fix.
      do 2 rewrite fol_sem_lconj.
      fol equiv conj.
      + split.
        * intros H s Hs.
          apply (congr_syms_spec _ φ), H, in_map_iff.
          exists s; auto.
        * intros H f; rewrite in_map_iff.
          intros (s & <- & Hs).
          apply congr_syms_spec, H; auto.
      + split.
        * intros H r Hr.
          apply (congr_rels_spec _ φ), H, in_map_iff.
          exists r; auto.
        * intros H f; rewrite in_map_iff.
          intros (r & <- & Hr).
          apply congr_rels_spec, H; auto.
    Qed.

    Local Definition fol_equivalence := 
            (∀₁ £0 ≡ £0)
          ⟑ (∀₁∀₁∀₁ £2 ≡ £1 ⤑ £1 ≡ £0 ⤑ £2 ≡ £0)
          ⟑ (∀₁∀₁ £1 ≡ £0 ⤑ £0 ≡ £1).

    Local Fact fol_equivalence_syms : fol_syms fol_equivalence = nil.
    Proof.
      unfold fol_equivalence.
      repeat (rewrite fol_syms_bin || rewrite fol_syms_quant).
      repeat rewrite fol_syms_e; auto.
    Qed.

    Local Fact fol_equivalence_rels : fol_rels fol_equivalence ⊑ e::nil.
    Proof. simpl; cbv; tauto. Qed.
  
    Fact fol_equiv_spec φ : 
           fol_sem M φ fol_equivalence <-> equiv _ (fun x y => x ≈ y).
    Proof.
      unfold fol_equivalence.
      repeat (rewrite fol_sem_bin_fix).
      repeat fol equiv conj.
      + rewrite fol_sem_quant_fix; apply forall_equiv; intro.
        rewrite fol_sem_e; simpl; tauto.
      + do 3 (rewrite fol_sem_quant_fix; apply forall_equiv; intro).
        do 2 rewrite fol_sem_bin_fix.
        do 3 rewrite fol_sem_e; simpl; tauto.
      + do 2 (rewrite fol_sem_quant_fix; apply forall_equiv; intro).
        rewrite fol_sem_bin_fix.
        do 2 rewrite fol_sem_e; simpl; tauto.
    Qed.

    (* Σ_eq_congruence encodes the fact that ≈ is a congruence wrt to all
        the symbols in ls and lr and this formula involve only the symbols
        of ls and lr, under the assumption that e belongs to lr *)

    Definition fol_congruence := 
          fol_congruent 
        ⟑ fol_equivalence.

    Fact fol_congruence_syms : fol_syms fol_congruence ⊑ ls.
    Proof.
      unfold fol_congruence.
      rewrite fol_syms_bin, fol_equivalence_syms, app_nil_r.
      apply fol_congruent_syms.
    Qed.

    Fact fol_congruence_rels : fol_rels fol_congruence ⊑ lr.
    Proof using He.
      unfold fol_congruence.
      rewrite fol_rels_bin.
      apply incl_app.
      + apply fol_congruent_rels.
      + intros x Hx.
        apply fol_equivalence_rels in Hx.
        destruct Hx as [ | [] ]; subst; auto.
    Qed.

    Fact fol_sem_congruence φ : 
             fol_sem M φ fol_congruence
         <-> Σ_congruence_wrt ls lr M (fun x y => x ≈ y)
          /\ equiv _ (fun x y => x ≈ y).
    Proof.
      fol equiv conj.
      + apply fol_congruent_spec.
      + apply fol_equiv_spec.
    Qed.

  End encode_congruence.

End fol_congruence.

Arguments fol_congruence { _ _ }.
