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
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat discrete.

Set Implicit Arguments.

(** 1/ A is satisfiable in a fin/dec/interpreted model iff 
     f(A) if satisfiable in a fin/dec model

    2/ A is satisfiable in a fin/dec iff 
      f(A) if satisfiable in a fin/dec/interpreted model 

    for 2/ simply add an equality symbol that is not in A
    and do not use it and interpret it as =. f(A) is same
    as A but in an upgraded signature

    for 1/ A over Σ may contain an identity symbol e
    the idea ... given ls and lr containing the syms and rels
    belongs of A, and also e,  

    Of course if A is satisfiable interpreted that A is 
    satisfiable (uninterpreted). No suppose A is satisfiable
    uninterpreted, how can we ensure that e is interpreted
    by equality in the compressed model.

    For this we add formulas stating that e is a congruence
    for any on the symbols and rels in ls/lr so that in the
    compressed model, e will ensure bisimilarity and thus
    equality.

  *)

Section remove_interpreted.

  Variables (Σ : fo_signature) (e : rels Σ) (H_ae : ar_rels _ e = 2)
            (ls : list (syms Σ)) (lr : list (rels Σ))
            (He : In e lr). 

  Notation 𝕋 := (fo_term nat (ar_syms Σ)).
  Notation 𝔽 := (fol_form Σ).

  Notation "x ≡ y" := (fol_atom Σ e (eq_rect_r _ (x##y##ø) H_ae)) (at level 59).

  Section encode_congruence.

  Variable (X : Type) (M : fo_model Σ X).

  Notation "x ≈ y" := (fom_rels M e (eq_rect_r _ (x##y##ø) H_ae)).

  Local Fact fol_sem_e x y φ : fol_sem M φ (x ≡ y) = fo_term_sem (fom_syms M) φ x ≈ fo_term_sem (fom_syms M) φ y.
  Proof.
    simpl; f_equal.
    rewrite H_ae; unfold eq_rect_r; simpl; auto.
  Qed.

  Let fol_syms_e x y : fol_syms (x ≡ y) = fo_term_syms x ++ fo_term_syms y.
  Proof.
    simpl.
    rewrite H_ae; unfold eq_rect_r; simpl; auto.
    rewrite <- app_nil_end; auto.
  Qed.

  Let fol_rels_e x y : fol_rels (x ≡ y) = e::nil.
  Proof. auto. Qed.

  Local Definition fol_vec_equiv n := fol_vec_fa (vec_set_pos (fun p : pos n => £(pos2nat p+n) ≡ £(pos2nat p))).

  Local Fact fol_vec_equiv_syms n : incl (fol_syms (fol_vec_equiv n)) nil.
  Proof. 
    unfold fol_vec_equiv.
    rewrite fol_syms_vec_fa.
    intros x; rewrite in_flat_map.
    intros (D & HD & H); revert H.
    apply vec_list_inv in HD.
    destruct HD as (p & ->). 
    rew vec; rewrite fol_syms_e; simpl; tauto.
  Qed.

  Local Fact fol_vec_equiv_rels n : incl (fol_rels (fol_vec_equiv n)) (e::nil).
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
    apply forall_equiv; intros p; rew vec.
    rewrite fol_sem_e; simpl; tauto.
  Qed.

  Section congr_syms.

    Variable (s : syms Σ).

    Let n := ar_syms _ s.

    Let A := fol_vec_equiv n.
    Let f : 𝕋 := in_fot s (vec_set_pos (fun p => £(pos2nat p))).
    Let g : 𝕋 := in_fot s (vec_set_pos (fun p => £(pos2nat p+n))).
    Let B := g ≡ f.

    Let HrA : incl (fol_syms A) nil.       Proof. apply fol_vec_equiv_syms. Qed.
    Let HsA : incl (fol_rels A) (e::nil).  Proof. apply fol_vec_equiv_rels. Qed.

    Let HrB : incl (fol_syms B) (s::nil).
    Proof.
      unfold B; simpl.
      rewrite H_ae; unfold eq_rect_r.
      intros x; do 2 (simpl; rewrite in_app_iff).
      do 2 rewrite in_concat_iff.
      intros [ | [ (l & Hx & H) | [ | [ (l & Hx & H) | [] ] ] ] ]; try tauto; revert Hx;
        apply vec_list_inv in H; destruct H as (p & ->); rew vec.
    Qed.

    Let HsB : incl (fol_rels B) (e::nil).
    Proof. simpl; cbv; tauto. Qed.

    Definition congr_syms : 𝔽 := fol_mquant fol_fa n (fol_mquant fol_fa n (A ⤑  B)).

    Fact congr_syms_syms : incl (fol_syms congr_syms) (s::nil).
    Proof.
      unfold congr_syms.
      do 2 rewrite fol_syms_mquant.
      rewrite fol_syms_bin.
      apply incl_app; auto.
      intros x Hx; destruct (HrA _ Hx).
    Qed.

    Fact congr_syms_rels : incl (fol_rels congr_syms) (e::nil).
    Proof.
      unfold congr_syms.
      do 2 rewrite fol_rels_mquant.
      rewrite fol_rels_bin.
      apply incl_app; auto.
    Qed.

    Definition congr_syms_spec φ : 
             fol_sem M φ congr_syms
         <-> forall v w, (forall p, vec_pos v p ≈ vec_pos w p) -> fom_syms M s v ≈ fom_syms M s w.
    Proof.
      unfold congr_syms.
      rewrite fol_sem_mforall.
      apply forall_equiv; intros v.
      rewrite fol_sem_mforall.
      apply forall_equiv; intros w.
      rewrite fol_sem_bin_fix.
      apply (fol_bin_sem_ext fol_imp).
      + unfold A; rewrite fol_vec_equiv_sem.
        apply forall_equiv; intros p; rew vec; simpl.
        apply fol_equiv_ext; repeat f_equal.
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
    Let B := fol_atom Σ r (vec_set_pos (fun p => £(pos2nat p))).
    Let C := fol_atom Σ r (vec_set_pos (fun p => £(pos2nat p+n))).

    Let HsA : incl (fol_syms A) nil.       Proof. apply fol_vec_equiv_syms. Qed.
    Let HrA : incl (fol_rels A) (e::nil).  Proof. apply fol_vec_equiv_rels. Qed.

    Let HsB : incl (fol_syms B) nil.
    Proof.
      unfold B; simpl.
      intros x; rewrite in_flat_map.
      intros (t & H & Ht); revert Ht.
      apply vec_list_inv in H; destruct H as (p & ->); rew vec.
    Qed.

    Let HrB : incl (fol_rels B) (r::nil).
    Proof. simpl; cbv; tauto. Qed.

    Let HsC : incl (fol_syms C) nil.
    Proof. 
      unfold C; simpl.
      intros x; rewrite in_flat_map.
      intros (t & Ht & H); revert H.
      apply vec_list_inv in Ht.
      destruct Ht as (p & ->); rew vec; simpl; tauto.
    Qed.

    Let HrC : incl (fol_rels C) (e::r::nil).
    Proof. simpl; cbv; tauto. Qed.

    Definition congr_rels : 𝔽 := fol_mquant fol_fa n (fol_mquant fol_fa n (A ⤑  (C ↔ B))).

    Fact congr_rels_syms : incl (fol_syms congr_rels) nil.
    Proof.
      unfold congr_rels.
      do 2 rewrite fol_syms_mquant.
      repeat rewrite fol_syms_bin.
      repeat (apply incl_app; auto).
    Qed.

    Fact congr_rels_rels : incl (fol_rels congr_rels) (e::r::nil).
    Proof.
      unfold congr_rels.
      do 2 rewrite fol_rels_mquant.
      repeat rewrite fol_rels_bin.
      repeat (apply incl_app; auto).
      intros x Hx; destruct (HrA _ Hx); try subst x; simpl; tauto.
    Qed.

    Definition congr_rels_spec φ : 
             fol_sem M φ congr_rels
         <-> forall v w, (forall p, vec_pos v p ≈ vec_pos w p) 
                      -> fom_rels M r v <-> fom_rels M r w.
    Proof.
      unfold congr_rels.
      rewrite fol_sem_mforall.
      apply forall_equiv; intros v.
      rewrite fol_sem_mforall.
      apply forall_equiv; intros w.
      simpl fol_sem at 1.
      apply (fol_bin_sem_ext fol_imp).
      + unfold A; rewrite fol_vec_equiv_sem.
        apply forall_equiv; intros p; rew vec; simpl.
        apply fol_equiv_ext; repeat f_equal.
        * rewrite env_vlift_fix1, env_vlift_fix0; auto.
        * rewrite env_vlift_fix0; auto.
      + apply fol_equiv_sem_ext; apply fol_equiv_ext; f_equal;
          apply vec_pos_ext; intros p; rew vec; rew fot.
        * rewrite env_vlift_fix1, env_vlift_fix0; auto.
        * rewrite env_vlift_fix0; auto.
    Qed.

  End congr_rels.

  Definition Σ_eq_congruent : 𝔽 :=
    fol_lconj (map congr_syms ls) ⟑ fol_lconj (map congr_rels lr).

  Fact Σ_eq_congruent_syms : incl (fol_syms Σ_eq_congruent) ls.
  Proof.
    unfold Σ_eq_congruent.
    rewrite fol_syms_bin.
    unfold fol_lconj; repeat rewrite fol_syms_bigop; simpl.
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

  Fact Σ_eq_congruent_rels : incl (fol_rels Σ_eq_congruent) lr.
  Proof.
    unfold Σ_eq_congruent.
    rewrite fol_rels_bin.
    unfold fol_lconj; repeat rewrite fol_rels_bigop; simpl.
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

  (** Σ_eq_congruence_spec encodes that ≈ is a congruence wrt to all
      the symbols in ls and lr *)

  Fact Σ_eq_congruent_spec φ :
          fol_sem M φ Σ_eq_congruent
      <-> (forall s, In s ls -> forall v w, (forall p, vec_pos v p ≈ vec_pos w p) 
                                          -> fom_syms M s v ≈ fom_syms M s w)
       /\ (forall r, In r lr -> forall v w, (forall p, vec_pos v p ≈ vec_pos w p) 
                                          -> fom_rels M r v <-> fom_rels M r w).
  Proof.
    unfold Σ_eq_congruent.
    rewrite fol_sem_bin_fix.
    do 2 rewrite fol_sem_lconj.
    apply (fol_bin_sem_ext fol_conj).
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

  Definition Σ_eq_equivalence := 
                           (∀(£0 ≡ £0)) 
                         ⟑ (∀(∀(£1 ≡ £0 ⤑ £0 ≡ £1)))
                         ⟑ (∀(∀(∀(£2 ≡ £1 ⤑ £1 ≡ £0 ⤑ £2 ≡ £0)))).
  
  Fact Σ_eq_equiv_spec φ : 
           fol_sem M φ Σ_eq_equivalence
       <-> (forall x, x ≈ x)
        /\ (forall x y, x ≈ y -> y ≈ x)
        /\ (forall x y z, x ≈ y -> y ≈ z -> x ≈ z).
  Proof.
    unfold Σ_eq_equivalence.
    repeat (rewrite fol_sem_bin_fix).
    repeat apply fol_bin_sem_ext.
    + rewrite fol_sem_quant_fix; apply forall_equiv; intro.
      rewrite fol_sem_e; simpl; tauto.
    + do 2 (rewrite fol_sem_quant_fix; apply forall_equiv; intro).
      rewrite fol_sem_bin_fix.
      do 2 rewrite fol_sem_e; simpl; tauto.
    + do 3 (rewrite fol_sem_quant_fix; apply forall_equiv; intro).
      do 2 rewrite fol_sem_bin_fix.
      do 3 rewrite fol_sem_e; simpl; tauto.
  Qed.

  Fact Σ_eq_equivalence_syms : fol_syms Σ_eq_equivalence = nil.
  Proof.
    unfold Σ_eq_equivalence.
    repeat (rewrite fol_syms_bin || rewrite fol_syms_quant).
    repeat rewrite fol_syms_e; auto.
  Qed.

  Fact Σ_eq_equivalence_rels : incl (fol_rels Σ_eq_equivalence) (e::nil).
  Proof. simpl; cbv; tauto. Qed.

  Definition Σ_eq_congruence := Σ_eq_congruent ⟑ Σ_eq_equivalence.

  Fact Σ_eq_congruence_syms : incl (fol_syms Σ_eq_congruence) ls.
  Proof.
    unfold Σ_eq_congruence.
    rewrite fol_syms_bin, Σ_eq_equivalence_syms, <- app_nil_end.
    apply Σ_eq_congruent_syms.
  Qed.

  Fact Σ_eq_congruence_rels : incl (fol_rels Σ_eq_congruence) lr.
  Proof.
    unfold Σ_eq_congruence.
    rewrite fol_rels_bin.
    apply incl_app.
    + apply Σ_eq_congruent_rels.
    + intros x Hx.
      apply Σ_eq_equivalence_rels in Hx.
      destruct Hx as [ | [] ]; subst; auto.
  Qed.

  Variable φ : nat -> X.

  Hypothesis Xfin : finite_t X.
  Hypothesis Mdec : fo_model_dec M.
  Hypothesis eq_congr : fol_sem M φ Σ_eq_congruence.

  Infix "~b" := (@fo_bisimilar Σ ls lr _ M) (at level 70, no associativity).

  Fact eq_bisim x y : x ≈ y <-> x ~b y.
  Proof.
    split.
    + destruct eq_congr as (H1 & H2).
      apply Σ_eq_congruent_spec in H1.
      apply Σ_eq_equiv_spec in H2.
      rewrite <- fom_eq_fol_characterization; auto.
      revert x y; apply fom_eq_incl.
      intros x y H; split.
      * intros s Hs v p.
        apply H1; simpl; auto.
        intros q; destruct (pos_eq_dec p q); rew vec; auto.
        apply (proj1 H2).
      * intros r' Hr v p; apply H1; auto.
        intros q; destruct (pos_eq_dec p q); rew vec; auto.
        apply (proj1 H2).
    + intros H.
      specialize (H (£1 ≡ £0) (fun n => match n with 0 => x | _ => y end)).
      do 2 rewrite fol_sem_e in H; apply H.
      * rewrite fol_syms_e; simpl; intros _ [].
      * rewrite fol_rels_e; intros x' [ | [] ]; try subst x'; auto.
      * apply proj2, Σ_eq_equiv_spec in eq_congr.
        apply (proj1 eq_congr).
  Qed.

  End encode_congruence.

  Definition Σ_noeq A := Σ_eq_congruence ⟑ A.

  Section soundness.

    Variable (A : 𝔽) (X : Type).

    Theorem Σ_noeq_sound : fo_form_fin_dec_eq_SAT_in _ H_ae A X
                        -> fo_form_fin_dec_SAT_in (Σ_noeq A) X.
    Proof.
      intros (M & H1 & H2 & HE & phi & H5).
      exists M, H1, H2, phi; unfold Σ_noeq.
      rewrite fol_sem_bin_fix; split; auto.
      split; [ | msplit 2 ].
      + rewrite Σ_eq_congruent_spec; split.
        * intros s _ v w H; rewrite HE.
          f_equal; apply vec_pos_ext; intros p.
          apply HE, H.
        * intros r _ v w H.
          apply fol_equiv_ext; f_equal.
          apply vec_pos_ext; intros p.
          apply HE, H.
      + intros ?; rewrite fol_sem_e, HE; auto.
      + intros ? ?; rewrite fol_sem_bin_fix.
        do 2 rewrite fol_sem_e; simpl.
        now repeat rewrite HE.
      + intros ? ? ?; repeat rewrite fol_sem_bin_fix.
        do 3 rewrite fol_sem_e; simpl.
        repeat rewrite HE; intros; subst; auto.
    Qed.

  End soundness.

  Section completeness.

    Variable (A : 𝔽) 
             (HA1 : incl (fol_syms A) ls) 
             (HA2 : incl (fol_rels A) lr). 

    Theorem Σ_noeq_complete : fo_form_fin_dec_SAT (Σ_noeq A)
                           -> fo_form_fin_dec_eq_SAT e H_ae A.
    Proof.
      intros (X & M & H1 & H2 & phi & H5 & H6).
      destruct (fo_fin_model_discretize ls lr H1 H2)
        as (n & Mn & Mdec & p & H).
      assert (fol_sem Mn (fun n => p (phi n)) (Σ_eq_congruence)) as H5'.
      { revert H5; apply fo_model_projection with (p := p).
        + intros; auto.
        + apply Σ_eq_congruence_syms.
        + intros x Hx.
          apply Σ_eq_congruence_rels in Hx; simpl; auto. }
      generalize (eq_bisim (finite_t_pos _) Mdec H5'); intros H7.
      exists (pos n), Mn, (finite_t_pos _), Mdec.
      exists.
      { intros x y; simpl; rewrite H7, H; tauto. } 
      exists (fun n => p (phi n)).
      revert H6; apply fo_model_projection with (p := p); auto.
    Qed.

  End completeness.

End remove_interpreted.
