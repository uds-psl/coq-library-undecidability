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

Import fol_notations.

Set Implicit Arguments.

(* * Uniformize the arity of relations *)

Local Notation ø := vec_nil.

Section vec_fill_tail.

  Variable (X : Type) (n : nat) (k : nat) (v : vec X k) (e : X).

  Definition vec_fill_tail : vec X n.
  Proof using v e.
    apply vec_set_pos; intros p.
    destruct (le_lt_dec k (pos2nat p)) as [ | H ].
    + exact e.
    + exact (vec_pos v (nat2pos H)).
  Defined.

  Fact vec_fill_tail_lt p (Hp : pos2nat p < k) : vec_pos vec_fill_tail p = vec_pos v (nat2pos Hp).
  Proof.
    unfold vec_fill_tail; rew vec.
    destruct (le_lt_dec k (pos2nat p)).
    + exfalso; lia.
    + do 2 f_equal; apply lt_pirr.
  Qed.

  Fact vec_fill_tail_ge p : k <= pos2nat p -> vec_pos vec_fill_tail p = e.
  Proof.
    intros H; unfold vec_fill_tail; rew vec.
    destruct (le_lt_dec k (pos2nat p)); auto; exfalso; lia.
  Qed.

End vec_fill_tail.

Opaque vec_fill_tail.

Fact vec_map_fill_tail X Y (f : X -> Y) n k v e :
  vec_map f (@vec_fill_tail X n k v e) = vec_fill_tail n (vec_map f v) (f e).
Proof.
  apply vec_pos_ext; intros p; rew vec.
  destruct (le_lt_dec k (pos2nat p)) as [ | Hp ].
  + do 2 (rewrite vec_fill_tail_ge; auto).
  + do 2 rewrite vec_fill_tail_lt with (Hp := Hp); rew vec.
Qed.

Section vec_first_half.

  Variable (X : Type) (n : nat) (k : nat) (Hk : k <= n).

  Definition vec_first_half (v : vec X n) : vec X k.
  Proof using Hk.
    apply vec_set_pos; intros p.
    refine (vec_pos v (@nat2pos _ (pos2nat p) _)).
    apply Nat.lt_le_trans with (2 := Hk), pos2nat_prop.
  Defined.

  Fact vec_first_half_fill_tail v e : vec_first_half (vec_fill_tail _ v e) = v.
  Proof.
    apply vec_pos_ext; intros p.
    unfold vec_first_half; rew vec.
    match goal with 
      | |- vec_pos _ ?p = _ => assert (H : pos2nat p < k)
    end.
    { rewrite pos2nat_nat2pos; apply pos2nat_prop. }
    rewrite vec_fill_tail_lt with (Hp := H).
    revert H.
    rewrite pos2nat_nat2pos.
    intros; f_equal; apply nat2pos_pos2nat.
  Qed.

End vec_first_half.

Section Sig_uniformize_rels.

  Variable (Σ : fo_signature) (n : nat) (Hn : forall r, ar_rels Σ r <= n).

  Definition Σunif : fo_signature.
  Proof using Σ n.
    exists (syms Σ) (rels Σ).
    + exact (ar_syms Σ).
    + exact (fun _ => n).
  Defined.

  Notation Σ' := Σunif.

  Fixpoint fol_uniformize (A : fol_form Σ) : fol_form Σ' :=
    match A with
      | ⊥                => ⊥
      | @fol_atom _ r v  => @fol_atom Σ' r (vec_fill_tail _ v (£0))
      | fol_bin c A B    => fol_bin c (fol_uniformize A) (fol_uniformize B)
      | fol_quant q A    => fol_quant q (fol_uniformize A)
    end.

  Variable (X : Type) (e : X).

  Section soundness.

    Variables (M : fo_model Σ X).

    Local Definition fom_uniformize : fo_model Σ' X.
    Proof using M Hn.
      split.
      + intros s; apply (fom_syms M s).
      + intros r v; exact (fom_rels M r (vec_first_half (Hn r) v)).
    Defined.

    Notation M' := fom_uniformize.

    Theorem fol_uniformize_sound A φ : 
        fol_sem M φ A <-> fol_sem M' φ (fol_uniformize A).
    Proof.
      revert φ; induction A as [ | r v | A HA B HB | q A HA ]; simpl; try tauto; intros phi.
      + apply fol_equiv_ext; f_equal.
        rewrite vec_map_fill_tail, vec_first_half_fill_tail; auto.
      + apply fol_bin_sem_ext; auto.
      + apply fol_quant_sem_ext; auto.
    Qed.

  End soundness.

  Variable (lr : list (rels Σ)).

  Section completeness.
  
    Variable (M' : fo_model Σ' X).

    Local Definition fom_specialize : fo_model Σ X.
    Proof using M' e.
      split.
      + intros s; apply (fom_syms M' s).
      + intros r v; exact (fom_rels M' r (vec_fill_tail n v e)).
    Defined.

    Notation M := fom_specialize.

    Section uniform_after.

      Variable (r : rels Σ).

      Let k := ar_rels _ r.
      
      Let w1 : vec (fol_term Σ') _ := 
           vec_fill_tail n (vec_set_pos (fun p : pos k => £(2+pos2nat p))) (£ 1).
      Let w2 : vec (fol_term Σ') _ := 
           vec_fill_tail n (vec_set_pos (fun p : pos k => £(2+pos2nat p))) (£ 0).

      Local Definition fol_uniform_after : fol_form Σ' :=
           fol_mquant fol_fa k (∀∀ @fol_atom Σ' r w1 ↔ @fol_atom Σ' r w2).

      Local Fact fol_uniform_after_spec φ :
           fol_sem M' φ fol_uniform_after 
       <-> forall v e1 e2,  fom_rels M' r (@vec_fill_tail _ n k v e1) 
                        <-> fom_rels M' r (vec_fill_tail n v e2).
      Proof.
        unfold fol_uniform_after.
        rewrite fol_sem_mforall. 
        apply forall_equiv; intros v.
        rewrite fol_sem_quant_fix.
        apply forall_equiv; intros e1.
        rewrite fol_sem_quant_fix.
        apply forall_equiv; intros e2.
        apply fol_equiv_sem_ext.
        + apply fol_equiv_ext; f_equal.
          unfold w1; rewrite vec_map_fill_tail; simpl; f_equal.
          apply vec_pos_ext; intros p; rew vec; simpl.
          rewrite env_vlift_fix0; auto.
        + apply fol_equiv_ext; f_equal.
          unfold w2; rewrite vec_map_fill_tail; simpl; f_equal.
          apply vec_pos_ext; intros p; rew vec; simpl.
          rewrite env_vlift_fix0; auto.
      Qed.

    End uniform_after.

    Local Definition fol_all_uniform_after : fol_form Σ' :=
             fol_lconj (map fol_uniform_after lr).

    Let uniform := forall r, In r lr -> forall (v : vec _ (ar_rels _ r)) e1 e2, 
                            fom_rels M' r (vec_fill_tail n v e1) 
                        <-> fom_rels M' r (vec_fill_tail n v e2).
 
    Local Fact fol_all_uniform_after_spec φ : 
            fol_sem M' φ fol_all_uniform_after <-> uniform.
    Proof.
      unfold fol_all_uniform_after.
      rewrite fol_sem_lconj; unfold uniform.
      split.
      + intros H r Hr.
        apply (fol_uniform_after_spec _ φ), H, in_map_iff.
        exists r; auto.
      + intros H f; rewrite in_map_iff.
        intros (r & <- & Hr); apply fol_uniform_after_spec, H; auto.
    Qed. 

    Hypothesis Hlr : uniform.

    Theorem fol_uniformize_complete A φ : 
          incl (fol_rels A) lr
       -> fol_sem M φ A <-> fol_sem M' φ (fol_uniformize A).
    Proof using Hlr.
      revert φ; induction A as [ | r v | b A HA B HB | q A HA ]; simpl; try tauto; intros phi Hr.
      + rewrite vec_map_fill_tail; rew fot.
        apply Hlr, Hr; simpl; auto.
      + apply fol_bin_sem_ext; auto.
        * apply HA; intros ? ?; apply Hr, in_app_iff; auto.
        * apply HB; intros ? ?; apply Hr, in_app_iff; auto.
      + apply fol_quant_sem_ext; auto.
    Qed.

  End completeness.

  Variable (A : fol_form Σ) (HA : incl (fol_rels A) lr).

  Definition Σuniformize := fol_all_uniform_after ⟑ fol_uniformize A.

  Theorem Σuniformize_sound : fo_form_fin_dec_SAT_in A X
                           -> fo_form_fin_dec_SAT_in Σuniformize X.
  Proof using Hn.
    intros (M & H1 & H2 & phi & H).
    exists (fom_uniformize M), H1.
    exists.
    { intros ? ?; apply H2. }
    exists phi; split.
    + apply fol_all_uniform_after_spec.
      intros r _ v e1 e2; simpl.
      do 2 rewrite vec_first_half_fill_tail; tauto.
    + revert H; apply fol_uniformize_sound.
  Qed.

  Theorem Σuniformize_complete : fo_form_fin_dec_SAT_in Σuniformize X
                              -> fo_form_fin_dec_SAT_in A X.
  Proof using e HA.
    intros (M' & H1 & H2 & phi & H3 & H4).
    rewrite fol_all_uniform_after_spec in H3.
    exists (fom_specialize M'), H1.
    exists.
    { intros ? ?; apply H2. }
    exists phi.
    revert H4.
    apply fol_uniformize_complete; auto.
  Qed.

End Sig_uniformize_rels.
