(**************************************************************)
(*   Copyright Dominik Kirst              [+]                 *)
(*             Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [+] Affiliation U. Sarrbrucken *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** The code was initially developed by Dominik Kirst to be 
    reimported to this alternate syntax & framework by @DLW 
*) 

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_terms fo_logic.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Local Definition cast X n k (v : vec X n) (H : n = k) : vec X k := eq_rect _ (vec X) v _ H.

Local Lemma cast_refl X n (v : vec X n) : cast v eq_refl = v.
Proof. reflexivity. Qed.

Section Uniform_arities_to_one.

  Variable (Σ : fo_signature) 
           (HΣ : syms Σ -> False)
           (a : nat) (Ha : forall r, ar_rels Σ r = a).

  Definition Σone_rel : fo_signature.
  Proof.
    exists (rels Σ) unit.
    + exact (fun _ => 0).
    + exact (fun _ => S a).
  Defined.

  Notation Σ' := Σone_rel.

  Let convert_t (t : fo_term nat (ar_syms Σ)) : fo_term nat (ar_syms Σ') :=
    match t with
    | in_var s   => in_var s
    | in_fot s _ => False_rect _ (HΣ s)
    end.

  Let convert_v n (v : vec _ n) := vec_map convert_t v.

  Fixpoint Σunif_one_rel (phi : fol_form Σ) : fol_form Σ' :=
    match phi with
    | ⊥              => ⊥
    | fol_atom _ r v => fol_atom Σ' tt (in_fot r ø##cast (convert_v v) (Ha _))
    | fol_bin b A B  => fol_bin b (Σunif_one_rel A) (Σunif_one_rel B)
    | fol_quant q A  => fol_quant q (Σunif_one_rel A)
    end.

  Notation encode := Σunif_one_rel.

  (* Direction 1: sat phi -> sat (encode phi) *)

  Section to_compr.

    Variable (X : Type) (M : fo_model Σ X) (x0 : X).

    Local Definition fD (x : X + rels Σ) : X := match x with inl x => x | inr _ => x0 end.

    Local Definition vec_fill n (v : vec _ n) := vec_map fD v.

    Local Fact vec_fill_inl n v : @vec_fill n (vec_map inl v) = v.
    Proof.
      unfold vec_fill.
      rewrite vec_map_map.
      apply vec_pos_ext; intro; rew vec.
    Qed.

    Definition Σunif_one_rel_model : fo_model Σ' (X + rels Σ).
    Proof.
      split.
      + intros r _; right; exact r.
      + intros []; simpl; intros v.
        exact (match vec_head v with
          | inl _ => True
          | inr r => fom_rels M r (cast (vec_fill (vec_tail v)) (eq_sym (Ha _))) 
        end).
    Defined.

    Notation M' := Σunif_one_rel_model.

    Let convert_env (φ : nat -> X) n : X + rels Σ := inl (φ n).

    Notation "⟦ t ⟧" := (fun φ => fo_term_sem (fom_syms M) φ t).
    Notation "⟦ t ⟧'" := (fun φ => fo_term_sem (fom_syms M') φ t) (at level 1, format "⟦ t ⟧'").

    Local Fact fot_sem_to_compr φ t : ⟦convert_t t⟧' (convert_env φ) = inl (⟦t⟧ φ).
    Proof. destruct t as [x | f v]; trivial; exfalso; auto. Qed.

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun φ => fol_sem M' φ A) (at level 1, format "⟪ A ⟫'").

    Let env_fill (φ : nat -> X + rels Σ) n : X + rels Σ := inl (fD (φ n)).

    Let env_fill_sat_help A φ x :
          ⟪encode A⟫' (env_fill (env_fill φ)↑x) 
      <-> ⟪encode A⟫' (env_fill (φ↑x)).
    Proof. apply fol_sem_ext; intros [] _; auto. Qed.

    Let env_fill_sat A φ : ⟪encode A⟫' (env_fill φ) <-> ⟪encode A⟫' φ.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in φ |- *; try tauto. 
      - simpl; rewrite <- (Ha r), !cast_refl. 
        unfold vec_fill, convert_v; rewrite !vec_map_map.
        apply fol_equiv_ext; f_equal.
        apply vec_pos_ext; intros p; rew vec.
        generalize (vec_pos v p).
        intros []; simpl; auto; exfalso; auto.
      - apply fol_bin_sem_ext; auto. 
      - simpl; apply fol_quant_sem_ext; intro; auto.
        rewrite <- HA, env_fill_sat_help, HA; tauto.
    Qed.

    Lemma Σunif_one_rel_sound A φ : ⟪A⟫ φ <-> ⟪encode A⟫' (convert_env φ).
    Proof.
      induction A as [ | r v | b A HA B HB | [] A HA ] in φ |- *; 
        try tauto.
      - cbn; rewrite <- (Ha r), !cast_refl.
        unfold convert_v; rewrite !vec_map_map.
        apply fol_equiv_ext; f_equal.
        apply vec_pos_ext; intros p; rew vec.
        generalize (vec_pos v p).
        intros [ n | s w ]; simpl; auto; exfalso; auto.
      - apply fol_bin_sem_ext; auto.
      - simpl; split.
        * intros (x & Hx); exists (inl x). 
          revert Hx; rewrite HA; apply fol_sem_ext.
          intros []; simpl; auto.
        * intros ( [x | r] & H).
          + exists x. 
            revert H; rewrite HA; apply fol_sem_ext.
            intros []; simpl; auto.
          + exists x0.
            apply HA; revert H.
            rewrite <- env_fill_sat.
            apply fol_sem_ext.
            intros []; simpl; auto.
      - simpl; split.
        * intros H [ x | r ].
          + generalize (H x); rewrite HA.
            apply fol_sem_ext.
            intros []; simpl; auto.
          + generalize (H x0).
            rewrite <- env_fill_sat, HA; apply fol_sem_ext.
            intros []; simpl; auto.
        * intros H x.
          generalize (H (inl x)).
          rewrite HA; apply fol_sem_ext.
          intros []; simpl; auto.
    Qed.

  End to_compr.

  Section from_compr.

    Variable (X : Type) (M' : fo_model Σ' X).

    Definition Σone_unif_rel_model : fo_model Σ X.
    Proof.
      split.
      + intros ? _; exfalso; auto.
      + exact (fun r v => fom_rels M' tt (fom_syms M' r ø##cast v (Ha _))).
    Defined.

    Notation M := Σone_unif_rel_model.

    Notation "⟦ t ⟧" := (fun φ => fo_term_sem (fom_syms M) φ t).
    Notation "⟦ t ⟧'" := (fun φ => fo_term_sem (fom_syms M') φ t) (at level 1, format "⟦ t ⟧'").

    Let eval_from_compr φ : forall t, ⟦t⟧ φ = ⟦convert_t t⟧' φ.
    Proof. intros []; simpl; auto; exfalso; auto. Qed.

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun φ => fol_sem M' φ A) (at level 1, format "⟪ A ⟫'").

    Lemma Σunif_one_rel_complete A φ : ⟪A⟫ φ <-> ⟪encode A⟫' φ.
    Proof.
      induction A as [ | r v | | ] in φ |- *; cbn; try firstorder tauto.
      + apply fol_equiv_ext; do 2 f_equal.
        revert v; generalize (Ha r); rewrite Ha; intros E v. 
        rewrite eq_nat_uniq with (H := E).
        unfold convert_v; rewrite !cast_refl, vec_map_map.
        apply vec_pos_ext; intro; rew vec.
      + apply fol_bin_sem_ext; auto.
      + apply fol_quant_sem_ext; intro; auto.
    Qed.

  End from_compr.

End Uniform_arities_to_one.
