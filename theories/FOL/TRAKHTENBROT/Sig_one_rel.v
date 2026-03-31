(**************************************************************)
(*   Copyright Dominik Kirst              [+]                 *)
(*             Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [+] Affiliation U. Sarrbrucken *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The code was initially developed by Dominik Kirst to be 
    reimported to this alternate syntax & framework by @DLW 
*) 

From Stdlib Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic.

Import fol_notations.

Set Implicit Arguments.

(* * From several relations to one, arity incremented by 1 *)

Local Reserved Notation "⟪ A ⟫'" (at level 0, format "⟪ A ⟫'").

Local Abbreviation ø := vec_nil.

Section Uniform_arities_to_one.

  Variable (Σ : fo_signature) 
           (HΣ : syms Σ -> False)
           (a : nat) (Ha : forall r, ar_rels Σ r = a).

  Definition Σone_rel : fo_signature.
  Proof using Σ a.
    exists (rels Σ) unit.
    + exact (fun _ => 0).
    + exact (fun _ => S a).
  Defined.

  Abbreviation Σ' := Σone_rel.

  Abbreviation 𝕋 := (fol_term Σ).
  Abbreviation 𝔽 := (fol_form Σ).

  Abbreviation 𝕋' := (fol_term Σ').
  Abbreviation 𝔽' := (fol_form Σ').

  Let convert_t (t : 𝕋) : 𝕋' :=
    match t with
    | in_var s   => in_var s
    | in_fot s _ => False_rect _ (HΣ s)
    end.

  Let convert_v n (v : vec _ n) := vec_map convert_t v.

  Fixpoint Σunif_one_rel (A : 𝔽) : 𝔽' :=
    match A with
    | ⊥              => ⊥
    | fol_atom r v   => @fol_atom Σ' tt (in_fot r ø##cast (convert_v v) (Ha _))
    | fol_bin b A B  => fol_bin b (Σunif_one_rel A) (Σunif_one_rel B)
    | fol_quant q A  => fol_quant q (Σunif_one_rel A)
    end.

  Abbreviation encode := Σunif_one_rel.
  
  Variable X : Type.

  Section soundness.

    Variable (M : fo_model Σ X) (x0 : X).

    Abbreviation X' := (X + rels Σ)%type.

    Let fX (x : X') : X := 
      match x with 
        | inl x => x 
        | inr _ => x0 
      end.

    Let vX n (v : vec _ n) := vec_map fX v.

    (* The base type of the model X is extended with finitely
        many points (rels Σ) that serve as indices for the
        original relations and are linked to corresponding
        constants *)

    Definition Σunif_one_rel_model : fo_model Σ' X'.
    Proof using Ha M x0.
      split.
      + exact (fun r _ => inr r).
      + exact (fun r v => 
          match vec_head v with
            | inl _    => False           (* arbitrary value here *)
            | inr r    => fom_rels M r (cast (vX (vec_tail v)) (eq_sym (Ha _)))
          end).
    Defined.

    Abbreviation M' := Σunif_one_rel_model.

    Let convert_env (φ : nat -> X) n : X' := inl (φ n).
    Let env_fill (ψ : nat -> X') n : X' := inl (fX (ψ n)).

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).

    Let env_fill_sat_help A ψ x :
          ⟪encode A⟫' (env_fill x·(env_fill ψ)) 
      <-> ⟪encode A⟫' (env_fill x·ψ).
    Proof. apply fol_sem_ext; intros [] _; auto. Qed.

    Let env_fill_sat A ψ : ⟪encode A⟫' (env_fill ψ) <-> ⟪encode A⟫' ψ.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in ψ |- *; try tauto. 
      - simpl; rewrite <- (Ha r), !cast_refl. 
        unfold vX, convert_v; rewrite !vec_map_map.
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

  End soundness.

  Section completeness.

    Variable (M' : fo_model Σ' X).

    (* The model is recovered using constants as indices for each relation *)

    Definition Σone_unif_rel_model : fo_model Σ X.
    Proof using M' Ha HΣ.
      split.
      + intros ? _; exfalso; auto.
      + exact (fun r v => fom_rels M' tt (fom_syms M' r ø##cast v (Ha _))).
    Defined.

    Abbreviation M := Σone_unif_rel_model.

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).

    Lemma Σunif_one_rel_complete A φ : ⟪A⟫ φ <-> ⟪encode A⟫' φ.
    Proof.
      induction A as [ | r v | | ] in φ |- *; cbn; try tauto.
      + apply fol_equiv_ext; do 2 f_equal.
        revert v; generalize (Ha r); rewrite Ha; intros E v. 
        rewrite eq_nat_uniq with (H := E).
        unfold convert_v; rewrite !cast_refl, vec_map_map.
        apply vec_pos_ext; intro; rew vec.
        generalize (vec_pos v p); intros []; simpl; auto; exfalso; auto.
      + apply fol_bin_sem_ext; auto.
      + apply fol_quant_sem_ext; intro; auto.
    Qed.

  End completeness.

End Uniform_arities_to_one.
