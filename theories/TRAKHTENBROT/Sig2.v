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

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_sig fo_terms fo_logic
                 membership gfp discrete.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Section Σ2_model.

  Variable (X : Type) (M : fo_model (Σrel 2) X).

  Definition Σ2_model_mem a b := fom_rels M tt (a##b##ø).

  Definition Σ2_model_ext := mb_member_ext Σ2_model_mem.

  Infix "≈m" := (mb_equiv Σ2_model_mem) (at level 70).

  Definition Σ2_model_discr := forall a b, a ≈m b <-> a = b.

  Hypothesis ext : Σ2_model_ext.

  (** In a extensional model of Σ2, extentional equivalence is bisimulation *)

  Fact Σ2_model_ext_equiv_bisim a b : a ≈m b -> @fo_bisimilar (Σrel 2) nil (tt::nil) _ M a b.
  Proof.
    rewrite <- fom_eq_fol_characterization.
    revert a b; apply gfp_greatest.
    + intros R T H1 x y (_ & H2).
      split; auto.
      intros ? [].
    + intros x y Hxy; split.
      * intros ? [].
      * intros ? [ <- | [] ] v p. 
        simpl in *.
        vec split v with a; vec split v with b; vec nil v; clear v.
        analyse pos p; simpl.
        - split; apply ext; auto.
          intro; symmetry; apply Hxy. 
        - apply Hxy.
  Qed.

End Σ2_model.

Section Sig2_extensional.

  (** If a formula A of Σ2 is satisfiable in some finite & decidable
      and extensional model, it is also satisfiable in a 
      finite & decidable & extensional model where extensional
      identity is equality *)

  Variables (X : Type) 
            (M : fo_model (Σrel 2) X)
            (Mfin : finite_t X)
            (Mdec : fo_model_dec M)
            (Mext : Σ2_model_ext M)
            (φ : nat -> X) (A : fol_form (Σrel 2)) 
            (HA : fol_sem M φ A).

    Let mem a b := fom_rels M tt (a##b##ø).

    Infix "∈m" := mem (at level 70).
    Infix "≈m" := (mb_equiv mem) (at level 70).

    Let discr := @fo_fin_model_discretize (Σrel 2) nil (tt::nil) _ Mfin M Mdec. 
  
    Let n := projT1 discr.
    Let Md : fo_model (Σrel 2) (pos n).
    Proof. apply (projT1 (projT2 discr)). Defined.
    Let Mb : fo_model_dec Md.
    Proof. apply (projT1 (projT2 (projT2 discr))). Qed.
    Let p : @fo_projection (Σrel 2) nil (tt::nil) _ M _ Md.
    Proof. apply (projT1 (projT2 (projT2 (projT2 discr)))). Qed.
    Let H x y : @fo_bisimilar (Σrel 2) nil (tt::nil) _ Md x y <-> x = y.
    Proof. apply (projT2 (projT2 (projT2 (projT2 discr)))). Qed.

    Let extensional : Σ2_model_ext Md.
    Proof.
      revert Mext.
      unfold Σ2_model_ext, Σ2_model_mem.
      rewrite <- Σ2_extensional_spec with (ψ := fun n => p (φ n)).
      rewrite <- Σ2_extensional_spec with (ψ := φ).
      apply fo_model_projection with (ls := nil) (lr := tt::nil) (p := p); auto.
      all: intros []; simpl; auto.
    Qed.

    Let discrete : Σ2_model_discr Md.
    Proof.
      intros x y; split.
      2: intros []; apply mb_equiv_refl.
      rewrite <- H.
      apply Σ2_model_ext_equiv_bisim; auto.
    Qed.

    Theorem Sig2_ext_discr : 
        { Y : Type & 
        { K : fo_model (Σrel 2) Y &
        { _ : finite_t Y &
        { _ : fo_model_dec K & 
        { _ : Σ2_model_ext K &
        { _ : Σ2_model_discr K & 
        { ψ | fol_sem K ψ A }}}}}}}.
    Proof.
      exists (pos n), Md.
      exists. { apply finite_t_pos. }
      exists Mb, extensional, discrete.
      exists (fun n => p (φ n)).
      revert HA.
      apply fo_model_projection with (ls := nil) (lr := tt::nil) (p := p); auto.
      all: intros []; simpl; auto.
      all: unfold incl; cbn; simpl; try tauto.
    Qed. 

End Sig2_extensional.
