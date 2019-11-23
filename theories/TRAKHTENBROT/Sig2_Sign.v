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
  Require Import notations fol_ops fo_terms fo_logic fo_sat.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Section Sig2_Sig_n_encoding.

  Variable (n : nat).

  Notation Σ2 := (Σrel 2).
  Notation Σn := (Σrel (S (S n))).

  Fixpoint Σ2_Σn (A : fol_form Σ2) : fol_form Σn :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ _ v => let a := Σrel_var (vec_head v)            in
                          let b := Σrel_var (vec_head (vec_tail v)) 
                          in  fol_atom Σn tt (£a##vec_set_pos (fun _ => £b))
      | fol_bin b A B  => fol_bin b (Σ2_Σn A) (Σ2_Σn B)
      | fol_quant q A  => fol_quant q (Σ2_Σn A)
     end.

  Variable (X : Type) (M2 : fo_model Σ2 X) (Mn : fo_model Σn X).

  Notation "⟪ A ⟫" := (fun ψ => fol_sem M2 ψ A).
  Notation "⟪ A ⟫'" := (fun φ => fol_sem Mn φ A) (at level 1, format "⟪ A ⟫'").

  Let P2 a b := fom_rels M2 tt (a##b##ø).
  Let Pn a b := fom_rels Mn tt (a##vec_set_pos (fun _ => b)).

  Variable R : X -> X -> Prop.

  Lemma Σ2_Σn_correct (A : fol_form Σ2) φ ψ :
           (forall x, R x x)
        -> (forall a a' b b', R a a' -> R b b' -> P2 a b <-> Pn a' b')
        -> (forall x, In x (fol_vars A) -> R (φ x) (ψ x))
        -> ⟪ A ⟫ φ <-> ⟪Σ2_Σn A⟫' ψ.
  Proof.
    intros H0 H1.
    revert φ ψ.
    induction A as [ | [] v | b A HA B HB | q A HA ]; intros phi psy H2.
    + simpl; tauto.
    + revert H2; vec split v with a; vec split v with b; vec nil v; clear v; revert a b.
      intros [ a | [] ] [ b | [] ]; rew fot; intros H2.
      unfold Σ2_Σn; simpl; rew fot.
      rewrite vec_map_set_pos; apply H1; apply H2; simpl; auto.
    + simpl; apply fol_bin_sem_ext.
      * apply HA; intros; apply H2, in_or_app; auto.
      * apply HB; intros; apply H2, in_or_app; auto.
    + simpl; apply fol_quant_sem_ext; intros x.
      apply HA; intros [ | m ] ?; simpl; auto.
      apply H2; simpl; apply in_flat_map.
      exists (S m); simpl; auto.
  Qed.
 
End Sig2_Sig_n_encoding.

Section SATn_SAT2.

  Section nested.

    Variables (n : nat)
              (A : fol_form (Σrel 2))
              (X : Type)
              (Mn : fo_model (Σrel (S (S n))) X)
              (H1 : finite_t X)
              (H2 : fo_model_dec Mn)
              (phi : nat -> X)
              (H3 : fol_sem Mn phi (Σ2_Σn n A)).

    Let M2 : fo_model (Σrel 2) X.
    Proof.
      exists.
      + intros [].
      + intros []; simpl.
        intros v.
        exact (fom_rels Mn tt (vec_head v##vec_set_pos (fun _ => vec_head (vec_tail v)))).
    Defined.
 
    Local Lemma SATn_SAT2_local : fo_form_fin_dec_SAT A.
    Proof.
      exists X, M2, H1.
      exists. { intros [] ?; apply H2. }
      exists phi.
      revert H3. 
      apply Σ2_Σn_correct with (R := eq); auto.
      intros a ? b ? <- <-; simpl; tauto.
    Qed.

  End nested.
 
  Theorem SATn_SAT2 n A : fo_form_fin_dec_SAT (Σ2_Σn n A)
                       -> fo_form_fin_dec_SAT A.
  Proof.
    intros (X & Mn & H1 & H2 & phi & H3).
    apply SATn_SAT2_local with (Mn := Mn) (phi := phi); auto.
  Qed.

End SATn_SAT2.

Section SAT2_SATn.

  Section nested.

    Variables (n : nat)
              (A : fol_form (Σrel 2))
              (X : Type)
              (M2 : fo_model (Σrel 2) X)
              (H1 : finite_t X)
              (H2 : fo_model_dec M2)
              (phi : nat -> X)
              (H3 : fol_sem M2 phi A).

    Let Mn : fo_model (Σrel (S (S n))) X.
    Proof.
      exists.
      + intros [].
      + intros []; simpl.
        intros v.
        exact (fom_rels M2 tt (vec_head v##vec_head (vec_tail v)##ø)).
    Defined.
 
    Local Lemma SAT2_SATn_local : fo_form_fin_dec_SAT (Σ2_Σn n A).
    Proof.
      exists X, Mn, H1.
      exists. { intros [] ?; apply H2. }
      exists phi.
      revert H3. 
      apply Σ2_Σn_correct with (R := eq); auto.
      intros a ? b ? <- <-; simpl; tauto.
    Qed.

  End nested.
 
  Theorem SAT2_SATn n A : fo_form_fin_dec_SAT A
                       -> fo_form_fin_dec_SAT (Σ2_Σn n A).
  Proof.
    intros (X & M2 & H1 & H2 & phi & H3).
    apply SAT2_SATn_local with (M2 := M2) (phi := phi); auto.
  Qed.

End SAT2_SATn.

Check SATn_SAT2.
Check SAT2_SATn.
  
