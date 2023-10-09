(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations fol_ops fo_sig fo_terms fo_logic fo_sat.

Import fol_notations.

Set Implicit Arguments.

(* * From binary singleton to n-ary singleton with n >= 2 *)

Local Notation ø := vec_nil.

(* The reduction could be made to work for (infinite) SAT only *)

Section Sig2_Sig_n_encoding.

  Variable (n : nat).

  Notation Σ2 := (Σrel 2).
  Notation Σn := (Σrel (S (S n))).

  (* The encoding is trivial here : replace R2(x,y) with Rn(x,y,...,y) *)

  Fixpoint Σ2_Σn (A : fol_form Σ2) : fol_form Σn :=
    match A with
      | ⊥              => ⊥
      | fol_atom   _ v => let x := Σrel_var (vec_head v)            in
                          let y := Σrel_var (vec_head (vec_tail v)) 
                          in  @fol_atom Σn tt (£x##vec_set_pos (fun _ => £y))
      | fol_bin b A B  => fol_bin b (Σ2_Σn A) (Σ2_Σn B)
      | fol_quant q A  => fol_quant q (Σ2_Σn A)
     end.

  Section correctness.

    Variable (X : Type) (M2 : fo_model Σ2 X) (Mn : fo_model Σn X).

    Notation "⟪ A ⟫" := (fun ψ => fol_sem M2 ψ A).
    Notation "⟪ A ⟫'" := (fun φ => fol_sem Mn φ A) (at level 1, format "⟪ A ⟫'").

    Let P2 a b := fom_rels M2 tt (a##b##ø).
    Let Pn a b := fom_rels Mn tt (a##vec_set_pos (fun _ => b)).

    Hypothesis HP : forall x y, P2 x y <-> Pn x y.

    Lemma Σ2_Σn_correct (A : fol_form Σ2) φ : ⟪ A ⟫ φ <-> ⟪Σ2_Σn A⟫' φ.
    Proof using HP.
      revert φ.
      induction A as [ | [] v | b A HA B HB | q A HA ]; intros phi.
      + simpl; tauto.
      + vec split v with a; vec split v with b; vec nil v; clear v; revert a b.
        intros [ a | [] ] [ b | [] ]; unfold Σ2_Σn; simpl; rew fot.
        rewrite vec_map_set_pos; apply HP.
      + simpl; apply fol_bin_sem_ext; auto.
      + simpl; apply fol_quant_sem_ext; intro; auto.
    Qed.

  End correctness.

  Variable (A : fol_form Σ2).

  Section soundness.

    Variables (X : Type)
              (M2 : fo_model Σ2 X)
              (H1 : finite_t X)
              (H2 : fo_model_dec M2)
              (phi : nat -> X)
              (H3 : fol_sem M2 phi A).

    Let Mn : fo_model Σn X.
    Proof.
      exists.
      + intros [].
      + intros []; simpl.
        intros v.
        exact (fom_rels M2 tt (vec_head v##vec_head (vec_tail v)##ø)).
    Defined.
 
    Local Lemma Σ2_Σn_sound_loc : fo_form_fin_dec_SAT (Σ2_Σn A).
    Proof using All.
      exists X, Mn, H1.
      exists. { intros [] ?; apply H2. }
      exists phi.
      revert H3. 
      apply Σ2_Σn_correct; simpl; tauto.
    Qed.

  End soundness.
 
  Lemma Σ2_Σn_soundness : 
        fo_form_fin_dec_SAT A
     -> fo_form_fin_dec_SAT (Σ2_Σn A).
  Proof.
    intros (X & M2 & H1 & H2 & phi & H3).
    apply Σ2_Σn_sound_loc with (M2 := M2) (phi := phi); auto.
  Qed.

  Section completeness.

    Variables (X : Type)
              (Mn : fo_model Σn X)
              (H1 : finite_t X)
              (H2 : fo_model_dec Mn)
              (phi : nat -> X)
              (H3 : fol_sem Mn phi (Σ2_Σn A)).

    Let M2 : fo_model Σ2 X.
    Proof.
      exists.
      + intros [].
      + intros []; simpl.
        intros v.
        exact (fom_rels Mn tt (vec_head v##vec_set_pos (fun _ => vec_head (vec_tail v)))).
    Defined.
 
    Local Lemma Σ2_Σn_complete_loc : fo_form_fin_dec_SAT A.
    Proof using All.
      exists X, M2, H1.
      exists. { intros [] ?; apply H2. }
      exists phi.
      revert H3. 
      apply Σ2_Σn_correct; simpl; tauto.
    Qed.

  End completeness.
 
  Lemma Σ2_Σn_completeness : 
        fo_form_fin_dec_SAT (Σ2_Σn A)
     -> fo_form_fin_dec_SAT A.
  Proof.
    intros (X & Mn & H1 & H2 & phi & H3).
    apply Σ2_Σn_complete_loc with (Mn := Mn) (phi := phi); auto.
  Qed.

End Sig2_Sig_n_encoding.

