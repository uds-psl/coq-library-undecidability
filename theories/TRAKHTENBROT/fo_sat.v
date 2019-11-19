(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import finite.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic.

Set Implicit Arguments.

Section satisfiability.

  Variable (Σ : fo_signature) (A : fol_form Σ).

  (** A first order formula over signature Σ is finitely satisfiable over
      type X if there exists a model M interpreting the signature Σ over type X
      which is both finite (strongly listable) and strongly decidable,
      and a valuation φ : nat -> X in which A is satisfied *)

  Definition fo_form_fin_SAT_in X := 
    exists (M : fo_model Σ X)  
           (_ : finite_t X) 
           (φ : nat -> X), 
           fol_sem M φ A.

  Definition fo_form_fin_dec_SAT_in X := 
    exists (M : fo_model Σ X)  
           (_ : finite_t X) 
           (_ : fo_model_dec M) 
           (φ : nat -> X), 
           fol_sem M φ A.

  Definition fo_form_fin_discr_dec_SAT_in X := 
    exists (_ : discrete X), 
           fo_form_fin_dec_SAT_in X.

  Definition fo_form_fin_SAT := ex fo_form_fin_SAT_in.
  Definition fo_form_fin_dec_SAT := ex fo_form_fin_dec_SAT_in.
  Definition fo_form_fin_discr_dec_SAT := ex fo_form_fin_discr_dec_SAT_in.

  Fact fo_form_fin_discr_dec_SAT_fin_dec : fo_form_fin_discr_dec_SAT -> fo_form_fin_dec_SAT.
  Proof. intros (X & _ & ?); exists X; trivial. Qed.

  Fact fo_form_fin_dec_SAT_fin : fo_form_fin_dec_SAT -> fo_form_fin_SAT.
  Proof. intros (X & M & H & _ & ?); exists X, M, H; trivial. Qed.

End satisfiability.

Print fo_form_fin_SAT_in.