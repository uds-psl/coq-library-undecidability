(** * Peano Arithmetic *)
(* ** Problems in PA *)
From Undecidability.FOL Require Import Syntax.Core.
From Undecidability.FOL.Arithmetics Require Export Signature FA Robinson PA.
Require Import Undecidability.FOL.Deduction.FullCore.
Require Import Undecidability.FOL.Semantics.Tarski.FullCore.
Import Vector.VectorNotations.
Require Import List.

Notation extensional M :=
  (forall x y, @i_atom _ _ _ M Eq ([x ; y]) <-> x = y).


(* Semantic entailment restricted to FA *)

Definition entailment_FA phi :=
  valid_ctx FAeq phi.


(* Deductive entailment restricted to intuitionistic rules and FA. *)

Definition deduction_FA phi :=
  FAeq ⊢I phi.


(* Semantic entailment restricted to Q *)

Definition entailment_Q phi :=
  valid_ctx Qeq phi.

(* Deductive entailment restricted to intuitionistic rules and FA. *)

Definition deduction_Q phi :=
  Qeq ⊢I phi.


(* Semantic entailment for PA *)

Definition entailment_PA phi :=
  forall D (I : interp D) rho, (forall psi rho, PAeq psi -> rho ⊨ psi) -> rho ⊨ phi.


(* Semantic entailment restricted to extensional models of PA *)

Definition ext_entailment_PA phi :=
  forall D (I : interp D) rho, extensional I -> (forall psi rho, PA psi -> rho ⊨ psi) -> rho ⊨ phi.


(* Deductive entailment restricted to intuitionistic rules. *)

Definition deduction_PA phi :=
  PAeq ⊢TI phi.
