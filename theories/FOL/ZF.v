(* * ZF set theory with Skolem function symbols *)
(* ** Axiomatisations *)

Require Export Undecidability.FOL.Utils.FullSyntax.
From Undecidability.FOL.Sets Require Export ZF minZF binZF Signatures.
Import Vector.VectorNotations.
Require Import List.

Declare Scope syn.
Open Scope syn.

(* ** Signature for ZF axiomatisation, containing function symbols for set operations *)

Import ZFSignature.
Export ZFSignature.
(* ** Problems *)

Notation extensional M :=
  (forall x y, @i_atom _ ZF_pred_sig _ M equal ([x; y]) <-> x = y).

(* Semantic entailment restricted to core axioms (without sep and rep) with equality axioms. *)

Definition entailment_ZFeq' phi :=
  forall D (M : interp D) (rho : nat -> D), (forall sigma psi, In psi ZFeq' -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment restricted to extensional models and hereditarily finite sets. *)

Definition entailment_HF phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi HF -> sigma ⊨ psi) -> rho ⊨ phi.

Definition entailment_HFN phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi HFN -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment restricted to extensional models and core axioms (without sep and rep). *)

Definition entailment_ZF' phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi ZF' -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment for Z restricted to extensional models. *)

Definition entailment_Z phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, Z psi -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment for ZF restricted to extensional models. *)

Definition entailment_ZF phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, ZF psi -> sigma ⊨ psi) -> rho ⊨ phi.

(* Deductive entailment restricted to hereditarily finite sets. *)

Definition deduction_HF phi :=
  HFeq ⊢I phi.

Definition deduction_HFN phi :=
  HFNeq ⊢I phi.

(* Deductive entailment restricted to intuitionistic rules and core axioms (without sep and rep). *)

Definition deduction_ZF' phi :=
  ZFeq' ⊢I phi.

(* Deductive entailment for Z restricted to intuitionistic rules. *)

Definition deduction_Z phi :=
  Zeq ⊢TI phi.

(* Deductive entailment for ZF restricted to intuitionistic rules. *)

Definition deduction_ZF phi :=
  ZFeq ⊢TI phi.


(* ** MinZF *)

(* Semantic entailment restricted to core axioms (without sep and rep) with equality axioms. *)

Definition entailment_minZFeq' phi :=
  forall D (M : interp D) (rho : nat -> D), (forall sigma psi, In psi minZFeq' -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment restricted to extensional models and core axioms (without sep and rep). *)

Definition entailment_minZF' phi :=
  forall D (M : @interp sig_empty _ D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi minZF' -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment for Z restricted to extensional models. *)

Definition entailment_minZ phi :=
  forall D (M : @interp sig_empty _ D) (rho : nat -> D), extensional M -> (forall sigma psi, minZ psi -> sigma ⊨ psi) -> rho ⊨ phi.

(* Semantic entailment for ZF restricted to extensional models. *)

Definition entailment_minZF phi :=
  forall D (M : @interp sig_empty _ D) (rho : nat -> D), extensional M -> (forall sigma psi, minZF psi -> sigma ⊨ psi) -> rho ⊨ phi.

(* Deductive entailment restricted to intuitionistic rules and core axioms (without sep and rep). *)

Definition deduction_minZF' phi :=
  minZFeq' ⊢I phi.

(* Deductive entailment for Z restricted to intuitionistic rules. *)

Definition deduction_minZ phi :=
  minZeq ⊢TI phi.

(* Deductive entailment for ZF restricted to intuitionistic rules. *)

Definition deduction_minZF phi :=
  minZFeq ⊢TI phi.


(* ** BinZF *)

(* Semantic entailment restricted to extensional models and core axioms (without sep and rep). *)

Definition entailment_binZF phi :=
  forall D (M : @interp sig_empty _ D) (rho : nat -> D), (forall psi, In psi binZF -> rho ⊨ psi) -> rho ⊨ phi.

(* Deductive entailment restricted to intuitionistic rules and core axioms (without sep and rep). *)

Definition deduction_binZF phi :=
  binZF ⊢I phi.

