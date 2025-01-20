(* * ZF set theory with Skolem function symbols *)
(* ** Axiomatisations *)

Require Export Undecidability.FOL.Utils.FullSyntax.
From Undecidability.FOL.Sets Require Export FST binFST Signatures.
Import Vector.VectorNotations.
From Stdlib Require Import List.

Declare Scope syn.
Open Scope syn.

(* ** Signature for ZF axiomatisation, containing function symbols for set operations *)

Import FSTSignature.
Export FSTSignature.

(* ** Problems *)

Notation extensional M :=
  (forall x y, @i_atom _ ZFSignature.ZF_pred_sig _ M equal ([x; y]) <-> x = y).

Definition entailment_FST phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi FST -> sigma ⊨ psi) -> rho ⊨ phi.

Definition entailment_FSTeq phi :=
  forall D (M : interp D) (rho : nat -> D), (forall sigma psi, In psi FSTeq -> sigma ⊨ psi) -> rho ⊨ phi.

Definition entailment_FSTI phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, FSTI psi -> sigma ⊨ psi) -> rho ⊨ phi.

Definition deduction_FST phi :=
  FSTeq ⊢I phi.

Definition deduction_FSTI phi :=
  FSTIeq ⊢TI phi.

(* ** Problems *)

Definition entailment_binFST phi :=
  forall D (M : @interp sig_empty _ D) (rho : nat -> D), (forall psi, In psi binFST -> rho ⊨ psi) -> rho ⊨ phi.

Definition deduction_binFST phi :=
  binFST ⊢I phi.



