(** * Finite Set Theory with Adjunction Operation *)
(** ** Axiomatisations *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Import Vector.VectorNotations.
Require Import List.


 
(* ** Signature for ZF axiomatisation, containing function symbols for set operations *)

Existing Instance falsity_on.

Inductive FST_Funcs : Type :=
| eset : FST_Funcs
| adj : FST_Funcs.

Definition FST_fun_ar (f : FST_Funcs) : nat :=
  match f with
  | eset => 0
  | adj => 2
  end.

Inductive FST_Preds : Type :=
| elem : FST_Preds
| equal : FST_Preds.

Definition FST_pred_ar (P : FST_Preds) : nat :=
  match P with _ => 2 end.

Instance FST_func_sig : funcs_signature :=
  {| syms := FST_Funcs; ar_syms := FST_fun_ar; |}.

Instance FST_pred_sig : preds_signature :=
  {| preds := FST_Preds; ar_preds := FST_pred_ar; |}.



(* ** Axioms *)

Notation "x ∈ y" := (atom _ FST_pred_sig elem ([x; y])) (at level 35) : syn.
Notation "x ≡ y" := (atom (Σ_preds := FST_pred_sig) equal ([x; y])) (at level 35) : syn.

Notation "∅" := (func FST_func_sig eset ([])) : syn.
Notation "x ::: y" := (func FST_func_sig adj ([x; y])) (at level 31) : syn.

Definition sub x y :=
  ∀ $0 ∈ x`[↑] ~> $0 ∈ y`[↑].

Notation "x ⊆ y" := (sub x y) (at level 34) : syn.

Definition ax_ext :=
  ∀ ∀ $1 ⊆ $0 ~> $0 ⊆ $1 ~> $1 ≡ $0.

Definition ax_eset :=
  ∀ ¬ ($0 ∈ ∅).

Definition ax_adj :=
  ∀ ∀ ∀ $0 ∈ $1 ::: $2 <~> $0 ≡ $1 ∨ $0 ∈ $2.

(* Finite set theory *)

Definition FST :=
  ax_ext :: ax_eset :: ax_adj :: nil.

(* Finite set theory with equalilty axioms *)

Definition ax_refl :=
  ∀ $0 ≡ $0.

Definition ax_sym :=
  ∀ ∀ $1 ≡ $0 ~> $0 ≡ $1.

Definition ax_trans :=
  ∀ ∀ ∀ $2 ≡ $1 ~> $1 ≡ $0 ~> $2 ≡ $0.

Definition ax_eq_elem :=
  ∀ ∀ ∀ ∀ $3 ≡ $1 ~> $2 ≡ $0 ~> $3 ∈ $2 ~> $1 ∈ $0.

Definition FSTeq :=
  ax_refl :: ax_sym :: ax_trans :: ax_eq_elem :: FST.



(* ** Problems *)

Notation extensional M :=
  (forall x y, @i_atom _ FST_pred_sig _ M equal ([x; y]) <-> x = y).

Definition entailment_FST phi :=
  forall D (M : interp D) (rho : nat -> D), extensional M -> (forall sigma psi, In psi FST -> sigma ⊨ psi) -> rho ⊨ phi.

Definition deduction_FST phi :=
  FSTeq ⊢I phi.


