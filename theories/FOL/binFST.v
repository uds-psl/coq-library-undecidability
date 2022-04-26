(** ** Axiomatisation of finite set theory just using membership *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.sig_bin.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Import Vector.VectorNotations.
Require Import List.


 
(* ** Minimal binary signature only containing membership, no function symbols or equality *)
#[global]
Existing Instance falsity_on.

Notation term' := (term sig_empty).
Notation form' := (form sig_empty sig_binary _ falsity_on).

Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Declare Scope syn'.
Open Scope syn'.

Notation "x ∈' y" := (atom sig_empty sig_binary tt ([x; y])) (at level 35) : syn'.

Definition eq' (x y : term') :=
  ∀ x`[↑] ∈' $0 ↔ y`[↑] ∈' $0.

Notation "x ≡' y" := (eq' x y) (at level 35) : syn'.



(* ** Symbol-free axiomatisation *)

Definition is_eset (t : term') :=
  ∀ ¬ ($0 ∈' t`[↑]).

Definition is_adj (x y t : term') :=
  ∀ $0 ∈' t`[↑] ↔ $0 ∈' x`[↑] ∨ $0 ≡' y`[↑].

Definition sub' (x y : term') :=
  ∀ $0 ∈' x`[↑] → $0 ∈' y`[↑].

Definition ax_ext' :=
  ∀ ∀ sub' $1 $0 → sub' $0 $1 → $1 ≡' $0.

Definition ax_eq_elem' :=
  ∀ ∀ ∀ ∀ $3 ≡' $1 → $2 ≡' $0 → $3 ∈' $2 → $1 ∈' $0.

Definition ax_eset' :=
  ∃ is_eset $0.

Definition ax_adj' :=
  ∀ ∀ ∃ is_adj $2 $1 $0.

Definition binFST :=
  ax_ext' :: ax_eq_elem' :: ax_eset' :: ax_adj' :: nil.



(* ** Problems *)

Definition entailment_binFST phi :=
  forall D (M : @interp sig_empty _ D) (rho : nat -> D), (forall psi, In psi binFST -> rho ⊨ psi) -> rho ⊨ phi.

Definition deduction_binFST phi :=
  binFST ⊢I phi.


