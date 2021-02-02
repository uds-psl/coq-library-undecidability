(* * Definition of semantic and deductive ZF-Entailment in binary signature *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.sig_bin.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Import Vector.VectorNotations.
Require Import List.


 
(* ** Minimal binary signature only containing membership, no function symbols or equality *)

Existing Instance falsity_on.

Notation term' := (term sig_func_empty).
Notation form' := (form sig_func_empty sig_pred_binary _ falsity_on).

Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Declare Scope syn'.
Open Scope syn'.

Notation "x ∈' y" := (atom sig_func_empty sig_pred_binary tt ([x; y])) (at level 35) : syn'.

Definition eq' (x y : term') :=
  ∀ x`[↑] ∈' $0 <~> y`[↑] ∈' $0.

Notation "x ≡' y" := (eq' x y) (at level 35) : syn'.



(* ** Characterisations of set operations *)

Fixpoint shift `{funcs_signature} `{preds_signature} n (t : term) :=
  match n with 
  | O => t
  | S n => subst_term ↑ (shift n t)
  end.

Definition is_eset (t : term') :=
  ∀ ¬ ($0 ∈' t`[↑]).

Definition is_pair (x y t : term') :=
  ∀ $0 ∈' t`[↑] <~> $0 ≡' x`[↑] ∨ $0 ≡' y`[↑].

Definition is_union (x t : term') :=
  ∀ $0 ∈' t`[↑] <~> ∃ $0 ∈' shift 2 x ∧ $1 ∈' $0.

Definition sub' (x y : term') :=
  ∀ $0 ∈' x`[↑] ~> $0 ∈' y`[↑].

Definition is_power (x t : term') :=
  ∀ $0 ∈' t`[↑] <~> sub' $0 x`[↑].

Definition is_sigma (x t : term') :=
  ∀ $0 ∈' t`[↑] <~> $0 ∈' x`[↑] ∨ $0 ≡' x`[↑].

Definition is_inductive (t : term') :=
  (∃ is_eset $0 ∧ $0 ∈' t`[↑]) ∧ ∀ $0 ∈' t`[↑] ~> (∃ is_sigma $1 $0 ∧ $0 ∈' shift 2 t).

Definition is_om (t : term') :=
  is_inductive t ∧ ∀ is_inductive $0 ~> sub' t`[↑] $0.



(* ** Symbol-free axiomatisation *)

Definition ax_ext' :=
  ∀ ∀ sub' $1 $0 ~> sub' $0 $1 ~> $1 ≡' $0.

Definition ax_eq_elem' :=
  ∀ ∀ ∀ ∀ $3 ≡' $1 ~> $2 ≡' $0 ~> $3 ∈' $2 ~> $1 ∈' $0.

Definition ax_eset' :=
  ∃ is_eset $0.

Definition ax_pair' :=
  ∀ ∀ ∃ is_pair $2 $1 $0.

Definition ax_union' :=
  ∀ ∃ is_union $1 $0.

Definition ax_power' :=
  ∀ ∃ is_power $1 $0.

Definition ax_om' :=
  ∃ is_om $0.

Definition binZF :=
  ax_ext' :: ax_eq_elem' :: ax_eset' :: ax_pair' :: ax_union' :: ax_power' :: ax_om' :: nil.



(* ** Problems *)

(* Semantic entailment restricted to extensional models and core axioms (without sep and rep). *)

Definition entailment_binZF phi :=
  forall D (M : @interp sig_func_empty _ D) (rho : nat -> D), (forall psi, In psi binZF -> rho ⊨ psi) -> rho ⊨ phi.

(* Deductive entailment restricted to intuitionistic rules and core axioms (without sep and rep). *)

Definition deduction_binZF phi :=
  binZF ⊢I phi.


