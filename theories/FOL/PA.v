(** * Peano Arithmetic *)
(** ** Axiomatisations *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Import Vector.VectorNotations.
Require Import List.

(* ** Signature for PA axiomatisation, containing function symbols for set operations *)

#[global]
Existing Instance falsity_on.


Inductive PA_funcs : Type :=
  Zero : PA_funcs
| Succ : PA_funcs
| Plus : PA_funcs
| Mult : PA_funcs.

Definition PA_funcs_ar (f : PA_funcs ) :=
match f with
 | Zero => 0
 | Succ => 1
 | Plus => 2
 | Mult => 2
 end.

Inductive PA_preds : Type :=
  Eq : PA_preds.

Definition PA_preds_ar (P : PA_preds) :=
match P with
 | Eq => 2
end.


#[global]
Instance PA_funcs_signature : funcs_signature :=
{| syms := PA_funcs ; ar_syms := PA_funcs_ar |}.

#[global]
Instance PA_preds_signature : preds_signature :=
{| preds := PA_preds ; ar_preds := PA_preds_ar |}.




Declare Scope PA_Notation.
Open Scope PA_Notation.

Notation "'zero'" := (@func PA_funcs_signature Zero ([])) (at level 1) : PA_Notation.
Notation "'σ' x" := (@func PA_funcs_signature Succ ([x])) (at level 32) : PA_Notation.
Notation "x '⊕' y" := (@func PA_funcs_signature Plus ([x ; y]) ) (at level 39) : PA_Notation.
Notation "x '⊗' y" := (@func PA_funcs_signature Mult ([x ; y]) ) (at level 38) : PA_Notation.
Notation "x '==' y" := (@atom PA_funcs_signature PA_preds_signature _ _ Eq ([x ; y])) (at level 40) : PA_Notation.
Notation "x '⧀' y"  := (∃ (x[↑] ⊕ σ $0) == y) (at level 42) : PA_Notation.




(* ** Axioms of PA *)


Definition ax_zero_succ := ∀  (zero == σ var 0 → falsity).
Definition ax_succ_inj :=  ∀∀ (σ $1 == σ $0 → $1 == $0).
Definition ax_add_zero :=  ∀  (zero ⊕ $0 == $0).
Definition ax_add_rec :=   ∀∀ ((σ $0) ⊕ $1 == σ ($0 ⊕ $1)).
Definition ax_mult_zero := ∀  (zero ⊗ $0 == zero).
Definition ax_mult_rec :=  ∀∀ (σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0).

Definition ax_induction (phi : form) :=
  phi[zero..] → (∀ phi → phi[σ $0 .: S >> var]) → ∀ phi.



(* Fragment only containing the defining equations for addition and multiplication. *)
Definition FA := ax_add_zero :: ax_add_rec :: ax_mult_zero :: ax_mult_rec :: nil.

(* Robinson Arithmetic *)
Definition ax_cases := ∀ $0 == zero ∨ ∃ $1 == σ $0.
Definition Q := FA ++ (ax_zero_succ::ax_succ_inj::ax_cases::nil).


(* Full axiomatisation of the theory of PA *)
Inductive PA : form -> Prop :=
  PA_FA phi : In phi FA -> PA phi
| PA_discr : PA ax_zero_succ
| PA_inj : PA ax_succ_inj
| PA_induction phi : PA (ax_induction phi).



(* Equality axioms for the PA signature *)

Definition ax_refl :=  ∀   $0 == $0.
Definition ax_sym :=   ∀∀  $1 == $0 → $0 == $1.
Definition ax_trans := ∀∀∀ $2 == $1 → $1 == $0 → $2 == $0.

Definition ax_succ_congr := ∀∀ $0 == $1 → σ $0 == σ $1.
Definition ax_add_congr := ∀∀∀∀ $0 == $1 → $2 == $3 → $0 ⊕ $2 == $1 ⊕ $3.
Definition ax_mult_congr := ∀∀∀∀ $0 == $1 → $2 == $3 → $0 ⊗ $2 == $1 ⊗ $3.


Definition EQ :=
  ax_refl :: ax_sym :: ax_trans :: ax_succ_congr :: ax_add_congr :: ax_mult_congr :: nil.

Definition FAeq :=
  EQ ++ FA.

Definition Qeq :=
  EQ ++ Q.

Inductive PAeq : form -> Prop :=
  PAeq_FA phi : In phi FAeq -> PAeq phi
| PAeq_discr : PAeq ax_zero_succ
| PAeq_inj : PAeq ax_succ_inj
| PAeq_induction phi : PAeq (ax_induction phi).

(* ** Problems *)

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
