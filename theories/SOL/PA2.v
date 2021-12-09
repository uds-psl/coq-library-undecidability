(* * Second-Order Peano Arithmetic *)

Require Import Undecidability.SOL.SOL.
Require Import Vector.
Import VectorNotations SOLNotations.


(* ** Signature of PA2 *)

Inductive PA2_funcs : Type := Zero | Succ | Plus | Mult.
Definition PA2_funcs_ar (f : PA2_funcs ) :=
  match f with
  | Zero => 0
  | Succ => 1
  | Plus => 2
  | Mult => 2
  end.

Inductive PA2_preds : Type := Eq : PA2_preds.
Definition PA2_preds_ar (P : PA2_preds) := match P with Eq => 2 end.

#[global]
Instance PA2_funcs_signature : funcs_signature :=
{| syms := PA2_funcs ; ar_syms := PA2_funcs_ar |}.

#[global]
Instance PA2_preds_signature : preds_signature :=
{| preds := PA2_preds ; ar_preds := PA2_preds_ar |}.

Definition zero := func (sym Zero) ([]).

Module PA2Notations.

  Notation "'σ' x" := (func (sym Succ) ([x])) (at level 37).
  Notation "x '⊕' y" := (func (sym Plus) ([x ; y])) (at level 39).
  Notation "x '⊗' y" := (func (sym Mult) ([x ; y])) (at level 38).
  Notation "x '==' y" := (atom (pred Eq) ([x ; y])) (at level 40).

  Notation "'izero'" := (@i_f _ _ (M_domain _) (M_interp _) Zero ([])).
  Notation "'iσ' x" := (@i_f _ _ (M_domain _) (M_interp _) Succ ([x])) (at level 37).
  Notation "x 'i⊕' y" := (@i_f _ _ (M_domain _) (M_interp _) Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗' y" := (@i_f _ _ (M_domain _) (M_interp _) Mult ([x ; y])) (at level 38).
  Notation "x 'i==' y" := (@i_P _ _ (M_domain _) (M_interp _) Eq ([x ; y])) (at level 40).

End PA2Notations.

Import PA2Notations.


(* ** Axioms of PA2 *)

Definition ax_eq_refl :=   ∀i $0 == $0.
Definition ax_eq_symm :=   ∀i ∀i $1 == $0 ~> $0 == $1.
Definition ax_eq_trans :=  ∀i ∀i ∀i $2 == $1 ~> $1 == $0 ~> $2 == $0.
Definition ax_zero_succ := ∀i zero == σ $0 ~> fal.
Definition ax_succ_inj :=  ∀i ∀i σ $1 == σ $0 ~> $1 == $0.
Definition ax_add_zero :=  ∀i zero ⊕ $0 == $0.
Definition ax_add_rec :=   ∀i ∀i (σ $0) ⊕ $1 == σ ($0 ⊕ $1).
Definition ax_mul_zero :=  ∀i zero ⊗ $0 == zero.
Definition ax_mul_rec :=   ∀i ∀i σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0.
Definition ax_ind := ∀p(1) p$0 ([zero]) ~> (∀i p$0 ([$0]) ~> p$0 ([σ $0])) ~> ∀i p$0 ([$0]).

Import List ListNotations.
Definition PA2_L := [ ax_eq_refl ; ax_eq_symm ; ax_zero_succ ; ax_succ_inj ; ax_add_zero ; ax_add_rec ; ax_mul_zero ; ax_mul_rec ; ax_ind ].
Definition PA2 phi := In phi PA2_L.


(* ** List of decision problems *)

(* Validity of formulas in PA2 *)
Definition PA2_valid (phi : form) := 
  forall M rho, (forall psi, PA2 psi -> @sat _ _ (M_domain M) (M_interp M) rho psi) -> @sat _ _ (M_domain M) (M_interp M) rho phi.

(* Satisfiability of formulas in PA2 *)
Definition PA2_satis (phi : form) := 
  exists M rho, (forall psi, PA2 psi -> @sat _ _ (M_domain M) (M_interp M) rho psi) /\ @sat _ _ (M_domain M) (M_interp M) rho phi.
