(** * Peano Arithmetic *)
(** ** Signature *)

Require Import Undecidability.FOL.Syntax.Core.
Import Vector.VectorNotations.
Require Import List.

(* ** Signature for PA axiomatisation, containing function symbols for set operations *)


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

