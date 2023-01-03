(* * First-Order Logic *)

From Undecidability.FOL Require Import FullSyntax.

#[global]
Existing Instance falsity_on.
(* ** Syntax as defined in Util/Syntax.v 

 Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.

  Inductive falsity_flag := falsity_off | falsity_on.

  Inductive form : falsity_flag -> Type :=
  | falsity : form falsity_on
  | atom {b} : forall (P : preds), vec term (ar_preds P) -> form b
  | bin {b} : binop -> form b -> form b -> form b
  | quant {b} : quantop -> form b -> form b.    
*)


(* ** Instantiation to for custom FSAT reduction *)

Inductive syms_func :=
  | f : bool -> syms_func
  | e : syms_func
  | dum : syms_func.

Definition func_arity (f : syms_func) := match f with
  | f _ => 1
  | e => 0
  | dum => 0 end.

#[global]
Instance sig_func : funcs_signature :=
  {| syms := syms_func; ar_syms := func_arity |}.

Inductive syms_pred := 
  | P : syms_pred
  | less : syms_pred
  | equiv : syms_pred.

Definition pred_arty (p : syms_pred) := 2.

#[global]
Instance sig_pred : preds_signature :=
  {| preds := syms_pred; ar_preds := pred_arty |}.
