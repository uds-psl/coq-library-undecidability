Require Import Undecidability.FOL.Syntax.Core.
Require Undecidability.FOL.Syntax.BinSig.

(* ** Signature for ZF axiomatisation, containing function symbols for set operations *)

Inductive ZF_Preds : Type :=
| elem : ZF_Preds
| equal : ZF_Preds.

Definition ZF_pred_ar (P : ZF_Preds) : nat :=
  match P with _ => 2 end.

Module ZFSignature.

#[export]
Existing Instance falsity_on.

Inductive ZF_Funcs : Type :=
| eset : ZF_Funcs
| pair : ZF_Funcs
| union : ZF_Funcs
| power : ZF_Funcs
| om : ZF_Funcs.

Definition ZF_fun_ar (f : ZF_Funcs) : nat :=
  match f with
  | eset => 0
  | pair => 2
  | union => 1
  | power => 1
  | om => 0
  end.

#[export]
Instance ZF_func_sig : funcs_signature :=
  {| syms := ZF_Funcs; ar_syms := ZF_fun_ar; |}.

#[export]
Instance ZF_pred_sig : preds_signature :=
  {| preds := ZF_Preds; ar_preds := ZF_pred_ar; |}.

End ZFSignature.


 
(* ** Signature for finite set theory axiomatisation, containing function symbols for set operations *)

Module FSTSignature.

#[export]
Existing Instance falsity_on.

Inductive FST_Funcs : Type :=
| eset : FST_Funcs
| adj : FST_Funcs.

Definition FST_fun_ar (f : FST_Funcs) : nat :=
  match f with
  | eset => 0
  | adj => 2
  end.

#[export]
Instance FST_func_sig : funcs_signature :=
  {| syms := FST_Funcs; ar_syms := FST_fun_ar; |}.

#[export]
Existing Instance ZFSignature.ZF_pred_sig | 0.

End FSTSignature.