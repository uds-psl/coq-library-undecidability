(* * Binary Signature *)

Require Import Undecidability.FOL.Util.Syntax.

Instance sig_func_empty : funcs_signature :=
  {| syms := False;  ar_syms := False_rect nat |}.

Instance sig_pred_binary : preds_signature :=
  {| preds := unit;  ar_preds := fun _ => 2 |}.

