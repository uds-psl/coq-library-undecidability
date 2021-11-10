(* * Binary Signature *)

Require Import Undecidability.FOL.Util.Syntax.

#[global]
Instance sig_empty : funcs_signature :=
  {| syms := False;  ar_syms := False_rect nat |}.

#[global]
Instance sig_binary : preds_signature :=
  {| preds := unit;  ar_preds := fun _ => 2 |}.

