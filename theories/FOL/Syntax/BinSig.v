(* * Binary Signature *)

Require Import Undecidability.FOL.Syntax.Core.

#[global]
Instance sig_empty : funcs_signature | 0 :=
  {| syms := False;  ar_syms := False_rect nat |}.

#[global]
Instance sig_binary : preds_signature | 0 :=
  {| preds := unit;  ar_preds := fun _ => 2 |}.

