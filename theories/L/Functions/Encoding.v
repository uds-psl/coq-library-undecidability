From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat LTerm.

(* ** Extracted encoding of natural numbers *)

#[global]
Instance term_nat_enc : computable (nat_enc).
Proof.
  extract.
Qed.

(* ** Extracted term encoding *)

#[global]
Instance term_term_enc : computable (term_enc).
Proof.
  extract.
Qed.
