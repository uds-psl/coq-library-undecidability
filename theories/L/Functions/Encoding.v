From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat LBool LTerm LProd LOptions List.List_basics.

(* ** Extracted encoding of natural numbers *)

#[global]
Instance term_nat_enc : computable (enc (X:=nat)).
Proof.
  unfold enc;cbn. extract.
Qed.

(* ** Extracted term encoding *)

#[global]
Instance term_term_enc : computable (enc (X:=term)).
Proof.
  unfold enc;cbn. extract.
Qed.

#[global]
Instance bool_enc : computable (enc (X:=bool)).
Proof.
  unfold enc; cbn. extract.
Qed.

(* ** Extracted tuple encoding *)

#[global]
Instance term_prod_enc X Y (R1:encodable X) (R2:encodable Y)
         {HX : computable (enc (X:=X))} {HY : computable (enc (X:=Y))}
  :computable (enc (X:=X*Y)).
Proof.
  unfold enc;cbn. extract.
Qed.

#[global]
Instance term_list_enc X (R:encodable X) {HX : computable (enc (X:=X))} :
  computable (enc (X:=list X)).
Proof.
  unfold enc;cbn. extract.
Qed.

#[global]
Instance term_option_enc X (R:encodable X) {HX : computable (enc (X := X))} :
  computable (enc (X:=option X)).
Proof.
  unfold enc; cbn. extract.
Qed.
