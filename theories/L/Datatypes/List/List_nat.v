From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Export List.List_enc LNat LOptions LBool.

#[global]
Instance termT_nth_error (X:Type) (Hx : encodable X): computable (@nth_error X). 
Proof.
  extract.
Qed.

#[global]
Instance termT_length X `{encodable X} : computable (@length X).
Proof.
extract.
Qed.

#[global]
Instance term_nth X (Hx : encodable X) : computable (@nth X). 
Proof.
  extract.
Qed.

#[global]
Instance term_repeat A `{encodable A}: computable (@repeat A).
Proof.
  extract.
Qed.
