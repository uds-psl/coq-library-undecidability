
From Undecidability.L.Tactics Require Export LTactics GenEncode.

Require Import Nat.
From Undecidability.L Require Import Datatypes.LBool Functions.EqBool Datatypes.LProd.
Import GenEncode.
(* ** Encoding of natural numbers *)

MetaCoq Run (tmGenEncode "nat_enc" nat).
#[export] Hint Resolve nat_enc_correct : Lrewrite.

#[global]
Instance termT_S : computable S.
Proof.
  extract constructor.
Qed.

#[global]
Instance termT_pred : computable pred.
Proof.
  extract.
Qed.

#[global]
Instance termT_plus' : computable add.
Proof.
  extract.
Qed.

#[global]
Instance termT_mult : computable mult.
Proof.
  extract.
Qed.

#[global]
Instance term_sub : computable Nat.sub.
Proof.
  extract.
Qed.

#[global]
Instance termT_leb : computable leb.
Proof.
  extract.
Qed.

#[global]
Instance term_ltb : computable Nat.ltb.
Proof.
  extract.
Qed.

#[global]
Instance eqbNat_inst : eqbClass Nat.eqb.
Proof.
  exact Nat.eqb_spec.
Qed.

#[global]
Instance term_eqb_nat : computable Nat.eqb.
Proof.
  extract.
Qed.

#[global]
Instance termT_nat_min : computable Nat.min.
Proof.
  extract.
Qed.

#[global]
Instance termT_nat_max : computable Nat.max.
Proof.
  extract.
Qed. 

#[global]
Instance termT_pow:
  computable Init.Nat.pow.
Proof.
  extract.
Qed.

#[global]
Instance termT_divmod :
  computable divmod.
Proof.
  extract.
Qed. 

#[global]
Instance termT_modulo :
  computable Init.Nat.modulo.
Proof.
  extract.
Qed.
