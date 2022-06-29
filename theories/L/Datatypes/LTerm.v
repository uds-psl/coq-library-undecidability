From Undecidability.L.Datatypes Require Export LNat.
From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import LTactics GenEncode.

(* ** Encoding for L-terms *)
MetaCoq Run (tmGenEncodeInj "term_enc" term).
#[export] Hint Resolve term_enc_correct : Lrewrite.
  
(* register the non-constant constructors *)
#[global]
Instance term_var : computableTime' var (fun n _ => (1, tt)).
Proof.
  extract constructor. solverec.
Qed.

#[global]
Instance term_app : computableTime' L.app (fun s1 _ => (1, (fun s2 _ => (1, tt)))).
Proof.
  extract constructor. solverec.
Qed.

#[global]
Instance term_lam : computableTime' lam (fun s _ => (1, tt)).
Proof.
  extract constructor. solverec.
Qed.


Definition c__termsize := c__natsizeS + 7. 
Lemma size_term_enc (s:term) :
  size (enc s) <= size s *c__termsize.
Proof.
  unfold enc;cbn.
  induction s;cbn - ["+"].
  rewrite size_nat_enc. all: unfold c__termsize, c__natsizeS, c__natsizeO in *; solverec.
Qed.


Lemma size_term_enc_r (s:term) :
  size s <= size (enc s).
Proof.
  induction s;cbv [enc encodable_term_enc] in *. all:cbn [size] in *.
  rewrite <- size_nat_enc_r. all:solverec.
Qed.
