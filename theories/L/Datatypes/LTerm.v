From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Export LNat.

(** ** Encoding for L-terms *)
Run TemplateProgram (tmGenEncode "term_enc" term).
Hint Resolve term_enc_correct : Lrewrite.
  
(* register the non-constant constructors *)
Instance term_var : computableTime' var (fun n _ => (1, tt)).
Proof.
  extract constructor. solverec.
Defined.

Instance term_app : computableTime' app (fun s1 _ => (1, (fun s2 _ => (1, tt)))).
Proof.
  extract constructor. solverec.
Defined.

Instance term_lam : computableTime' lam (fun s _ => (1, tt)).
Proof.
  extract constructor. solverec.
Defined.


Lemma size_term_enc (s:term) :
  size (enc s) <= size s *11.
Proof.
  induction s;cbv [enc registered_term_enc] in *. all:cbn [size term_enc] in *.
  rewrite size_nat_enc. all:solverec.
Qed.


Lemma size_term_enc_r (s:term) :
  size s <= size (enc s).
Proof.
  induction s;cbv [enc registered_term_enc] in *. all:cbn [size term_enc] in *.
  rewrite <- size_nat_enc_r. all:solverec.
Qed.
