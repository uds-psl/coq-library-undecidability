From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Export LNat.

(** ** Encoding for L-terms *)
Run TemplateProgram (tmGenEncode "term_enc" term).
Hint Resolve term_enc_correct : Lrewrite.
  
(* register the non-constant constructors *)
Instance term_var : computableTime var (fun n _ => (1, tt)).
Proof.
  extract constructor. solverec.
Defined.

Instance term_app : computableTime app (fun s1 _ => (1, (fun s2 _ => (1, tt)))).
Proof.
  extract constructor. solverec.
Defined.

Instance term_lam : computableTime lam (fun s _ => (1, tt)).
Proof.
  extract constructor. solverec.
Defined.
