From Undecidability.L Require Export L Tactics.LTactics.

From Undecidability.L.Datatypes Require Import LNat.

(** ** Encoding of sums *)

Section Fix_XY.

  Variable X Y:Type.
  
  Variable intX : registered X.
  Variable intY : registered Y.

  Run TemplateProgram (tmGenEncode "sum_enc" (X + Y)).
  Hint Resolve sum_enc_correct : Lrewrite.
  
  (* now we must register the constructors*)
  Global Instance term_inl : computable inl.
  Proof.
    extract constructor.
  Qed.

  Global Instance term_inr : computable inr.
  Proof.
    extract constructor.
  Qed.
  
End Fix_XY.

Hint Resolve sum_enc_correct : Lrewrite.
