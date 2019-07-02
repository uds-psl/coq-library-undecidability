From Undecidability.L Require Import Tactics.LTactics Datatypes.LBool.
From Undecidability.L Require Import Tactics.GenEncode.

(** ** Encoding of sum type *)
Section Fix_XY.
  Variable X Y:Type.
  Context {intX : registered X}.
  Context {intY : registered Y}.

  
  
  Run TemplateProgram (tmGenEncode "sum_enc" (sum X Y)).
  Hint Resolve sum_enc_correct : Lrewrite.
  
  (* now we must register the non-constant constructors*)
  
  Global Instance term_inl : computableTime' (@inl X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Defined.

   Global Instance term_inr : computableTime' (@inr X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Defined.
End Fix_XY.
Hint Resolve sum_enc_correct : Lrewrite.
