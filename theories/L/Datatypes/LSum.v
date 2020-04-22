From Undecidability.L Require Import Tactics.LTactics Datatypes.LBool.
From Undecidability.L Require Import Tactics.GenEncode.

(** ** Encoding of sum type *)
Section Fix_XY.

  Variable X Y:Type.
  
  Variable intX : registered X.
  Variable intY : registered Y.

  Run TemplateProgram (tmGenEncode "sum_enc" (X + Y)).
  Hint Resolve sum_enc_correct : Lrewrite.
  
  (* now we must register the non-constant constructors*)
  
  Global Instance term_inl : computableTime' (@inl X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.

   Global Instance term_inr : computableTime' (@inr X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.
  
End Fix_XY.

Hint Resolve sum_enc_correct : Lrewrite.

Lemma size_sum X Y `{registered X} `{registered Y} (l: X + Y):
  size (enc l) = match l with inl x => size (enc x) + 5 | inr x => size (enc x) + 4 end.
Proof.
  change (enc l) with (sum_enc _ _ l).
  destruct l as [x|x]. all:cbn [sum_enc map sumn size]. 
  all:change ((match _ with
           | @mk_registered _ enc _ _ => enc
           end x)) with (enc x).
  all:lia. 
Qed.
