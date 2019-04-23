From Undecidability.L Require Export L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
(** * Encodings and extracted basic functions *)
(** ** Encoding of unit *)

Run TemplateProgram (tmGenEncode "unit_enc" unit).
Hint Resolve unit_enc_correct : Lrewrite.
