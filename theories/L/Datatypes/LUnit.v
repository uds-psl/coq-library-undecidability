From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
(* * Encodings and extracted basic functions *)
(* ** Encoding of unit *)

MetaCoq Run (tmGenEncodeInj "unit_enc" unit).
#[export] Hint Resolve unit_enc_correct : Lrewrite.
