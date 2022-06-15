From Undecidability.L.Tactics Require Import GenEncode.
(* * Encodings and extracted basic functions *)
(* ** Encoding of unit *)

MetaCoq Run (tmGenEncodeInj "unit_enc" unit).
#[export] Hint Resolve unit_enc_correct : Lrewrite.
