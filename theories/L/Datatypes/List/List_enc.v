From Undecidability.L.Tactics Require Import LTactics GenEncode.

(* ** Encoding of lists *)

Section Fix_X.
  Variable (X:Type).
  Context {intX : encodable X}.

  MetaCoq Run (tmGenEncode "list_enc" (list X)).

  Global Instance encInj_list_enc {H : encInj intX} : encInj (encodable_list_enc).
  Proof. register_inj. Qed. 

  (* now we must register the non-constant constructors*)
  
  Global Instance termT_cons : computable (@cons X).
  Proof.
    extract constructor.
  Qed.
End Fix_X.

#[export] Hint Resolve list_enc_correct : Lrewrite.
