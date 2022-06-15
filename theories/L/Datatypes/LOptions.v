From Undecidability.L Require Import Tactics.LTactics Datatypes.LBool Tactics.GenEncode.

(* ** Encoding of option type *)
Section Fix_X.
  Variable X:Type.
  Context {intX : encodable X}.

  MetaCoq Run (tmGenEncode "option_enc" (option X)).
  Hint Resolve option_enc_correct : Lrewrite.

  Global Instance encInj_option_enc {H : encInj intX} : encInj (encodable_option_enc).
  Proof. register_inj. Qed. 

  (* now we must register the non-constant constructors*)

  Global Instance term_Some : computable (@Some X).
  Proof.
    extract constructor.
  Qed.

End Fix_X.

#[export] Hint Resolve option_enc_correct : Lrewrite.

Section option_eqb.

  Variable X : Type.
  Variable eqb : X -> X -> bool.
  Variable spec : forall x y, reflect (x = y) (eqb x y).

  Definition option_eqb (A B : option X) :=
    match A,B with
    | None,None => true
    | Some x, Some y => eqb x y
    | _,_ => false
    end.

  Lemma option_eqb_spec A B : reflect (A = B) (option_eqb A B).
  Proof using spec.
    destruct A, B; try now econstructor. cbn.
    destruct (spec x x0); econstructor; congruence.
  Qed.
End option_eqb.

Section int.

  Variable X:Type.
  Context {HX : encodable X}.

  Global Instance term_option_eqb : computable (@option_eqb X).
  Proof.
    extract.
  Qed.

  Global Instance eqbOption f `{eqbClass (X:=X) f}:
    eqbClass (option_eqb f).
  Proof.
    intros ? ?. eapply option_eqb_spec. all:eauto using eqb_spec.
  Qed.
End int.

Definition isSome {T} (u : option T) := match u with Some _ => true | _ => false end.

#[global]
Instance term_isSome {T} `{encodable T} : computable (@isSome T).
Proof.
  extract.
Qed.

