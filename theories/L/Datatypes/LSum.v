From Undecidability.L Require Import Tactics.LTactics Datatypes.LBool.
From Undecidability.L Require Import Tactics.GenEncode.

(* ** Encoding of sum type *)
Section Fix_XY.

  Variable X Y:Type.
  
  Variable intX : encodable X.
  Variable intY : encodable Y.

  MetaRocq Run (tmGenEncode "sum_enc" (X + Y)).
  Hint Resolve sum_enc_correct : Lrewrite.

  Global Instance encInj_sum_enc {H : encInj intX} {H' : encInj intY} : encInj (encodable_sum_enc).
  Proof. register_inj. Qed. 
  
  (* now we must register the non-constant constructors*)
  
  Global Instance term_inl : computable (@inl X Y).
  Proof.
    extract constructor.
  Qed.

   Global Instance term_inr : computable (@inr X Y).
  Proof.
    extract constructor.
  Qed.
  
End Fix_XY.

#[export] Hint Resolve sum_enc_correct : Lrewrite.

Section sum_eqb.

  Variable X Y : Type.
  Variable eqb__X : X -> X -> bool.
  Variable spec__X : forall x y, reflect (x = y) (eqb__X x y).
  Variable eqb__Y : Y -> Y -> bool.
  Variable spec__Y : forall x y, reflect (x = y) (eqb__Y x y).

  Definition sum_eqb (A B : X + Y) :=
    match A,B with
    | inl a,inl b => eqb__X a b
    | inr a,inr b => eqb__Y a b
    | _,_ => false
    end.

  Lemma sum_eqb_spec A B : reflect (A = B) (sum_eqb A B).
  Proof using spec__X spec__Y.
    destruct A, B; (try now econstructor);cbn.
    -destruct (spec__X x x0); econstructor;congruence.
    -destruct (spec__Y y y0); constructor;congruence.
  Qed.
End sum_eqb.

From Undecidability Require Import EqBool.

Section int.

  Variable X Y:Type.
  Context {HX : encodable X} {HY : encodable Y}.

  Global Instance eqbSum f g `{eqbClass (X:=X) f} `{eqbClass (X:=Y) g}:
    eqbClass (sum_eqb f g).
  Proof.
    intros ? ?. eapply sum_eqb_spec. all:eauto using eqb_spec.
  Qed.

  Global Instance eqbComp_sum `{H:eqbComp X (R:=HX)} `{H':eqbComp Y (R:=HY)}:
    eqbComp (sum X Y).
  Proof.
    constructor. unfold sum_eqb.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract.
  Qed.

End int.
