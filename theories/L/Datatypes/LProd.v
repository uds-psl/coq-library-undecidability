From Undecidability.L Require Export L Tactics.LTactics GenEncode.

From Undecidability.L.Datatypes Require Import LBool.

From Undecidability.L Require Import Functions.EqBool GenEncode.
(*
From Undecidability.L Require Import LNat.*)

(* ** Encoding of pairs *)

Section Fix_XY.

  Variable X Y:Type.
  
  Context {intX : encodable X}.
  Context {intY : encodable Y}.

  MetaRocq Run (tmGenEncode "prod_enc" (X * Y)).
  Hint Resolve prod_enc_correct : Lrewrite.

  Global Instance encInj_prod_enc {H : encInj intX} {H' : encInj intY} : encInj (encodable_prod_enc).
  Proof. register_inj. Qed. 
  
  (* now we must register the constructors*)
  Global Instance term_pair : computable (@pair X Y).
  Proof.
    extract constructor.
  Qed.

  Global Instance term_fst : computable (@fst X Y).
  Proof.
    extract.
  Qed.

  Global Instance term_snd : computable (@snd X Y).
  Proof.
    extract.
  Qed.

  Definition prod_eqb f g (a b: X*Y):=
    let (x1,y1):= a in
    let (x2,y2):= b in
    andb (f x1 x2) (g y1 y2).

  Lemma prod_eqb_spec f g:
    (forall (x1 x2 : X) , reflect (x1 = x2) (f x1 x2))
    -> (forall (y1 y2 : Y) , reflect (y1 = y2) (g y1 y2))
    -> forall x y, reflect (x=y) (prod_eqb f g x y).
  Proof with try (constructor;congruence).
    intros Hf Hg [x1 y1] [x2 y2].
    specialize (Hf x1 x2); specialize (Hg y1 y2);cbn. 
    inv Hf;inv Hg;cbn...
  Qed.

  Global Instance eqbProd f g `{eqbClass (X:=X) f} `{eqbClass (X:=Y) g}:
    eqbClass (prod_eqb f g).
  Proof.
    intros ? ?. eapply prod_eqb_spec. all:eauto using eqb_spec.
  Qed.

  
  Global Instance eqbComp_Prod `{eqbComp X (R:=intX)} `{eqbComp Y (R:=intY)}:
    eqbComp (X*Y).
  Proof.
    constructor. unfold prod_eqb.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract.
  Qed.
  
End Fix_XY.

#[export] Hint Resolve prod_enc_correct : Lrewrite.
