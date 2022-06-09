From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L Require Import Datatypes.LBool GenEncode.

(* ** Encoding of pairs *)

Section Fix_XY.

  Variable X Y:Type.
  
  Context {intX : registered X}.
  Context {intY : registered Y}.

  MetaCoq Run (tmGenEncode "prod_enc" (X * Y)).
  Hint Resolve prod_enc_correct : Lrewrite.
  
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

  Variable eqbX : X -> X -> bool.
  Variable eqbY : Y -> Y -> bool.
  Context {HeqbX : computable eqbX}.
  Context {HeqbY : computable eqbY}.

  #[global]
  Instance term_prod_eqb : computable (prod_eqb eqbX eqbY).
  Proof using HeqbX HeqbY.
    apply computableExt with (x := fun a b : X * Y => eqbX (fst a) (fst b) && eqbY (snd a) (snd b)).
    { now intros [??] [??]. }
    extract.
  Qed.

End Fix_XY.

#[export] Hint Resolve prod_enc_correct : Lrewrite.
