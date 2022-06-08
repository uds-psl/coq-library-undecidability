From Undecidability.L Require Export L Tactics.LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LBool.
From Undecidability.L Require Import Functions.EqBool GenEncode.

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

End Fix_XY.

#[global]
Instance term_prod_eqb X Y `{eqbCompT X} `{eqbCompT Y} : computable (@prod_eqb X Y eqb eqb).
Proof.
  apply computableExt with (x := fun a b : X * Y => eqb0 (fst a) (fst b) && eqb1 (snd a) (snd b)).
  { now intros [??] [??]. }
  extract.
Qed.

#[global]
Instance inst_eqbCompT_prod X Y `{eqbCompT X} `{eqbCompT Y} : eqbCompT (X * Y).
Proof.
  constructor. now apply term_prod_eqb.
Qed.

#[export] Hint Resolve prod_enc_correct : Lrewrite.
