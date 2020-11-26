From Undecidability.L Require Export L Tactics.LTactics GenEncode.

From Undecidability.L.Datatypes Require Import LBool.

From Undecidability.L Require Import Functions.EqBool GenEncode.
(*
From Undecidability.L Require Import LNat.*)

(* ** Encoding of pairs *)

Section Fix_XY.

  Variable X Y:Type.
  
  Context {intX : registered X}.
  Context {intY : registered Y}.

  MetaCoq Run (tmGenEncode "prod_enc" (X * Y)).
  Hint Resolve prod_enc_correct : Lrewrite.
  
  (* now we must register the constructors*)
  Global Instance term_pair : computableTime' (@pair X Y) (fun _ _ => (1,fun _ _ => (1,tt))).
  Proof.
    extract constructor. solverec. 
  Qed.

  Global Instance term_fst : computableTime' (@fst X Y) (fun _ _ => (5,tt)).
  Proof.
    extract. solverec.
  Qed.

  Global Instance term_snd : computableTime' (@snd X Y) (fun _ _ => (5,tt)).
  Proof.
    extract. solverec.
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

  Global Instance eqbComp_Prod `{eqbCompT X (R:=intX)} `{eqbCompT Y (R:=intY)}:
    eqbCompT (X*Y).
  Proof.
    evar (c:nat). exists c. unfold prod_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract. unfold eqb,eqbTime. fold @enc.
    recRel_prettify2. easy.
    [c]:exact (c__eqbComp X + c__eqbComp Y + 6).
    all:unfold c. cbn iota delta [prod_enc].
    fold (@enc X _). fold (@enc Y _). 
    cbn [size].  nia.
  Qed.


  (*
  Global Instance term_prod_eqb :
    computableTime' prod_eqb
                     (fun _ eqT1 =>
                        (1,fun _ eqT2 =>
                             (1,fun x _ =>
                                  (1,fun y _ =>
                                       (let '(k1,eqT1') := (eqT1 (fst x) tt) in
                                                             k1 +fst (eqT1' (fst y) tt)
                                       + (let '(k2,eqT2') := (eqT2 (snd x) tt) in
                                           k2 +fst (eqT2' (snd y) tt)) + 14, tt))))).
  Proof.
    extract. solverec. 
  Qed.

  Global Instance term_prod_eqb_notime :
    computable prod_eqb.
  Proof.
    extract. 
  Qed. *)

  
  Lemma size_prod (w:X*Y):
    size (enc w) = size (enc (fst w)) + size (enc (snd w)) + 4.
  Proof.
    destruct w. unfold enc. now cbn.
  Qed.

  
End Fix_XY.

Hint Resolve prod_enc_correct : Lrewrite.
