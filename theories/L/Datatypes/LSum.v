From Undecidability.L Require Import Tactics.LTactics Datatypes.LBool.
From Undecidability.L Require Import Tactics.GenEncode.

(* ** Encoding of sum type *)
Section Fix_XY.

  Variable X Y:Type.
  
  Variable intX : encodable X.
  Variable intY : encodable Y.

  MetaCoq Run (tmGenEncode "sum_enc" (X + Y)).
  Hint Resolve sum_enc_correct : Lrewrite.

  Global Instance encInj_sum_enc {H : encInj intX} {H' : encInj intY} : encInj (encodable_sum_enc).
  Proof. register_inj. Qed. 
  
  (* now we must register the non-constant constructors*)
  
  Global Instance term_inl : computableTime' (@inl X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.

   Global Instance term_inr : computableTime' (@inr X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.
  
End Fix_XY.

#[export] Hint Resolve sum_enc_correct : Lrewrite.

Lemma size_sum X Y `{encodable X} `{encodable Y} (l: X + Y):
  size (enc l) = match l with inl x => size (enc x) + 5 | inr x => size (enc x) + 4 end.
Proof.
  unfold enc at 1.
  destruct l as [x|x]. all:cbn.
  all:lia. 
Qed.


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

  (*Global Instance term_sum_eqb : computableTime' (@sum_eqb X Y)
                                                    (fun eqb eqbX => (1, (fun _ eqbY => (1,fun a _ => (1,fun b _ => (match a,b with
                                                                                            inl a, inl b => callTime2 eqbX a b + 10
                                                                                          | inr a, inr b => callTime2 eqbY a b + 10

                                                                                          | _,_ => 9 end,tt)))))). 
  Proof.
    extract. solverec.
  Defined. (*comment *) *)

  Global Instance eqbSum f g `{eqbClass (X:=X) f} `{eqbClass (X:=Y) g}:
    eqbClass (sum_eqb f g).
  Proof.
    intros ? ?. eapply sum_eqb_spec. all:eauto using eqb_spec.
  Qed.

  Global Instance eqbComp_sum `{H:eqbCompT X (R:=HX)} `{H':eqbCompT Y (R:=HY)}:
    eqbCompT (sum X Y).
  Proof.
    evar (c:nat). exists c. unfold sum_eqb.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract. unfold eqb,eqbTime.
    all:set (f:=enc (X:=X + Y)); unfold enc in f;subst f;cbn - ["+"].
    recRel_prettify2. all:cbn [size].
    [c]:exact (c__eqbComp X + c__eqbComp Y + 6).
    all:unfold c. all:nia. 
  Qed.

End int.
