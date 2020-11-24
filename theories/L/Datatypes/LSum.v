From Undecidability.L Require Import Tactics.LTactics Datatypes.LBool.
From Undecidability.L Require Import Tactics.GenEncode.

(* ** Encoding of sum type *)
Section Fix_XY.

  Variable X Y:Type.
  
  Variable intX : registered X.
  Variable intY : registered Y.

  MetaCoq Run (tmGenEncode "sum_enc" (X + Y)).
  Hint Resolve sum_enc_correct : Lrewrite.
  
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

Hint Resolve sum_enc_correct : Lrewrite.

Lemma size_sum X Y `{registered X} `{registered Y} (l: X + Y):
  size (enc l) = match l with inl x => size (enc x) + 5 | inr x => size (enc x) + 4 end.
Proof.
  change (enc l) with (sum_enc _ _ l).
  destruct l as [x|x]. all:cbn [sum_enc map sumn size]. 
  all:change ((match _ with
           | @mk_registered _ enc _ _ => enc
           end x)) with (enc x).
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
  Proof.
    destruct A, B; (try now econstructor);cbn.
    -destruct (spec__X x x0); econstructor;congruence.
    -destruct (spec__Y y y0); constructor;congruence.
  Qed.
End sum_eqb.

From Undecidability Require Import EqBool.

Section int.

  Variable X Y:Type.
  Context {HX : registered X} {HY : registered Y}.

  (*Global Instance term_sum_eqb : computableTime' (@sum_eqb X Y)
                                                    (fun eqb eqbX => (1, (fun _ eqbY => (1,fun a _ => (1,fun b _ => (match a,b with
                                                                                            inl a, inl b => callTime2 eqbX a b + 10
                                                                                          | inr a, inr b => callTime2 eqbY a b + 10

                                                                                          | _,_ => 9 end,tt)))))). 
  Proof.
    extract. solverec.
  Defined. *)

  Global Instance eqbSum f g `{eqbClass (X:=X) f} `{eqbClass (X:=Y) g}:
    eqbClass (sum_eqb f g).
  Proof.
    intros ? ?. eapply sum_eqb_spec. all:eauto using eqb_spec.
  Qed.

  Global Instance eqbComp_sum `{H:eqbCompT X (R:=HX)} `{H':eqbCompT Y (R:=HY)}:
    eqbCompT (sum X Y).
  Proof.
    evar (c:nat). exists c. unfold sum_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract. unfold eqb,eqbTime.
    fold (enc (X:=X)).  fold (enc (X:=Y)).
    recRel_prettify2. easy.
    [c]:exact (c__eqbComp X + c__eqbComp Y + 6).
    all:unfold c. all:cbn iota beta delta [sum_enc].
    all:  change ((match HX with
           | @mk_registered _ enc _ _ => enc
                   end)) with (enc (X:=X)).
    all:  change ((match HY with
           | @mk_registered _ enc _ _ => enc
           end)) with (enc (X:=Y)).
    all:cbn [size]. all: nia.
  Qed.

End int.
