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

Section int.

  Variable X Y:Type.
  Context {HX : registered X} {HY : registered Y}.

  Global Instance eqbSum f g `{eqbClass (X:=X) f} `{eqbClass (X:=Y) g}:
    eqbClass (sum_eqb f g).
  Proof.
    intros ? ?. eapply sum_eqb_spec. all:eauto using eqb_spec.
  Qed.

End int.
