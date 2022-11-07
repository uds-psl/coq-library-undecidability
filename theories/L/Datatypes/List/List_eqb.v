From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L Require Import Functions.EqBool.

From Undecidability.L.Datatypes Require Export List.List_enc LBool LOptions LNat.

Section Fix_X.
  Variable (X:Type).
  Context {intX : encodable X}.

  Fixpoint inb eqb (x:X) (A: list X) :=
    match A with
      nil => false
    | a::A' => orb (eqb a x) (inb eqb x A')
    end.

  Variable X_eqb : X -> X -> bool.
  Hypothesis X_eqb_spec : (forall (x y:X), Bool.reflect (x=y) (X_eqb x y)).

  Global Instance term_inb: computable inb.
  Proof.
    extract.
  Defined. (*because other extract*)

End Fix_X.

Section list_eqb.

  Variable X : Type.
  Variable eqb : X -> X -> bool.
  Variable spec : forall x y, reflect (x = y) (eqb x y).

  Fixpoint list_eqb A B :=
    match A,B with
    | nil,nil => true
    | a::A',b::B' => eqb a b && list_eqb A' B'
    | _,_ => false
    end.

  Lemma list_eqb_spec A B : reflect (A = B) (list_eqb A B).
  Proof using spec.
    revert B; induction A; intros; destruct B; cbn in *; try now econstructor.
    destruct (spec a x), (IHA B); cbn; econstructor; congruence.
  Qed.

End list_eqb.

Section int.

  Context {X : Type}.
  Context {HX : encodable X}.

  Global Instance term_list_eqb : computable (list_eqb (X:=X)).
  Proof.
    extract.
  Qed.

  Global Instance eqbList f `{eqbClass (X:=X) f}:
    eqbClass (list_eqb f).
  Proof.
    intros ? ?. eapply list_eqb_spec. all:eauto using eqb_spec.
  Qed.
  Import EqBool.
  Global Instance eqbComp_List `{eqbComp X (R:=HX)}:
    eqbComp (list X).
  Proof.
    constructor. unfold list_eqb.
    extract.
  Qed.
End int.
