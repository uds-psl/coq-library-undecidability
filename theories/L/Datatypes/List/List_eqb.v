From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L Require Import UpToC.
From Undecidability.L Require Import Functions.EqBool.

From Undecidability.L.Datatypes Require Export List.List_enc LBool LOptions LNat.

Set Default Proof Using "Type".

Section Fix_X.
  Variable (X:Type).
  Context {intX : registered X}.

  Fixpoint inb eqb (x:X) (A: list X) :=
    match A with
      nil => false
    | a::A' => orb (eqb a x) (inb eqb x A')
    end.

  Variable X_eqb : X -> X -> bool.
  Hypothesis X_eqb_spec : (forall (x y:X), Bool.reflect (x=y) (X_eqb x y)).

  Lemma inb_spec: forall x A, Bool.reflect (In x A) (inb X_eqb x A).
  Proof using X_eqb_spec.
    intros x A. induction A.
    -constructor. tauto.
    -simpl. destruct (X_eqb_spec a x).
    +constructor. tauto.
    +inv IHA. destruct (X_eqb_spec a x).
      *constructor. tauto.
      *constructor. tauto.
      *constructor. tauto.
  Qed.

  Global Instance term_inb: computableTime' inb (fun eq eqT => (5,fun x _ => (1,fun l _ =>
                                        (fold_right (fun x' res => callTime2 eqT x' x
                                                                + res + 17) 4 l ,tt)))).
  Proof.
    extract.
    solverec. 
  Defined.

  Global Instance term_inb_notime: computable inb.
  Proof.
    extract.
  Defined.



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
  Context {HX : registered X}.

  Fixpoint list_eqbTime (eqbT: timeComplexity (X -> X -> bool)) (A B:list X) :=
    match A,B with
      a::A,b::B => callTime2 eqbT a b + 22 + list_eqbTime eqbT A B
    | _,_ => 9
    end.

  Global Instance term_list_eqb : computableTime' (list_eqb (X:=X))
                                                  (fun _ eqbT => (1,(fun A _ => (5,fun B _ => (list_eqbTime eqbT A B,tt))))).
  Proof.
    extract.
    solverec.                                                                                             
  Defined.

  Definition list_eqbTime_leq (eqbT: timeComplexity (X -> X -> bool)) (A B:list X) k:
    (forall a b, callTime2 eqbT a b <= k)
    -> list_eqbTime eqbT A B <= length A * (k+22) + 9.
  Proof.
    intros H'. induction A in B|-*.
    -cbn. lia.
    -destruct B.
    {cbn. intuition. }
    cbn - [callTime2]. setoid_rewrite IHA.
    rewrite H'. ring_simplify. intuition.
  Qed.


  Lemma list_eqbTime_bound_r (eqbT : timeComplexity (X -> X -> bool)) (A B : list X) f:
    (forall (x y:X), callTime2 eqbT x y <= f y) ->
    list_eqbTime eqbT A B <= sumn (map f B) + 9 + length B * 22.
  Proof.
    intros H.
    induction A in B|-*;unfold list_eqbTime;fold list_eqbTime. now Lia.lia.
    destruct B.
    -cbn. Lia.lia.
    -rewrite H,IHA. cbn [length map sumn]. Lia.lia.
  Qed.

  Global Instance eqbList f `{eqbClass (X:=X) f}:
    eqbClass (list_eqb f).
  Proof.
    intros ? ?. eapply list_eqb_spec. all:eauto using eqb_spec.
  Qed.
  Import EqBool.
  Global Instance eqbComp_List `{eqbCompT X (R:=HX)}:
    eqbCompT (list X).
  Proof.
    evar (c:nat). exists c. unfold list_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    extract. unfold eqb,eqbTime. fold @enc.
    recRel_prettify2. easy.
    [c]:exact (c__eqbComp X + 6).
    all:unfold c. all:cbn iota beta delta [list_enc].
    all:  change ((match HX with
                  | @mk_registered _ enc _ _ => enc
                  end)) with (enc (X:=X)).
    all:cbn [size]. all: nia.
  Qed.

End int.
