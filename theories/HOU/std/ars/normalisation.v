Set Implicit Arguments.
From Undecidability.HOU Require Import std.ars.basic.

Set Default Proof Using "Type".

(* Strong normalisation *)
Section StrongNormalisation.

  Variables (X A: Type).
  Variables (R: X -> X -> Prop) (S: A -> A -> Prop).

 
  Inductive SN {X} (R: X -> X -> Prop) : X -> Prop :=
  | SNC x : (forall y, R x y -> SN R y) -> SN R x.

  Lemma SN_ext Q x :
    (forall x y, R x y <-> Q x y) ->
    SN R x <-> SN Q x.
  Proof.
    split; induction 1; econstructor; firstorder.
  Qed.

  Fact SN_unfold x :
    SN R x <-> forall y, R x y -> SN R y.
  Proof.
    split.
    - destruct 1 as [x H]. exact H.
    - intros H. constructor. exact H.
  Qed.

  Fact Normal_SN x :
    Normal R x -> SN R x.
  Proof.
    intros H. constructor. intros y H1.
    exfalso. eapply H; eauto.
  Qed.


  Fact Normal_star_stops x:
    Normal R x -> forall y, star R x y -> x = y.
  Proof.
    destruct 2; firstorder.
  Qed.


  Fact SN_multiple x :
    SN R x <-> SN (multiple R) x.
  Proof.
    split.
    - induction 1 as [x _ IH].
      constructor. induction 1; eauto.
      apply IHmultiple. intros z H1 % multiple_exp.
      destruct (IH x' H) as [H2].
      apply H3. eauto.
    - induction 1 as [x _ IH].
      constructor. intros y H1. apply IH. eauto.
  Qed.

  Definition morphism  (f: X -> A) :=
    forall x y, R x  y -> S (f x) (f y).

  Fact SN_morphism f x :
    morphism f -> SN S (f x) -> SN R x.
  Proof.
    intros H H1.
    remember (f x) as a eqn:H2. revert x H2.
    induction H1 as [a _ IH]. intros x ->.
    constructor. intros y H1 % H.
    apply (IH _ H1). reflexivity.
  Qed.

  Fact SN_finite_steps:
     (forall x, (exists y, R x y) \/ Normal R x) -> forall x, SN R x -> exists2 y, star R x y & Normal R y.
  Proof.
    intros H; induction 1 as [x H1 IH]. destruct (H x) as [[y H2]|].
    + edestruct IH as [z H3 H4]; eauto.
    + eexists; eauto.
  Qed.


End StrongNormalisation.
