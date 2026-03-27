Set Implicit Arguments.
From Stdlib Require Import List Morphisms Finite.
From Undecidability.HOU Require Import std.tactics std.ars.basic std.ars.confluence.
Import ListNotations ArsInstances.
Section ListRelations.

  Variable (X : Type) (R: X -> X -> Prop).
  Inductive lstep: list X -> list X -> Prop :=
  | stepHead s s' A: R s s' -> lstep (s :: A) (s' :: A)
  | stepTail s A A': lstep A A' -> lstep (s :: A) (s :: A').

  Hint Constructors lstep : core.
  
  Lemma lstep_cons_nil S:
    lstep S nil -> False.
  Proof.
    intros. inv H. 
  Qed.

  Lemma lsteps_cons_nil s S:
    star lstep (s :: S) nil -> False.
  Proof.
    intros. remember (s :: S) as S'. remember nil as T.  revert S s HeqS' HeqT.
    induction H.
    - intros; subst; discriminate.
    - intros; subst. inv H; eapply IHstar; eauto.
  Qed.

  Lemma lstep_nil_cons S:
    lstep nil S -> False.
  Proof.
    intros H. inv H.
  Qed.

  Lemma lsteps_nil_cons s S:
    star lstep nil (s :: S) -> False.
  Proof.
    intros H. inv H.  
    eapply lstep_nil_cons; eauto. 
  Qed.
  
  Lemma lsteps_cons_inv s t S T:
    star lstep (s :: S) (t :: T) -> star R s t /\ star lstep S T.
  Proof.
    intros H. remember (s :: S) as S'. remember (t :: T) as T'.
    revert s t S T HeqS' HeqT'.
    induction H; intros.
    - subst. injection HeqT' as ??; subst. intuition.
    - subst. inv H.
      + destruct (IHstar s' t S T); eauto.
      + destruct (IHstar s t A' T); eauto.
  Qed.
  
  #[export] Instance lsteps_cons :
    Proper (star R ++> star lstep ++> star lstep) cons. 
  Proof.
    intros ??; induction 1; intros ??; induction 1; eauto. 
  Qed.

  Lemma confluence_lstep:
    confluent R -> confluent lstep.
  Proof.
    intros conf ?. induction x; intros.
    - inv H. inv H0. exists nil; eauto. inv H. inv H1.
    - destruct y, z; try solve [exfalso; eapply lsteps_cons_nil; eassumption].
      eapply lsteps_cons_inv in H; eapply lsteps_cons_inv in H0.
      intuition idtac; destruct (IHx _ _ H2 H3) as [V].
      destruct (conf _ _ _ H1 H) as [v].
      exists (v :: V).
      now rewrite H5, H0. now rewrite H6, H4.
  Qed.

  Hint Resolve confluence_lstep : core.

  Lemma normal_lstep_in A:
    Normal lstep A -> forall x, In x A  -> Normal R x.
  Proof.
    induction A; cbn; intuition idtac; subst; trivial.
    intros ? H1. eapply H. constructor. eassumption.
    eapply IHA; trivial. intros ? H2. eapply H.
    econstructor 2; eauto. 
  Qed.


  
  Lemma normal_in_lstep A:
    (forall x, In x A  -> Normal R x) -> Normal lstep A.
  Proof.
    induction A; cbn; intuition idtac. 
    - intros ? H1. inv H1.
    - intros ? H1. inv H1.
      eapply H; eauto.
      eapply IHA; eauto.   
  Qed.


  Lemma lstep_normal_cons_l a A:
    Normal lstep (a :: A) -> Normal R a.
  Proof. intros ? ? ?. eapply H; econstructor; eauto. Qed.
  
  Lemma lstep_normal_cons_r a A:
    Normal lstep (a :: A) -> Normal lstep A.
  Proof. intros ? ? ?. eapply H; econstructor 2; eauto. Qed.
  
  Lemma lstep_normal_cons a A:
    Normal R a -> Normal lstep A -> Normal lstep (a :: A).
  Proof. intros ? ? ? ?. inv H1; firstorder.  Qed.
  
  Lemma lstep_normal_nil:
    Normal lstep nil.
  Proof. intros ? H; inv H. Qed.
  
  Hint Resolve
       lstep_normal_nil
       lstep_normal_cons_l
       lstep_normal_cons_r
       lstep_normal_cons : core.
  
  Hint Resolve normal_lstep_in normal_in_lstep : core.

  Lemma equiv_lstep_cons_inv s t S T:
    equiv lstep (s :: S) (t :: T) -> equiv R s t /\ equiv lstep S T.
  Proof.
    intros H. remember (s :: S) as S'. remember (t :: T) as T'.
    revert s t S T HeqS' HeqT'.
    induction H; intros.
    - subst. injection HeqT' as ??; subst; intuition.
    - subst. inv H.
      + destruct x'. eapply lstep_cons_nil in H1 as [].
        edestruct IHstar; trivial. inv H1.
        * intuition idtac.
          transitivity x; eauto. 
        * intuition idtac. transitivity x'; eauto.
      + destruct x'. eapply lstep_nil_cons in H1 as [].
        edestruct IHstar; trivial. inv H1; intuition idtac. 
        * transitivity x; eauto. 
        * transitivity x'; eauto. 
  Qed.


  #[export] Instance equiv_lstep_cons_proper:
    Proper (equiv R ++> equiv lstep ++> equiv lstep) cons.
  Proof.
    intros ??; induction 1; intros ??; induction 1; [eauto|..].
    - rewrite <-IHstar. destruct H.
      eauto. symmetry. eauto.
    - rewrite <-(IHstar x0 x0); try reflexivity.
      destruct H. eauto. symmetry. eauto.
    - rewrite <-IHstar0.
      destruct H1. eauto. symmetry. eauto.
  Qed.

  Lemma not_equiv_lstep_nil_cons a A:
    ~ equiv lstep nil (a :: A).
  Proof.
    intros H; inv H; inv H0; inv H. 
  Qed.
  
  Lemma list_equiv_ind (P: list X -> list X -> Prop):
    P nil nil ->
    (forall s t S T, equiv R s t -> equiv lstep S T -> P S T -> P (s :: S) (t :: T)) ->
    forall S T, equiv lstep S T -> P S T.
  Proof.
    intros B IH S T H; induction S in T, H |-*; destruct T; trivial.
    - exfalso; eapply not_equiv_lstep_nil_cons; eauto. 
    - exfalso; eapply not_equiv_lstep_nil_cons; symmetry; eauto. 
    - eapply equiv_lstep_cons_inv in H as (? & ?).
      eapply IH; eauto.
  Qed.

End ListRelations.



#[export] Hint Constructors lstep : core.

#[export] Hint Resolve
     lstep_normal_nil
     lstep_normal_cons_l
     lstep_normal_cons_r
     lstep_normal_cons : core.

#[export] Hint Resolve confluence_lstep : core.
#[export] Hint Resolve normal_lstep_in normal_in_lstep : core.
