(*
Parts of this file are copied and modified from the Coq Demos of the lecture Semantics at UdS:
http://www.ps.uni-saarland.de/courses/sem-ws17/confluence.v
 *)

Set Implicit Arguments.
From Stdlib Require Import Morphisms Finite ConstructiveEpsilon.
From Undecidability.HOU Require Import std.tactics std.decidable std.misc std.ars.basic std.ars.confluence.
Import ArsInstances.
Section Evaluator.

  Variables (X: Type) (R: X -> X -> Prop) (rho: X -> X). 
  
  Definition red_fun rho :=
    (forall x, star R x (rho x)) /\
    (forall x y, evaluates R x y -> exists n, it n rho x = y).
  
  Variables (red: red_fun rho).


  Fact red_fun_fp x :
    Normal R x -> rho x = x.
  Proof using red.
    intros H. symmetry.
    eapply Normal_star_stops; eauto.
    apply red.
  Qed.

  Fact red_fun_fp_it x n :
    Normal R x -> it n rho x = x.
  Proof using red.
    intros H.
    induction n as [|n IH]; cbn.
    - reflexivity.
    - rewrite IH. apply red_fun_fp, H.
  Qed.

  Variable (delta: Dec1 (Normal R)). 

  Fixpoint E n x : option X :=
    match n with
    | 0 => None
    | S n' => if delta x then Some x else E n' (rho x)
    end.

  Fact E_S n x :
    E (S n) x = if delta x then Some x else E n (rho x).
  Proof.
    reflexivity.
  Qed.

  Fact E_it x n :
    Normal R (it n rho x) -> E (S n) x = Some (it n rho x).
  Proof using red.
    revert x.
    induction n as [|n IH]; intros x.
    - cbn. destruct (delta x) as [H|H]; tauto.
    - cbn [it]. rewrite it_commute. intros H1 % IH.
      rewrite E_S.
      destruct (delta x) as [H|H]; [|exact H1].
      rewrite red_fun_fp; [|exact H].
      rewrite red_fun_fp_it; [|exact H].
      reflexivity.
  Qed.

  Fact E_correct x y :
    evaluates R x y <-> exists n, E n x = Some y.
  Proof using red.
    split.
    - intros H. generalize H. intros [n <-] % red.
      exists (S n). apply E_it, H.
    - intros [n H]; revert x H.
      induction n as [|n IH]; cbn; intros x.
      + discriminate.
      + destruct (delta x) as [H|H]; intros H1.
        * assert (x=y) as <- by congruence.
          split; auto.
        * apply IH in H1 as [H1 H2].
          split; [|exact H2].
          rewrite <- H1. apply red.
  Qed.

  Fact E_unique n m x y1 y2:
    E n x = Some y1 -> E m x = Some y2 -> y1 = y2.
  Proof.
    induction n in x, m |-*; destruct m; try discriminate.
    cbn; destruct delta; eauto; now intros [= ->] [= ->].
  Qed.

  Fact E_stops n x:
    Normal R x -> E (S n) x = Some x.
  Proof. cbn; destruct delta; intuition. Qed.

  Fact E_step n x y:
    E n x = Some y -> E (S n) x = Some y.
  Proof.
    induction n in x, y |-*; cbn; try discriminate.
    destruct (delta x); eauto.
  Qed.
      

  Fact E_monotone n m x y:
    n <= m ->  E n x = Some y -> E m x = Some y.
  Proof.
    induction 1 in x, y |-*; eauto using E_step.
  Qed.    

End Evaluator.


Section EvaluatorTakahashi.
  Variable (X: Type) (R S: X -> X -> Prop).
  Hypothesis (D: Dec1 (Normal R)).

  Variable (rho: X -> X).
  Hypotheses (tf: tak_fun S rho).
  Hypotheses (refl: Reflexive S) (H1: subrelation R S)
             (H2: subrelation S (star R)).
  

  Lemma rho_evaluates:
    forall x y : X, evaluates R x y -> exists n : nat, it n rho x = y.
  Proof using H1 H2 S tf.
    intros x y [H3 H4].
    eapply sandwich_equiv with (S := S) in H3; eauto. 
    eapply tak_cofinal in H3; eauto.
    destruct H3 as [n H3]; exists n.
    eapply sandwich_equiv with (S := S) in H3; eauto. 
    now eapply Normal_star_stops in H3. 
  Qed.


  Lemma red_fun_rho: red_fun R rho.
  Proof using H1 H2 S tf refl.
    split.
    - intros x. eapply H2, tf, refl. 
    - eapply rho_evaluates.
  Qed.


  Lemma evaluates_E s:
    (exists t, evaluates R s t) -> exists n, exists t, E rho D n s = Some t.
  Proof using H1 H2 S tf refl.
    intros [t H]; destruct (E_correct red_fun_rho D s t) as [H3 _].
    eapply H3 in H. destruct H as [n]. exists n. now (exists t). 
  Qed.

  Instance decidable_E s n:
    Dec (exists t, E rho D n s = Some t).
  Proof.
    destruct (E rho D n s).
    - left; eexists; eauto.
    - right; intros []; discriminate.
  Qed.
                         

  Lemma E_evaluates (s: X):
    { n: nat | exists t, E rho D n s = Some t } -> { t | evaluates R s t }.
  Proof using H1 H2 S tf refl.
    intros [n H].
    destruct (E rho D n s) as [t|] eqn: H3.
    - exists t. eapply E_correct; eauto using red_fun_rho.
    - exfalso. destruct H. discriminate.
  Qed.

  Lemma compute_evaluation (s: X):
    (exists t, evaluates R s t) -> { t | evaluates R s t }.
  Proof using H1 H2 S tf refl rho D.
    intros.
    eapply E_evaluates.
    eapply constructive_indefinite_ground_description
      with (f := id) (g := id); eauto.
    - eapply decidable_E.
    - eapply evaluates_E, H.
  Qed.

End EvaluatorTakahashi.  
