Require Import List.
Import ListNotations.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Import PCPListNotation.

Set Implicit Arguments. 
Unset Strict Implicit.

Lemma tau1_app {X : Type} (A B: stack X) : tau1 (A ++ B) = tau1 A ++ tau1 B.
Proof.
  induction A; cbn; auto. destruct a. rewrite <- app_assoc. congruence.
Qed.

Lemma tau2_app {X : Type} (A B: stack X) : tau2 (A ++ B) = tau2 A ++ tau2 B.
Proof.
  induction A; cbn; auto. destruct a. rewrite <- app_assoc. congruence.
Qed.

Lemma tau1_inv (a : nat) B z :
tau1 B = a :: z ->
exists x y, (a :: x, y) el B.
Proof.
induction B; cbn; intros; inv H.
destruct a0 as ([],y).
- cbn in H1. firstorder.
- cbn in H1. inv H1. eauto.
Qed.

Lemma tau2_inv (a : nat) B z :
tau2 B = a :: z ->
exists x y, (y, a :: x) el B.
Proof.
induction B; cbn; intros; inv H.
destruct a0 as (x,[]).
- cbn in H1. firstorder.
- cbn in H1. inv H1. eauto.
Qed.

Definition cards {X : Type} (x: list X) := map (fun a => ([a], [a])) x.

Lemma tau1_cards {X : Type} (x: list X) : tau1 (cards x) = x.
Proof.
  induction x; cbv in *; try rewrite IHx; trivial.
Qed.

Lemma tau2_cards {X : Type} (x: list X) : tau2 (cards x) = x.
Proof.
  induction x; cbv in *; try rewrite IHx; trivial.
Qed.


Lemma itau1_app {X : Type} {P : stack X} A B : itau1 P (A++B) = itau1 P A ++ itau1 P B.
Proof. induction A; simpl; auto; rewrite app_ass; simpl; f_equal; auto. Qed.

Lemma itau2_app {X : Type} {P : stack X} A B : itau2 P (A++B) = itau2 P A ++ itau2 P B.
Proof. induction A; simpl; auto; rewrite app_ass; simpl; f_equal; auto. Qed.

Definition card_eq : forall x y : card bool, {x = y} + {x <> y}.
Proof.
  intros. repeat decide equality.
Defined.

Global Hint Rewrite (@tau1_app nat) (@tau2_app nat) (@tau1_cards nat) (@tau2_cards nat) : list.

Implicit Types a b : nat.
Implicit Types x y z : string nat.
Implicit Types d e : card nat.
Implicit Types A R P : stack nat.


Fixpoint sym (R : stack nat) :=
  match R with
    [] => []
  | (x, y) :: R => x ++ y ++ sym R
  end.

Lemma sym_app P R :
  sym (P ++ R) = sym P ++ sym R.
Proof.
  induction P as [ | [] ]; eauto; cbn; rewrite IHP. now rewrite <- ? app_assoc.
Qed.

Lemma sym_map X (f : X -> card nat) l Sigma :
  (forall x : X, x el l -> sym [f x] <<= Sigma) -> sym (map f l) <<= Sigma.
Proof.
  intros. induction l as [ | ]; cbn in *.
  - firstorder.
  - pose proof (H a). destruct (f a). repeat eapply incl_app.
    + eapply app_incl_l, H0. eauto.
    + eapply app_incl_l, app_incl_R; eauto.
    + eauto.
Qed. 

Lemma sym_word_l R u v  :
  (u, v) el R -> u <<= sym R.
Proof.
  induction R; cbn; intros.
  - tauto.
  - destruct a as (u', v'). destruct H.
    + inv H. intros x Hx. eapply in_app_iff. now left.
    + intros x Hx. rewrite ? in_app_iff. right. right. now eapply IHR.
Qed.

Lemma sym_word_R R u v  :
  (u, v) el R -> v <<= sym R.
Proof.
  induction R; cbn; intros.
  - tauto.
  - destruct a as (u', v'). destruct H.
    + inv H. intros x Hx. rewrite ? in_app_iff. right. now left.
    + intros x Hx. rewrite ? in_app_iff. right. right. now eapply IHR.
Qed.

#[export] Hint Resolve sym_word_l sym_word_R : core.

Lemma sym_mono A P :
  A <<= P -> sym A <<= sym P.
Proof.
  induction A as [ | (x,y) ]; cbn; intros.
  - firstorder.
  - eapply incl_app; try eapply incl_app. 
    + eapply sym_word_l. eapply H. now left.
    + eapply sym_word_R. eapply H. now left.
    + eapply IHA. eapply cons_incl. eassumption.
Qed.

Lemma tau1_sym A : tau1 A <<= sym A.
Proof.
  induction A as [ | (x & y) ].
  - firstorder.
  - cbn. intros ? [ | ] % in_app_iff. eapply in_app_iff. eauto.
    rewrite !in_app_iff. eauto.
Qed.

Lemma tau2_sym A : tau2 A <<= sym A.
Proof.
  induction A as [ | (x & y) ].
  - firstorder.
  - cbn. intros ? [ | ] % in_app_iff. rewrite ? in_app_iff. eauto.
    rewrite !in_app_iff. eauto.
Qed.  

Coercion sing (n : nat) := [n].

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability Require Export PCP.PCP.
From Undecidability.Shared Require Export ListAutomation.
Import ListAutomationNotations.

Lemma stack_discrete :
  discrete (stack bool).
Proof. 
  eapply discrete_iff; econstructor. intros ? ?. hnf. repeat decide equality.
Qed.

Lemma stack_enum :
  enumerable__T (stack bool).
Proof.
  unfold stack, card. eauto.
Qed.

Local Definition BSRS := list (card bool).
Local Notation "x / y" := (x, y).
(* ** Enumerability *)

Fixpoint L_PCP n : list (BSRS * (string bool * string bool)) :=
  match n with
  | 0 => []
  | S n => L_PCP n
              ++ [ (C, (x, y)) | (C, x, y) ∈ (L_T BSRS n × L_T (string bool) n × L_T (string bool) n), (x/y) el C ]
              ++ [ (C, (x ++ u, y ++ v)) | ( (C, (u,v)), x, y) ∈ (L_PCP n × L_T (string bool) n × L_T (string bool) n), (x,y) el C ]
  end.

Lemma enum_PCP' :
  list_enumerator L_PCP (fun '(C, (u, v)) => @derivable bool C u v).
Proof.
  intros ( C & u & v ). split.
  + induction 1.
    * destruct (el_T C) as [m1], (el_T x) as [m2], (el_T y) as [m3].
      exists (1 + m1 + m2 + m3). cbn. in_app 2.
      in_collect (C, x, y); eapply cum_ge'; eauto; lia.
    * destruct IHderivable as [m1], (el_T x) as [m2], (el_T y) as [m3]. 
      exists (1 + m1 + m2 + m3). cbn. in_app 3.
      in_collect ( (C, (u, v), x, y)); eapply cum_ge'; eauto; try lia.
  + intros [m]. revert C u v H. induction m; intros.
    * inv H.
    * cbn in H. inv_collect; inv H; eauto using der_sing, der_cons.
Qed.

Lemma enumerable_derivable : enumerable (fun '(C, (u, v)) => @derivable bool C u v).
Proof.
  eapply list_enumerable_enumerable. eexists. eapply enum_PCP'.
Qed.

Lemma enumerable_PCP : enumerable dPCPb.
Proof.
  pose proof enumerable_derivable. 
  assert (enumerable (X := (stack bool * (string bool * string bool))) (fun '(C, (s, t)) => s = t)). {
    eapply dec_count_enum.
    - eapply decidable_iff. econstructor. intros (? & ? & ?). exact _.
    - eapply enum_enumT. econstructor. exact _.
  }
  unshelve epose proof (enumerable_conj _ _ _ _ H H0).
  - eapply discrete_iff. econstructor. exact _.
  - eapply projection in H1 as [f]. exists f.
    unfold enumerator in *.
    intros x. rewrite <- H1. intuition.
    + destruct H2 as [u]. exists (u,u). eauto.
    + destruct H2 as [[u v] [? ->]]. exists v. eauto.
Qed.
