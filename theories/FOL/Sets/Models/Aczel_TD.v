(* * Consistency of ZF-Axiomatisation *)

From Undecidability.FOL.Sets.Models Require Import Aczel.
Require Import Setoid Morphisms.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Set Default Proof Using "Type".


(* ** Quotient Model *)

Class extensional_normaliser :=
  {
    tdelta : (Acz -> Prop) -> Acz;
    TDesc1 : forall P, (exists s, forall t, P t <-> Aeq t s) -> P (tdelta P);
    TDesc2 : forall P P', (forall s, P s <-> P' s) -> tdelta P = tdelta P';
    PI : forall s (H H' : tdelta (Aeq s) = s), H = H';
  }.

Section QM.

  Context { Delta : extensional_normaliser }.

  (* Auxiliary lemmas *)

  Definition N s :=
    tdelta (Aeq s).

  Fact CR1 :
    forall s, Aeq s (N s).
  Proof.
    intros s. pattern (N s). apply TDesc1. now exists s.
  Qed.

  Lemma CR2 :
    forall s t, Aeq s t -> N s = N t.
  Proof.
    intros s t H. apply TDesc2.
    intros u. rewrite H. tauto.
  Qed.

  Lemma N_idem s :
    N (N s) = N s.
  Proof.
    apply CR2. symmetry. apply CR1.
  Qed.

  Lemma N_eq_Aeq s t :
    N s = N t -> Aeq s t.
  Proof.
    intros H. rewrite (CR1 s), (CR1 t). now rewrite H.
  Qed.

  Global Instance N_proper :
    Proper (Aeq ==> Aeq) N.
  Proof.
    intros s t H. now rewrite <- (CR1 s), <- (CR1 t).
  Qed.

  Definition SET :=
    sig (fun s => N s = s).

  Definition NS s : SET :=
    exist (fun s => N s = s) (N s) (N_idem s).

  Definition IN (X Y : SET) :=
    Ain (proj1_sig X) (proj1_sig Y).

  Definition Subq (X Y : SET) :=
    forall Z, IN Z X -> IN Z Y.

  (* Helpful lemmas for automation *)

  Lemma Aeq_p1_NS s :
    Aeq s (proj1_sig (NS s)).
  Proof.
    exact (CR1 s).
  Qed.

  Lemma NS_eq_Aeq_p1 s X :
    NS s = X -> Aeq s (proj1_sig X).
  Proof.
    intros <-. apply Aeq_p1_NS.
  Qed.

  Lemma Ain_IN_p1 X Y :
    Ain (proj1_sig X) (proj1_sig Y) -> IN X Y.
  Proof.
    intros H1. unfold IN. exact H1.
  Qed.

  Lemma Ain_IN_NS s t :
    Ain s t -> IN (NS s) (NS t).
  Proof.
    intros H1. unfold IN. now repeat rewrite <- Aeq_p1_NS.
  Qed.

  Lemma Ain_IN_p1_NS X s :
    Ain (proj1_sig X) s -> IN X (NS s).
  Proof.
    intros H1. unfold IN. now rewrite <- Aeq_p1_NS.
  Qed.

  Lemma Ain_IN_NS_p1 s X :
    Ain s (proj1_sig X) -> IN (NS s) X.
  Proof.
    intros H1. unfold IN. now rewrite <- Aeq_p1_NS.
  Qed.

  Lemma IN_Ain_p1 X Y :
    IN X Y -> Ain (proj1_sig X) (proj1_sig Y).
  Proof.
    tauto.
  Qed.

  Lemma IN_Ain_NS s t :
    IN (NS s) (NS t) -> Ain s t.
  Proof.
    unfold IN. now repeat rewrite <- Aeq_p1_NS.
  Qed.

  Lemma IN_Ain_p1_NS X s :
    IN X (NS s) -> Ain (proj1_sig X) s.
  Proof.
    unfold IN. now rewrite <- Aeq_p1_NS.
  Qed.

  Lemma IN_Ain_NS_p1 s X :
    IN (NS s) X -> Ain s (proj1_sig X).
  Proof.
    unfold IN. now rewrite <- Aeq_p1_NS.
  Qed.

  Hint Resolve Ain_IN_p1 Ain_IN_NS Ain_IN_p1_NS Ain_IN_NS_p1 IN_Ain_p1 IN_Ain_NS IN_Ain_p1_NS IN_Ain_NS_p1 : core.

  Lemma ASubq_Subq_p1 X Y :
    ASubq (proj1_sig Y) (proj1_sig X) <-> Subq Y X.
  Proof.
    split; intros H Z H1.
    - apply Ain_IN_p1, H. auto.
    - apply IN_Ain_NS_p1, H. auto.
  Qed.

  Lemma PI_eq s t (H1 : N s = s) (H2 : N t = t) :
    s = t -> exist (fun s => N s = s) s H1 = exist (fun s => N s = s) t H2.
  Proof.
    intros XY. subst t. f_equal. apply PI.
  Qed.

  Lemma NS_p1_eq X :
    NS (proj1_sig X) = X.
  Proof.
    destruct X. simpl. now apply PI_eq.
  Qed.

  Lemma Aeq_p1_NS_eq X s :
    Aeq (proj1_sig X) s -> X = NS s.
  Proof.
    destruct X as [t H1]. simpl. intros H2. unfold NS.
    apply PI_eq. rewrite <- H1. now apply CR2.
  Qed.

  Lemma Aeq_p1_eq (X Y : SET) :
    Aeq (proj1_sig X) (proj1_sig Y) -> X = Y.
  Proof.
    intros H. rewrite <- (NS_p1_eq Y). now apply Aeq_p1_NS_eq.
  Qed.

  Lemma Aeq_NS_eq s t :
    Aeq s t -> NS s = NS t.
  Proof.
    intros H % CR2.
    now apply PI_eq.
  Qed.



  (* ** Extensional Axioms *)

  (* Lifted set operations *)

  Definition Sempty :=
    NS AEmpty.

  Definition Supair (X Y : SET) :=
    NS (Aupair (proj1_sig X) (proj1_sig Y)).

  Definition Sunion (X : SET) :=
    NS (Aunion (proj1_sig X)).

  Definition Spower (X : SET) :=
    NS (Apower (proj1_sig X)).

  Definition empred (P : SET -> Prop) :=
    fun s => P (NS s).

  Definition Ssep (P : SET -> Prop) (X : SET) :=
    NS (Asep (empred P) (proj1_sig X)).

  Definition emfun (F : SET -> SET) :=
    fun s => proj1_sig (F (NS s)).

  Definition Srepl (F : SET -> SET) (X : SET) :=
    NS (Arepl (emfun F) (proj1_sig X)).

  Definition Som :=
    NS Aom.

  (* Extensionality *)

  Lemma set_ext X Y : 
    Subq X Y /\ Subq Y X <-> X = Y.
  Proof.
    split; intros H; try now rewrite H. destruct H as [H1 H2].
    apply Aeq_p1_eq, Aeq_ext; now apply ASubq_Subq_p1.
  Qed.

  (* Empty *)

  Lemma emptyE X :
    ~ IN X Sempty.
  Proof.
    intros H % IN_Ain_p1_NS. now apply AEmptyAx in H.
  Qed.

  (* Unordered Pairs *)

  Lemma upairAx X Y Z :
    IN Z (Supair X Y) <-> Z = X \/ Z = Y.
  Proof.
    split; intros H.
    - apply IN_Ain_p1_NS, AupairAx in H as [H|H].
      + left. now apply Aeq_p1_eq.
      + right. now apply Aeq_p1_eq.
    - apply Ain_IN_p1_NS, AupairAx.
      destruct H as [-> | ->]; auto.
  Qed.

  (* Union *)

  Lemma unionAx X Z :
    IN Z (Sunion X) <-> exists Y, IN Y X /\ IN Z Y.
  Proof.
    split; intros H.
    - apply IN_Ain_p1_NS, AunionAx in H as [y[Y1 Y2]].
      exists (NS y). split; auto.
    - destruct H as [Y[Y1 Y2]].
      apply Ain_IN_p1_NS, AunionAx.
      exists (proj1_sig Y). split; auto.
  Qed.

  (* Power *)

  Lemma powerAx X Y :
    IN Y (Spower X) <-> Subq Y X.
  Proof.
    split; intros H.
    - apply IN_Ain_p1_NS, ApowerAx in H.
      now apply ASubq_Subq_p1.
    - apply Ain_IN_p1_NS, ApowerAx.
      now apply ASubq_Subq_p1.
  Qed.

  (* Separation *)

  Fact empred_Aeq P :
    cres Aeq (empred P).
  Proof.
    intros s s' H % Aeq_NS_eq. unfold empred. now rewrite H.
  Qed.

  Lemma sepAx P X Y :
    IN Y (Ssep P X) <-> IN Y X /\ P Y.
  Proof with try apply empred_Aeq.
    split; intros H.
    - apply IN_Ain_p1_NS, AsepAx in H as [H1 H2]...
      split; auto. unfold empred in H2.
      now rewrite NS_p1_eq in H2.
    - destruct H as [H1 H2]. apply Ain_IN_p1_NS, AsepAx...
      split; trivial. unfold empred. now rewrite NS_p1_eq.
  Qed.

  (* Functional Replacement *)

  Fact emfun_Aeq F :
    fres Aeq (emfun F).
  Proof.
    intros s s' H % Aeq_NS_eq.
    unfold emfun. now rewrite H.
  Qed.

  Lemma replAx F X Y :
    IN Y (Srepl F X) <-> exists Z, IN Z X /\ Y = F Z.
  Proof with try apply emfun_Aeq.
    split; intros H.
    - apply IN_Ain_p1_NS, AreplAx in H as [z[Z1 Z2]]...
      exists (NS z). split; auto. now apply Aeq_p1_eq.
    - destruct H as [Z[Z1 Z2]].
      apply Ain_IN_p1_NS, AreplAx...
      exists (proj1_sig Z). split; auto.
      rewrite Z2. unfold emfun.
      now rewrite NS_p1_eq.
  Qed.

  (* Description Operator *)

  Definition desc (P : SET -> Prop) :=
    NS (tdelta (fun s => empred P s)).

  Lemma descAx (P : SET -> Prop) X :
    P X -> unique P X -> P (desc P).
  Proof.
    intros H1 H2. 
    enough (empred P (tdelta (empred P))) by assumption.
    apply TDesc1. exists (proj1_sig X).
    intros t. split; intros H.
    - apply NS_eq_Aeq_p1. symmetry. now apply H2.
    - symmetry in H. apply (empred_Aeq H).
      hnf. now rewrite NS_p1_eq.
  Qed.

  Lemma descAx2 (P P' : SET -> Prop) :
    (forall x, P x <-> P' x) -> desc P = desc P'.
  Proof.
    intros H. apply Aeq_NS_eq, Aeq_ref', TDesc2.
    intros s. apply H.
  Qed.

  (* Relational Replacement *)
  
  Definition Srep (R : SET -> SET -> Prop) X :=
    Srepl (fun x => desc (R x)) (Ssep (fun x => exists y, R x y) X).

  Definition functional X (R : X -> X -> Prop) :=
    forall x y y', R x y -> R x y' -> y = y'.

  Lemma repAx R X Y :
    functional R -> IN Y (Srep R X) <-> exists Z, IN Z X /\ R Z Y.
  Proof.
    intros H. unfold Srep. rewrite replAx.
    split; intros [Z[H1 H2]]; exists Z; split.
    - now apply sepAx in H1.
    - apply sepAx in H1 as [_ [Y' H']].
      subst. eapply descAx; firstorder eauto.
    - apply sepAx; split; trivial. now exists Y.
    - eapply H; eauto. eapply descAx; firstorder eauto.
  Qed.

  (* Infinity *)

  Definition Ssucc X :=
    Sunion (Supair X (Supair X X)).

  Definition Sinductive X :=
    IN Sempty X /\ forall Y, IN Y X -> IN (Ssucc Y) X.

  Lemma Ainductive_Sinductive X :
    Ainductive (proj1_sig X) <-> Sinductive X.
  Proof.
    split; intros [H1 H2]; split.
    - now apply Ain_IN_NS_p1.
    - intros Y H % IN_Ain_p1. apply H2 in H.
      unfold IN. cbn. now rewrite <- !CR1.
    - now apply IN_Ain_NS_p1.
    - intros s H % Ain_IN_NS_p1. specialize (H2 (NS s) H).
      unfold IN in H2. cbn in H2. now rewrite <- !CR1 in H2.
  Qed.

  Lemma omAx1 :
    Sinductive Som.
  Proof.
    split.
    - apply Ain_IN_NS. apply AomAx1.
    - intros X H. unfold IN in *; cbn in *.
      rewrite <- !CR1 in *. now apply AomAx1.
  Qed.

  Lemma omAx2 :
    forall X, Sinductive X -> Subq Som X.
  Proof.
    intros X H. apply ASubq_Subq_p1. cbn.
    rewrite <- CR1. apply AomAx2.
    now apply Ainductive_Sinductive.
  Qed.

End QM.
