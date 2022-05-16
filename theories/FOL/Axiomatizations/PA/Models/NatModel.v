From Undecidability.FOL Require Import Syntax.Facts Semantics.Tarski.FullFacts Deduction.FullFacts.
Require Import Undecidability.FOL.Axiomatizations.PA.FA.
Require Import Undecidability.FOL.Axiomatizations.PA.Signature.
Require Import Undecidability.FOL.Axiomatizations.PA.Problems.
Require Import Lia List Vector.
Import Vector.VectorNotations.

Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.


(** ** The standard model *)

Section StdModel.

  Definition interp_nat : interp nat.
  Proof.
    split.
    - destruct f; intros v.
      + exact 0.
      + exact (S (Vector.hd v) ).
      + exact (Vector.hd v + Vector.hd (Vector.tl v) ).
      + exact (Vector.hd v * Vector.hd (Vector.tl v) ).
    - destruct P. intros v.
      exact (Vector.hd v = Vector.hd (Vector.tl v) ).
  Defined.


  Fact nat_extensional : extensional interp_nat.
  Proof.
    now intros x y. 
  Qed.


  Lemma nat_is_FA_model : forall rho phi,  List.In phi FAeq -> sat interp_nat rho phi.
  Proof.
    intros rho phi. intros H.
    repeat (destruct H as [<- | H]; auto).
    all: cbn; try congruence. inversion H.
  Qed.

  Lemma nat_is_Q_model : forall rho phi,  List.In phi Qeq -> sat interp_nat rho phi.
  Proof.
    intros rho phi. intros H.
    repeat (destruct H as [<- | H]; auto).
    all: cbn; try congruence.
    2: inversion H.
    induction d. now left.
    right. destruct IHd.
    exists 0. congruence.
    exists d. reflexivity.
  Qed.

  Fact nat_eval_num (sigma : env nat) n : @eval _ _ _ interp_nat sigma (μ n) = n.
  Proof.
    induction n.
    - reflexivity.
    - cbn. now rewrite IHn.
  Qed.


  Fact nat_induction phi : forall rho, sat interp_nat rho (ax_induction phi).
  Proof.
    intros rho H0 IH d. induction d; cbn in *.
    rewrite <-sat_single in H0. apply H0.
    apply IH in IHd. rewrite sat_comp in IHd.
    revert IHd. apply sat_ext. intros []; reflexivity.
  Qed.
    

  Fact nat_is_PAeq_model : forall ax rho, PAeq ax -> sat interp_nat rho ax.
  Proof.
    intros rho psi [].
    now apply nat_is_FA_model.
    all: cbn; try congruence.
    apply nat_induction.
 Qed.


  Fact nat_is_PA_model : forall ax rho, PA ax -> sat interp_nat rho ax.
  Proof.
    intros rho psi [].
    repeat (destruct H as [<- | H]; auto).
    all: cbn; try congruence. inversion H.
    apply nat_induction.
  Qed.


End StdModel.
