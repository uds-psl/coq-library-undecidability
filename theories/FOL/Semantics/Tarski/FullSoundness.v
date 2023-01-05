(** ** Tarski Soundness *)

Require Import Undecidability.FOL.Syntax.Facts.
Require Import Undecidability.FOL.Semantics.Tarski.FullFacts.
Require Import Undecidability.FOL.Deduction.FullND.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Import ListNotations.
Require Import Vector Lia.

Local Set Implicit Arguments.
Local Unset Strict Implicit.


#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).

(* ** Soundness *)

Section Soundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma soundness {ff : falsity_flag} A phi :
    A ⊢I phi -> valid_ctx A phi.
  Proof.
    remember intu as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    - exists (eval rho t). cbn. specialize (IHprv Heqp D I rho HA).
      apply sat_comp in IHprv. eapply sat_ext; try apply IHprv. now intros [].
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el List.map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Heqp D I (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - firstorder.
    - firstorder. now apply H0.
    - firstorder. now apply H0.
    - firstorder.
    - firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - discriminate.
  Qed.

  Lemma soundness' {ff : falsity_flag} phi :
    [] ⊢I phi -> valid phi.
  Proof.
    intros H % soundness. intros D I rho; now apply H. 
  Qed.

  Corollary tsoundness {ff : falsity_flag} T phi :
    T ⊢TI phi -> forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi.
  Proof.
    intros (A & H1 & H2) D I rho HI. apply (soundness H2).
    intros psi HP. apply HI, H1, HP.
  Qed.

  Lemma sound_for_classical_model {p:peirce} {ff : falsity_flag} A phi (D : Type) (I : interp D) (rho : env D) : 
    (forall rho phi, (rho ⊨ phi) \/ ~(rho ⊨ phi)) -> A ⊢ phi -> rho ⊫ A -> rho ⊨ phi.
  Proof.
    intros LEM HD. revert LEM rho. induction HD; cbn; intros LEM rho HA.
    - intros Hphi. apply IHHD; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHHD1, IHHD2.
    - intros d. apply IHHD; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHHD LEM rho HA (eval rho t)). now intros [].
    - exists (eval rho t). cbn. specialize (IHHD LEM rho HA).
      apply sat_comp in IHHD. eapply sat_ext; try apply IHHD. now intros [].
    - edestruct IHHD1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el List.map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHHD2 LEM (d.:rho) H'). apply sat_comp in IHHD2. apply IHHD2.
    - apply (IHHD LEM) in HA. firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
    - edestruct IHHD1; eauto.
      + apply IHHD2; trivial. intros xi [<-|HX]; auto.
      + apply IHHD3; trivial. intros xi [<-|HX]; auto.
    - intros H. 
      destruct (LEM rho phi) as [Ht|Hf]. 1:easy.
      destruct (LEM rho psi) as [Ht2|Hf2]; tauto.
  Qed.
 
  Hypothesis LEM : forall P, P \/ ~ P.

  Lemma Peirce (P Q : Prop) :
    ((P -> Q) -> P) -> P.
  Proof using LEM.
    destruct (LEM (((P -> Q) -> P) -> P)); tauto.
  Qed.

  Lemma soundness_class {ff : falsity_flag} A phi :
    A ⊢C phi -> valid_ctx A phi.
  Proof using LEM.
    remember class as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    - exists (eval rho t). cbn. specialize (IHprv Heqp D I rho HA).
      apply sat_comp in IHprv. eapply sat_ext; try apply IHprv. now intros [].
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el List.map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Heqp D I (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - clear LEM. firstorder.
    - firstorder. now apply H0.
    - firstorder. now apply H0.
    - clear LEM. firstorder.
    - clear LEM. firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - apply Peirce.
  Qed.

  Lemma soundness_class' {ff : falsity_flag} phi :
    [] ⊢C phi -> valid phi.
  Proof using LEM.
    intros H % soundness_class. clear LEM. intros D I rho; now apply H.
  Qed.

  Corollary tsoundness_class {ff : falsity_flag} T phi :
    T ⊢TC phi -> forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi.
  Proof using LEM.
    intros (A & H1 & H2) D I rho HI. apply (soundness_class H2).
    intros psi HP. apply HI, H1, HP.
  Qed.

End Soundness.


