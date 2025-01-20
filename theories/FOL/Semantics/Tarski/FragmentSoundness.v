Require Import Undecidability.FOL.Syntax.Facts.
Require Import Undecidability.FOL.Semantics.Tarski.FragmentFacts.
Require Import Undecidability.FOL.Deduction.FragmentND.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
From Stdlib Require Import Vector Lia.

Local Set Implicit Arguments.
Local Unset Strict Implicit.


#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).

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
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - discriminate.
  Qed.

  Lemma soundness' {ff : falsity_flag} phi :
    [] ⊢I phi -> valid phi.
  Proof.
    intros H % soundness. intros D I rho. now apply H.
  Qed.

  Lemma intuitionistic_is_classical {ff:falsity_flag} A phi :
    A ⊢I phi -> A ⊢C phi.
  Proof.
  induction 1; comp.
  - now apply II, IHprv.
  - now eapply IE, IHprv2.
  - now eapply AllI, IHprv.
  - now eapply AllE, IHprv.
  - now eapply Exp, IHprv.
  - now eapply Ctx, H.
  - apply Pc.
  Qed.

  Lemma classical_soundness (LEM:forall P:Prop, P \/ ~P) {ff : falsity_flag} A phi :
    A ⊢C phi -> valid_ctx A phi.
  Proof.
    induction 1; intros D I rho HA; cbn.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv D I rho HA (eval rho t)). now intros [].
    - apply (IHprv) in HA. firstorder.
    - firstorder.
    - intros H. 
      destruct (LEM (rho ⊨ phi)) as [Ht|Hf]. 1:easy.
      destruct (LEM (rho ⊨ psi)) as [Ht2|Hf2]; tauto.
  Qed.

  Lemma sound_for_classical_model {p:peirce} {ff : falsity_flag} A phi (D : Type) (I : interp D) (rho : env D) : 
    classical I -> A ⊢ phi -> rho ⊫ A -> rho ⊨ phi.
  Proof.
    intros LEM HD. revert LEM rho. induction HD; cbn; intros LEM rho HA.
    - intros Hphi. apply IHHD. 1:easy. intros a [<-|Ha]; try easy. now apply HA.
    - now apply IHHD1, IHHD2.
    - intros d. apply IHHD; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHHD LEM rho HA (eval rho t)). now intros [].
    - apply (IHHD) in HA; cbn in *; eauto. exfalso;easy.
    - apply HA, H.
    - intros H. unfold classical in LEM. cbn in LEM. eapply LEM. exact H.
  Qed.



End Soundness.
