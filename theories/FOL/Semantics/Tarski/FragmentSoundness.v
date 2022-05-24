(* * Tarski Semantics *)

Require Import Undecidability.FOL.Syntax.Facts.
Require Import Undecidability.FOL.Semantics.Tarski.FragmentFacts.
Require Import Undecidability.FOL.Deduction.FragmentND.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector Lia.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Set Default Proof Using "Type".

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
    intros H % soundness. firstorder.
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
    induction 1; intros D I rho HA; comp.
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


End Soundness.