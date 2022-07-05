(* * Kripke Semantics *)

From Undecidability Require Import FOL.Semantics.Kripke.FragmentCore FOL.Deduction.FragmentND.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.

#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).


(* ** Soundness **)

Section KSoundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Ltac clean_ksoundness :=
    match goal with
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ H : (?A -> ?B), H2 : (?A -> ?B) -> _ |- _] => specialize (H2 H)
    end.

  Lemma ksoundness A (phi : form) :
    A ⊢I phi -> kvalid_ctx A phi.
  Proof.
    intros Hprv D M. remember intu as s. induction Hprv; subst; cbn; intros u rho HA.
    all: repeat (clean_ksoundness + discriminate). all: (eauto || comp; eauto).
    - intros v Hr Hpi. eapply IHHprv. intros ? []; subst; eauto using ksat_mon.
    - eapply IHHprv1. 3: eapply IHHprv2. all: eauto. apply M.
    - intros d. apply IHHprv. intros psi [psi' [<- Hp]] % in_map_iff. cbn. rewrite ksat_comp. apply HA, Hp.
    - rewrite ksat_comp. eapply ksat_ext. 2: eapply (IHHprv u rho HA (eval rho t)). 
      unfold funcomp. now intros [].
    - now apply IHHprv in HA.
  Qed.

  Lemma ksoundness_bot {ff1 ff2 : falsity_flag} A  (psi : @form _ _ _ ff1) (phi : @form _ _ _ ff2) :
    closed psi ->
    (forall xi, kvalid (psi → xi)) ->
    A ⊢I phi -> kvalid_ctx (map (fun x => x [psi/⊥]) A) (phi[psi/⊥]).
  Proof.
    intros Hclosed Hexpl Hprv D M. remember intu as s. revert psi Hexpl Hclosed. induction Hprv; intros newbot Hexp Hclosed; subst; cbn; intros u rho HA.
    all: repeat (clean_ksoundness + discriminate). all: (eauto || comp; eauto).
    - intros v Hr Hpi. eapply IHHprv. 1-2:easy. intros ? []; subst; eauto using ksat_mon.
    - eapply IHHprv1. 1-2:easy. 3: eapply IHHprv2. all: eauto. apply M.
    - intros d. apply IHHprv. 1-2: now rewrite subst_closed. intros xi [psi' [<- [psi'' [<- Hpsi'']]%in_map_iff]] % in_map_iff.
      rewrite <- subst_falsity_comm. rewrite ksat_comp. apply HA, in_map, Hpsi''.
    - erewrite <- (subst_closed _ Hclosed). rewrite <- subst_falsity_comm.
      rewrite ksat_comp. eapply ksat_ext.
      2: {specialize (IHHprv newbot Hexp Hclosed).
          rewrite subst_closed in IHHprv. 2:easy.
          now eapply (IHHprv u rho HA (eval rho t)). } 
      unfold funcomp. now intros [].
    - apply (Hexp (phi[newbot/⊥]) D M u rho). 1: apply M. apply IHHprv. 1-2:easy. apply HA.
  Qed.

  Lemma ksoundness_bot_model {ff1 ff2 : falsity_flag} A  (psi : @form _ _ _ ff1) (phi : @form _ _ _ ff2) D (M : kmodel D):
    closed psi ->
    (ff2 = falsity_on -> forall u rho xi, rho ⊩(u,M) (psi → xi)) ->
    A ⊢I phi -> 
    forall u rho, 
    (forall psi', psi' el (map (fun x => x [psi/⊥]) A) -> rho ⊩(u,M) psi') -> 
    rho ⊩(u,M) (phi[psi/⊥]).
  Proof.
    intros Hclosed Hexpl Hprv. remember intu as s. revert psi Hexpl Hclosed. induction Hprv; intros newbot Hexp Hclosed; subst; cbn; intros u rho HA.
    all: repeat (clean_ksoundness + discriminate). all: (eauto || comp; eauto).
    - intros v Hr Hpi. eapply IHHprv. 1-2:easy. intros ? []; subst; eauto using ksat_mon.
    - eapply IHHprv1. 1-2:easy. 3: eapply IHHprv2. all: eauto. apply M.
    - intros d. apply IHHprv. 1-2: now rewrite subst_closed. intros xi [psi' [<- [psi'' [<- Hpsi'']]%in_map_iff]] % in_map_iff.
      rewrite <- subst_falsity_comm. rewrite ksat_comp. apply HA, in_map, Hpsi''.
    - erewrite <- (subst_closed _ Hclosed). rewrite <- subst_falsity_comm.
      rewrite ksat_comp. eapply ksat_ext.
      2: {specialize (IHHprv newbot Hexp Hclosed).
          rewrite subst_closed in IHHprv. 2:easy.
          now eapply (IHHprv u rho HA (eval rho t)). } 
      unfold funcomp. now intros [].
    - apply (Hexp u rho). 1: apply M. apply IHHprv. 1-2:easy. apply HA.
  Qed.

  Lemma ksoundness' (phi : form) :
    [] ⊢I phi -> kvalid phi.
  Proof.
    intros H % ksoundness. firstorder.
  Qed.

  Lemma ksoundness'_bot {ff1 ff2 : falsity_flag} (psi : @form _ _ _ ff1) (phi : @form _ _ _ ff2) :
    closed psi ->
    (forall xi, kvalid (psi → xi)) ->
    [] ⊢I phi -> kvalid (phi[psi/⊥]).
  Proof.
    intros Hcl Hexp H % (ksoundness_bot Hcl Hexp). intros D M u rho. now apply (H D M u rho).
  Qed.

End KSoundness.

