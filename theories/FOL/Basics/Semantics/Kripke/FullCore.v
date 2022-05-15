(* * Kripke Semantics *)

Require Import Undecidability.FOL.Basics.Semantics.Tarski.FullFacts.
Require Export Undecidability.FOL.Basics.Semantics.Tarski.FullCore.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.

#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).

Section Kripke.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Section Model.

    Variable domain : Type.

    Class kmodel :=
      {
        nodes : Type ;

        reachable : nodes -> nodes -> Prop ;
        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

        k_interp : interp domain ;
        k_P : nodes -> forall P : preds, Vector.t domain (ar_preds P) -> Prop ;
        (* k_Bot : nodes -> Prop ; *)

        mon_P : forall u v, reachable u v -> forall P (t : Vector.t domain (ar_preds P)), k_P u t -> k_P v t;
      }.

    Variable M : kmodel.

    Fixpoint ksat {ff : falsity_flag} u (rho : nat -> domain) (phi : form) : Prop :=
      match phi with
      | atom P v => k_P u (Vector.map (@eval _ _ _ k_interp rho) v)
      | falsity => False
      | bin Impl phi psi => forall v, reachable u v -> ksat v rho phi -> ksat v rho psi
      | bin Conj phi psi => ksat u rho phi /\ ksat u rho psi
      | bin Disj phi psi => ksat u rho phi \/ ksat u rho psi
      | quant All phi => forall v (j : domain), reachable u v -> ksat v (j .: rho) phi
      | quant Ex phi => exists (j : domain), ksat u (j .: rho) phi
      end.

    Lemma ksat_mon {ff : falsity_flag} (u : nodes) (rho : nat -> domain) (phi : form) :
      forall v (H : reachable u v), ksat u rho phi -> ksat v rho phi.
    Proof.
      revert rho.
      induction phi; intros rho v' H; cbn; try destruct b0; try destruct q; intuition; eauto using mon_P, reach_tran.
      (* Ex *) + destruct H0 as [j Hj]. exists j. now apply IHphi.
    Qed.

    Lemma ksat_iff {ff : falsity_flag} u rho phi :
      ksat u rho phi <-> forall v (H : reachable u v), ksat v rho phi.
    Proof.
      split.
      - intros H1 v H2. eapply ksat_mon; eauto.
      - intros H. apply H. eapply reach_refl.
    Qed.
  End Model.

  Notation "rho  '⊩(' u ')'  phi" := (ksat _ u rho phi) (at level 20).
  Notation "rho '⊩(' u , M ')' phi" := (@ksat _ M _ u rho phi) (at level 20).
  Arguments ksat {_ _ _} _ _ _, _ _ _ _ _ _.

  Hint Resolve reach_refl : core.

  Section Substs.

    Variable D : Type.
    Context {M : kmodel D}.

    Lemma ksat_ext {ff : falsity_flag} u rho xi phi :
      (forall x, rho x = xi x) -> rho ⊩(u,M) phi <-> xi ⊩(u,M) phi.
    Proof.
      induction phi as [ | b P v | b [ | | ] | b [ | ] ] in rho, xi, u |-*; intros Hext; comp.
      - tauto.
      - erewrite Vector.map_ext. reflexivity. intros t. now apply eval_ext.
      - split; (intros [H1 H2]; split; [eapply IHphi1; [ | apply H1] | eapply IHphi2; [ | apply H2]]; congruence).
      - split; (intros [H1 | H2]; [left; eapply IHphi1; [ | apply H1] | right; eapply IHphi2; [ | apply H2]]; congruence).
      - split; intros H v Hv Hv'; now apply (IHphi2 v rho xi Hext), (H _ Hv), (IHphi1 v rho xi Hext).
      - split; intros H v d Hv; apply (IHphi v (d .: rho) (d .: xi)). all: ((intros []; cbn; congruence) + auto).
      - split; intros [j Hj]; exists j; (eapply IHphi; [ | eapply Hj]). all: ((intros []; cbn; congruence) + auto).
    Qed.

    Lemma ksat_comp {ff : falsity_flag} u rho xi phi :
      rho ⊩(u,M) phi[xi] <-> (xi >> eval rho (I := @k_interp _ M)) ⊩(u,M) phi.
    Proof.
      induction phi as [ | b P v | b [ | | ] | b [ | ] ] in rho, xi, u |-*; comp.
      - tauto.
      - erewrite Vector.map_map. erewrite Vector.map_ext. 2: apply eval_comp. reflexivity.
      - setoid_rewrite IHphi1. now setoid_rewrite IHphi2.
      - setoid_rewrite IHphi1. now setoid_rewrite IHphi2.
      - setoid_rewrite IHphi1. now setoid_rewrite IHphi2.
      - setoid_rewrite IHphi. split; intros H v d Hv; eapply ksat_ext. 2, 4: apply (H v d Hv).
        all: intros []; cbn; trivial; unfold funcomp; now erewrite eval_comp.
      - setoid_rewrite IHphi. split; intros [j Hj]; exists j; eapply ksat_ext. 2, 4: apply (Hj).
        all: intros []; cbn; trivial; unfold funcomp; now erewrite eval_comp.
    Qed.

  End Substs.


  Context {ff : falsity_flag}.

  Definition kvalid_ctx A phi :=
    forall D (M : kmodel D) u rho, (forall psi, psi el A -> ksat u rho psi) -> ksat u rho phi.

  Definition kvalid phi :=
    forall D (M : kmodel D) u rho, ksat u rho phi.

  Definition ksatis phi :=
    exists D (M : kmodel D) u rho, ksat u rho phi.


End Kripke.

Notation "rho  '⊩(' u ')'  phi" := (ksat u rho phi) (at level 20).
Notation "rho '⊩(' u , M ')' phi" := (@ksat _ _ _ M _ u rho phi) (at level 20).

Arguments ksat {_ _ _ _ _} _ _ _, {_ _ _} _ {_} _ _ _.
