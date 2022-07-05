(* * Kripke Semantics *)

Require Import Undecidability.FOL.Semantics.Tarski.FragmentFacts.
Require Export Undecidability.FOL.Semantics.Tarski.FragmentCore.
Require Export Undecidability.FOL.Syntax.Facts.
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
      | quant All phi => forall j : domain, ksat u (j .: rho) phi
      end.

    Lemma ksat_mon {ff : falsity_flag} (u : nodes) (rho : nat -> domain) (phi : form) :
      forall v (H : reachable u v), ksat u rho phi -> ksat v rho phi.
    Proof.
      revert rho.
      induction phi; intros rho v' H; cbn; try destruct b0; try destruct q; intuition; eauto using mon_P, reach_tran.
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
      induction phi as [ | b P v | | ] in rho, xi, u |-*; intros Hext; comp.
      - tauto.
      - erewrite Vector.map_ext. reflexivity. intros t. now apply eval_ext.
      - destruct b0; split; intros H v Hv Hv'; now apply (IHphi2 v rho xi Hext), (H _ Hv), (IHphi1 v rho xi Hext).
      - destruct q; split; intros H d; apply (IHphi _ (d .: rho) (d .: xi)). all: ((intros []; cbn; congruence) + auto).
    Qed.

    Lemma ksat_comp {ff : falsity_flag} u rho xi phi :
      rho ⊩(u,M) phi[xi] <-> (xi >> eval rho (I := @k_interp _ M)) ⊩(u,M) phi.
    Proof.
      induction phi as [ | b P v | | ] in rho, xi, u |-*; comp.
      - tauto.
      - erewrite Vector.map_map. erewrite Vector.map_ext. 2: apply eval_comp. reflexivity.
      - destruct b0. setoid_rewrite IHphi1. now setoid_rewrite IHphi2.
      - destruct q. setoid_rewrite IHphi. split; intros H d; eapply ksat_ext. 2, 4: apply (H d).
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


Section Bottom.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {domain : Type}.
  Context {M : kmodel domain}.
  Program Definition kmodel_bot 
    (F_P : @nodes _ _ _ M -> Prop)
    (mon_F : forall u v, reachable u v -> F_P u -> F_P v)
     : @kmodel Σ_funcs (@Σ_preds_bot Σ_preds) domain := {|
    nodes := @nodes _ _ _ M ;
    reachable := @reachable _ _ _ M ;
    k_interp := interp_bot False (@k_interp _ _ _ M) ;
    k_P := fun n P => match P with inl _ => fun _ => F_P n | inr P' => @k_P _ _ _ M n P' end
  |}.
  Next Obligation. apply reach_refl. Qed.
  Next Obligation. now apply reach_tran with v. Qed.
  Next Obligation. destruct P as [|P'].
    + now apply mon_F with u.
    + now apply mon_P with u.
  Qed.

  Definition ksat_bot 
    {ff : falsity_flag} (F_P : @nodes _ _ _ M -> Prop)
    (mon_F : forall u v, reachable u v -> F_P u -> F_P v)
    u (rho : env domain) (phi : form) : Prop 
    := @ksat _ Σ_preds_bot domain (kmodel_bot mon_F) falsity_off u rho (falsity_to_pred phi).

  Lemma sat_bot_False {ff:falsity_flag} u rho phi
    (e : forall u v, reachable u v -> False -> False)
    : @ksat_bot ff (fun _ => False) e u rho phi <-> @ksat _ _ domain M ff u rho phi.
  Proof.
    induction phi in rho,u|-*.
    - easy.
    - easy.
    - destruct b0. unfold sat_bot, falsity_to_pred in *. cbn.
      split; intros H v Hreach H1 %IHphi1; apply IHphi2; now apply H, H1.
    - destruct q. unfold sat_bot, falsity_to_pred in *. cbn.
      split; intros H d; apply IHphi, H.
  Qed.

End Bottom.



