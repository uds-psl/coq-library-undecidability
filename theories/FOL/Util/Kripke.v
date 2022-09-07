(* * Kripke Semantics *)

From Undecidability Require Import FOL.Util.Deduction FOL.Util.Tarski FOL.Util.Syntax.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationHints.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.

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

  Lemma ksoundness' (phi : form) :
    [] ⊢I phi -> kvalid phi.
  Proof.
    intros H % ksoundness. firstorder.
  Qed.

End KSoundness.



(* ** Connection to Tarski Semantics *)

Section ToTarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Program Instance interp_kripke {domain} (I : interp domain) : kmodel domain :=
    {| nodes := unit ; reachable u v := True |}.
  Next Obligation.
    - now apply I in X.
  Defined.

  Lemma kripke_tarski {ff : falsity_flag} domain (I : interp domain) rho phi :
    rho ⊨ phi <-> ksat (interp_kripke I) tt rho phi.
  Proof.
    revert rho. induction phi; intros rho.
    - tauto.
    - tauto.
    - destruct b0. cbn. rewrite IHphi1, IHphi2. intuition. destruct v. tauto.
    - destruct q. cbn. split; intros H; cbn in *.
      + intros i. apply IHphi, H.
      + intros i. apply IHphi, H.
  Qed.

  Lemma kvalid_valid b (phi : form b) :
    kvalid phi -> valid phi.
  Proof.
    intros H domain I rho. apply kripke_tarski, H.
  Qed.

  Lemma ksatis_satis b (phi : form b) :
    satis phi -> ksatis phi.
  Proof.
    intros (domain & I & rho & ?). eapply kripke_tarski in H.
    now exists domain, (interp_kripke I), tt, rho.
  Qed.

End ToTarski.
