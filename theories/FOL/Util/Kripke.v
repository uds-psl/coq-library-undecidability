(** * Kripke Semantics *)

From Undecidability Require Export FOL.Util.Deduction.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

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
        k_Bot : nodes -> Prop ;

        mon_P : forall u v, reachable u v -> forall P (t : Vector.t domain (ar_preds P)), k_P u t -> k_P v t;
        mon_Bot : forall u v, reachable u v -> k_Bot u -> k_Bot v
      }.

    Variable M : kmodel.

    Fixpoint ksat {ff : falsity_flag} u (rho : nat -> domain) (phi : form) : Prop :=
      match phi with
      | atom P v => k_P u (Vector.map (@eval _ _ _ k_interp rho) v)
      | falsity => k_Bot u
      | bin Impl phi psi => forall v, reachable u v -> ksat v rho phi -> ksat v rho psi
      | quant All phi => forall j : domain, ksat u (j .: rho) phi
      end.

    (*Global Instance kmodel_reach_refl : Reflexive reachable := reach_refl.
    Global Instance kmodel_reach_trans : Transitive reachable := reach_tran.*)

    Lemma ksat_mon {ff : falsity_flag} (u : nodes) (rho : nat -> domain) (phi : form) :
      forall v (H : reachable u v), ksat u rho phi -> ksat v rho phi.
    Proof.
      revert rho.
      induction phi; intros rho v' H; cbn; try destruct b0; try destruct q; intuition; eauto using mon_P, mon_Bot, reach_tran.
    Qed.

    Lemma ksat_iff {ff : falsity_flag} u rho phi :
      ksat u rho phi <-> forall v (H : reachable u v), ksat v rho phi.
    Proof.
      split.
      - intros H1 v H2. eapply ksat_mon; eauto.
      - intros H. apply H. eapply reach_refl.
    Qed.
  End Model.

  Notation "rho  '⊨(' u ')'  phi" := (ksat _ u rho phi) (at level 20).
  Notation "rho '⊨(' u , M ')' phi" := (@ksat _ M _ u rho phi) (at level 20).
  Arguments ksat {_ _ _} _ _ _, _ _ _ _ _ _.

  Hint Resolve reach_refl.

  Section Substs.
    Variable D : Type.
    Context {M : kmodel D}.

    Lemma ksat_ext {ff : falsity_flag} u rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨(u,M) phi <-> xi ⊨(u,M) phi.
    Proof.
      induction phi in rho, xi, u |-*; intros Hext; comp.
      - tauto.
      - erewrite Vector.map_ext. reflexivity. intros t. now apply eval_ext.
      - destruct b0; split; intros H v Hv Hv'; now apply (IHphi2 v rho xi Hext), (H _ Hv), (IHphi1 v rho xi Hext).
      - destruct q; split; intros H d; apply (IHphi _ (d .: rho) (d .: xi)). all: ((intros []; cbn; congruence) + auto).
    Qed.

    Lemma ksat_comp {ff : falsity_flag} u rho xi phi :
      rho ⊨(u,M) (subst_form xi phi) <-> (xi >> eval rho (I := @k_interp _ M)) ⊨(u,M) phi.
    Proof.
      induction phi in rho, xi, u |-*; comp.
      - tauto.
      - erewrite Vector.map_map. erewrite Vector.map_ext. 2: apply eval_comp. reflexivity.
      - destruct b0. setoid_rewrite IHphi1. now setoid_rewrite IHphi2.
      - destruct q. setoid_rewrite IHphi. split; intros H d; eapply ksat_ext. 2, 4: apply (H d).
        all: intros []; cbn; trivial; unfold funcomp; now erewrite eval_comp.
    Qed.
  End Substs.

  Definition kconstraint := forall D, kmodel D -> Prop.
  Definition kcon_subs (C C' : kconstraint) := (forall D (M : kmodel D), C' D M -> C D M).

  Definition kstandard D (M : kmodel D) := forall v, k_Bot v -> False.
  (*Definition kexploding D (M : kmodel D) := forall v rho phi, rho ⊨(v) (falsity --> phi).
  Definition kexploding' D (M : kmodel D) := forall v rho P t, rho ⊨(v) (⊥ --> Pred P t). 
  Definition kbottomless D (M : kmodel D) := True.*)

  (*Lemma kstandard_explodes :
    kcon_subs kexploding kstandard.
  Proof.
    intros D M HC u rho P t v [] % HC. 
  Qed.*)

  Context {ff : falsity_flag}.

  Definition kvalid_L (C : kconstraint) A phi :=
    forall D (M : @kmodel D), C _ M -> forall u rho, (forall psi, psi el A -> ksat u rho psi) -> ksat u rho phi.

  (*Definition kvalid_T (C : kconstraint) T phi :=
    forall D (M : @kmodel D), C _ M -> forall u rho, (forall psi, psi ∈ T -> ksat u rho psi) -> ksat u rho phi.*)

  Lemma kvalid_L_subs C C' A phi :
    kcon_subs C' C -> kvalid_L C' A phi -> kvalid_L C A phi.
  Proof.
    intros Hsub HC' D M HC % Hsub u rho HA. now apply HC'.
  Qed.
End Kripke.

Notation "rho  '⊨(' u ')'  phi" := (ksat u rho phi) (at level 20).
Notation "rho '⊨(' u , M ')' phi" := (@ksat _ _ M u rho phi) (at level 20).
(*Notation "A ⊫KE phi" := (kvalid_L kexploding A phi) (at level 20).*)
Notation "A ⊫KS phi" := (kvalid_L kstandard A phi) (at level 20).
(*Notation "A ⊫KBL phi" := (kvalid_L kbottomless A phi) (at level 20).*)
Arguments ksat {_ _} _ _ _ _,  {_} _ _ _ _ _.

(** ** Soundness **)

Section KSoundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Ltac clean_ksoundness :=
    match goal with
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ H : (?A -> ?B), H2 : (?A -> ?B) -> _ |- _] => specialize (H2 H)
    end.

  Lemma ksemantic_explosion D (M : kmodel D) :
    kexploding' M -> kexploding M.
  Proof.
    intros H v rho phi.
    induction phi in rho, v |-*; firstorder.
  Qed.

  Lemma ksoundness A C (phi : form) :
    (b = expl -> kcon_subs kexploding C) -> @prv _ intu _ A phi  -> kvalid_L C A phi.
  Proof.
    intros Hexp Hprv D M HM. remember intu as s. induction Hprv; subst; cbn; intros u rho HA.
    all: repeat (clean_ksoundness + discriminate). all: (eauto || comp; eauto).
    - intros v Hr Hpi. capply IHHprv. intros ? []; subst; eauto using ksat_mon.
    - eapply IHHprv1. 3: eapply IHHprv2. all: eauto. reflexivity.
    - intros d. apply IHHprv. apply switch_map. intros psi Hpsi. rewrite ksat_comp. apply HA, Hpsi.
    - rewrite ksat_comp. eapply ksat_ext. 2: eapply (IHHprv u rho HA (eval rho t)). 
      asimpl. now intros [].
    - apply Hexp in HM. apply (HM u); eauto. apply M.
  Qed.

  Lemma strong_ksoundness T C phi :
    (b = expl -> kcon_subs kexploding C) -> @tprv _ intu _ T phi  -> kvalid_T C T phi.
  Proof.
    intros Hexp (A & HA1 & HA2) D M HM u rho HT. apply (ksoundness Hexp HA2 HM).
    firstorder.
  Qed.

End KSoundness.

Lemma ksoundness' {Sigma : Signature} A phi :
  A ⊢IE phi -> A ⊫KS phi.
Proof.
  apply ksoundness. intros _. firstorder.
Qed.



(** ** Connection to Tarski Semantics *)

Program Instance interp_kripke {domain eta} (I : interp domain eta) : kmodel  eta :=
  {| nodes := unit ; reachable u v := True |}.
Next Obligation.
  all: try abstract tauto.
  intros. apply emb_refl.
Defined.

Lemma kripke_tarski domain eta (b : logic) (I : interp domain eta) rho phi :
  rho ⊨ phi <-> rho ⊩(tt, interp_kripke I, _) phi.
Proof.
  revert rho. induction phi; intros rho.
  - tauto.
  - tauto.
  - tauto.
  - split; intros H. cbn in *.
    + intros [] [] H'. apply IHphi2, H,  IHphi1, H'.
    + intros H'. apply IHphi2, (H tt Logic.I), IHphi1, H'.
  - split; intros H; cbn in *.
    + intros [] [] i. apply IHphi, H.
    + intros i. apply IHphi, (H tt Logic.I).
Qed.

Definition kvalid b (phi : form b) :=
  forall domain eta (M : @kmodel domain eta) u rho, rho ⊩(u,M,eta) phi.

Definition ksatis b (phi : form b) :=
  exists domain eta (M : @kmodel domain eta) u rho, ksat eta M u rho phi.

Lemma kvalid_valid b (phi : form b) :
  kvalid phi -> valid phi.
Proof.
  intros H domain I eta rho. eapply kripke_tarski, H.
Qed.

Lemma ksatis_satis b (phi : form b) :
  satis phi -> ksatis phi.
Proof.
  intros (domain & eta & I & rho & ?). eapply kripke_tarski in H.
  now exists domain, eta, (interp_kripke I), tt,  rho.
Qed.



