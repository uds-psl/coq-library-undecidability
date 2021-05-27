Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
Require Import Undecidability.SystemF.Util.typing_facts Undecidability.SystemF.Util.term_facts.

Inductive step : term -> term -> Prop :=
| step_beta s P Q :
    step (app (abs s P) Q) (subst_term poly_var (scons Q var) P)
| step_ty_beta P s :
    step (ty_app (ty_abs P) s) (subst_term (scons s poly_var) var P)
| step_appL P P' Q :
    step P P' -> step (app P Q) (app P' Q)
| step_appR P P' Q :
    step P P' -> step (app Q P) (app Q P')
| step_ty_app P P' s :
    step P P' -> step (ty_app P s) (ty_app P' s)
| step_lam s P P' :
    step P P' -> step (abs s P) (abs s P')
| step_ty_lam P P' :
    step P P' -> step (ty_abs P) (ty_abs P').

Inductive sn x : Prop :=
| SNI : (forall y, step x y -> sn y) -> sn x.

Local Hint Constructors step normal_form head_form : core.

Require Import Coq.Relations.Relation_Operators.

Ltac inv_step :=
  match goal with
    [ H : step ?P ?Q |- _] => inversion H; subst; clear H; try now firstorder
  end.

Lemma progress P :
  (forall Q, ~ step P Q) \/ exists Q, step P Q.
Proof.
  induction P.
  - firstorder inv_step.
  - destruct IHP1 as [H1 | [Q1 H1]]; eauto.
    destruct IHP2 as [H2 | [Q2 H2]]; eauto.
    destruct P1. 3:eauto.
    all: firstorder inv_step.
  - destruct IHP as [H1 | [Q1 H1]]; eauto. firstorder inv_step.
  - destruct IHP as [H1 | [Q1 H1]]; eauto.
    destruct P. 5:eauto. 
    all: firstorder inv_step.
  - destruct IHP as [H1 | [Q1 H1]]; eauto. firstorder inv_step.
Qed.

Lemma preservation P Q Γ s :
  typing Γ P s -> step P Q -> typing Γ Q s.
Proof.
  induction 1 in Q |- *.
  - inversion 1.
  - inversion 1; subst.
    + inversion H; subst.
      eapply typing_subst_term. eassumption.
      intros [] ? [=]; subst; cbn;
      eauto using typing.
    + eauto using typing.
    + eauto using typing.
  - inversion 1; subst. eauto using typing.
  - inversion 1; subst.
    + inversion H; subst.
      evar (Gamma' : environment).
      replace Gamma with Gamma'. all: subst Gamma'.
      eapply typing_subst_poly_type. eassumption.
      erewrite List.map_map, List.map_ext, List.map_id.
      reflexivity. intros. now asimpl.
    + eauto using typing.
  - inversion 1; subst. eauto using typing.
Qed.

Lemma preservation_star P Q Γ s :
  typing Γ P s -> Relation_Operators.clos_refl_trans term step P Q -> typing Γ Q s.
Proof.
  intros H. induction 1; eauto using preservation.
Qed.

Lemma step_ext_2 P Q1 Q2 :
  step P Q1 -> Q1 = Q2 -> step P Q2.
Proof.
  now intros ? ->.
Qed.

Ltac now_asimpl := asimpl; ( (reflexivity || eapply ext_term; now intros []; repeat asimpl) ||
                   f_equal; (reflexivity || eapply ext_term; now intros []; repeat asimpl)).

Lemma step_subst P Q σ τ :
  step P Q -> step (subst_term σ τ P) (subst_term σ τ Q).
Proof.
  induction 1 in σ, τ |- *; cbn; asimpl; eauto using step.
  - eapply step_ext_2. 
    econstructor. now_asimpl.
  - eapply step_ext_2.
    econstructor. now_asimpl.
Qed.

(* Require Import Equations.Prop.DepElim. *)
Require Import Coq.Program.Equality.

Ltac inv H := inversion H; subst; clear H.

Lemma step_subst_inv P Q σ τ :
  step (subst_term σ (τ >> var) P) Q -> exists P', step P P' /\ subst_term σ (τ >> var) P' = Q.
Proof with eexists; split; [eauto | now_asimpl].
  intros H. dependent induction H; rename x into Eqn.
  - destruct P; inv Eqn. destruct P1; inv H0...
  - destruct P; inv Eqn. destruct P; inv H0... 
  - destruct P; inv Eqn. destruct (IHstep _ _ _ eq_refl) as (P1' & H1 & <-)...
  - destruct P; inv Eqn. destruct (IHstep _ _ _ eq_refl) as (P1' & H1 & <-)...
  - destruct P; inv Eqn. destruct (IHstep _ _ _ eq_refl) as (P1' & H1 & <-)...
  - destruct P; inv Eqn.
    edestruct (IHstep P (up_term_poly_type σ) (0 .: τ >> shift))  as (P1' & H1 & <-).
    now_asimpl. exists (abs p P1'). split. eauto. now_asimpl. 
  - destruct P; inv Eqn.  destruct (IHstep _ _ _ eq_refl) as (P1' & H1 & <-)...
Qed.

Definition nf P := match P with abs s P => normal_form P
                           | ty_abs P => normal_form P | P => head_form P end.

Lemma nf_normal_form P :
  nf P -> normal_form P.
Proof.
  destruct P; cbn; eauto.
Qed.

Lemma sn_normal_form Γ P s :
  typing Γ P s -> (forall Q, ~ step P Q) -> nf P.
Proof.
  intros H Hstep.
  induction H; cbn in *.
  - eauto.
  - econstructor.
    destruct P.
    all: try now (eapply IHtyping1; intros ? ?; eapply Hstep; eauto).
    + exfalso. eapply Hstep; eauto.
    + inversion H. 
    + eapply nf_normal_form, IHtyping2. intros ? ?; eapply Hstep; eauto.
  - eapply nf_normal_form, IHtyping. intros ? ?. eapply Hstep. eauto.
  - econstructor.
    destruct P.
    all: try now (eapply IHtyping; intros ? ?; eapply Hstep; eauto).
    + inversion H.
    + exfalso. eapply Hstep. eauto.
  - eapply nf_normal_form, IHtyping. intros ? ?. eapply Hstep. eauto.
Qed.

Lemma sn_normal Γ P s :
  typing Γ P s ->
  sn P -> exists Q, clos_refl_trans _ step P Q /\ normal_form Q.
Proof.
  intros H.
  induction 1 as [P Hsn IH] in s, H |- *.
  destruct (progress P) as [Hstep | [Q Hstep]].
  - exists P. split. econstructor 2.
    eauto using nf_normal_form, sn_normal_form.
  - pose proof (Hstep' := Hstep).
    eapply IH in Hstep as (Q' & H1 & H2).
    + exists Q'. split. econstructor 3. econstructor 1. all: eauto.
    + eauto using preservation.
Qed.
