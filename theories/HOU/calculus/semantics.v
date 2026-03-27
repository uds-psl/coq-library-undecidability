Set Implicit Arguments.
From Undecidability.HOU Require Import calculus.prelim calculus.terms calculus.syntax std.std.
From Stdlib Require Import Morphisms Lia Finite. 

(* * Semantics **)
Section Semantics.

  Context {X: Const}.
  Implicit Types (s t: exp X) (delta: fin -> fin) (sigma: fin -> exp X).


  Reserved Notation "s > t" (at level 70).

  Inductive step : exp X -> exp X -> Prop :=
  | stepBeta s s' t: beta s t = s' -> (lambda s) t > s'
  | stepLam s s': s > s' -> lambda s > lambda s'
  | stepAppL s s' t: s > s' -> s t > s' t
  | stepAppR s t t': t > t' -> s t > s t'
  where "s > t" := (step s t).
  

  Notation "s >* t" := (star step s t) (at level 70).
  Hint Constructors step star : core.
  
  Notation "s ▷ t" := (evaluates step s t) (at level 60).
  Notation normal := (Normal step).


  (* ** Compatibility Properties *)
  Section CompatibilityProperties.

    #[export] Instance lam_proper: Proper (star step ++> star step) lam.
    Proof. induction 1; eauto. Qed.
    
    #[export] Instance app_proper: Proper (star step ++> star step ++> star step) app.
    Proof.
      intros x x' H1 y y' H2; induction H1; induction H2; eauto. 
    Qed.

    Lemma ren_step s t delta:
      s > t -> ren delta s > ren delta t.
    Proof.
      induction 1 in delta |-*; cbn; eauto.
      econstructor. subst. now asimpl. 
    Qed.
    
    Lemma ren_steps s t delta:
      s >* t -> ren delta s >* ren delta t.
    Proof.
      induction 1; eauto using ren_step. 
    Qed.

    #[export] Instance ren_step_proper:
      Proper (eq ++> step ++> step) (@ren X).
    Proof.
      intros ? zeta -> s t H; now eapply ren_step.
    Qed.

    #[export] Instance ren_steps_proper:
      Proper (eq ++> star step ++> star step) (@ren X).
    Proof.
      intros ? zeta -> s t H; now eapply ren_steps.
    Qed.

    Lemma subst_step s t sigma:
      s > t -> sigma • s > sigma • t.
    Proof.
      induction 1 in sigma |-*; cbn; eauto.
      - econstructor. subst. now asimpl.
    Qed.
    
    Lemma subst_steps s t sigma:
      s >* t -> sigma • s >* sigma • t.
    Proof.
      induction 1; eauto using subst_step. 
    Qed.

    #[export] Instance subst_step_proper:
      Proper (eq ++> step ++> step) (@subst_exp X).
    Proof.
      intros ? zeta -> s t H; now eapply subst_step.
    Qed.

    #[export] Instance subst_steps_proper:
      Proper (eq ++> star step ++> star step) (@subst_exp X).
    Proof.
      intros ? zeta -> s t H; now eapply subst_steps.
    Qed.

  End CompatibilityProperties.

  (* ** Normality Characterisation *)
  Section Normality.

    Lemma normal_var x: normal (var x).
    Proof. intros t H1; inv H1. Qed.
    
    Lemma normal_const c: normal (const c).
    Proof. intros t H1; inv H1. Qed.

    Lemma normal_lam_intro s: normal s -> normal (lambda s).
    Proof. intros H1 t H2; inv H2; eapply H1; eauto. Qed.
    
    Lemma normal_lam_elim s: normal (lambda s) -> normal s.
    Proof. intros H1 t H2; eapply H1; eauto. Qed.
    
    Lemma normal_app_l s t: normal (s t) -> normal s.
    Proof. intros H t' H1; eapply H; eauto. Qed. 

    Lemma normal_app_r s t: normal (s t) -> normal t.
    Proof. intros H t' H1; eapply H; eauto. Qed. 
    
    Lemma normal_app_not_lam s t: normal (s t) -> ~ isLam s.
    Proof. destruct s; intuition; eapply H; eauto. Qed.
    
    Lemma normal_app_intro s t:
      ~ isLam s -> normal s -> normal t -> normal (s t).
    Proof.
      intros; intros t' H2; inv H2; cbn in *; eauto.
      all: firstorder. 
    Qed.

    Hint Resolve normal_var normal_const normal_lam_intro
       normal_lam_elim normal_app_l normal_app_r normal_app_intro : core.
  

    Lemma normal_ren s delta:
      normal s -> normal (ren delta s).
    Proof.
      induction s in delta |-*; cbn; intuition.
      eapply normal_app_intro; eauto.
      destruct s1; cbn; eauto.
      intros _; eapply H; eauto.
    Qed.

    Lemma normal_subst s sigma:
      (forall x, ~ isLam (sigma x)) ->
      (forall x, normal (sigma x)) ->
      normal s -> normal (sigma • s).
    Proof.
      induction s in sigma |-*; intros H1 H2 N; cbn in *; intuition.
      - eapply normal_lam_intro, IHs; [| | now eapply normal_lam_elim].
        + intros []; cbn; intuition.
          unfold funcomp in *. eapply H1 with (x := n).
          destruct sigma; cbn; intuition.
        + intros []; cbn; intuition.
          now eapply normal_ren.
      - eapply normal_app_intro; eauto.
        destruct s1; eauto.
        intros _; eapply N; eauto.
    Qed.

    #[export] Instance dec_normal: Dec1 (normal).
    Proof.
      intros s; unfold Dec; induction s; intuition.
      all: try solve [right; contradict b; eauto].
      destruct s1; intuition. 
      right; intros H; eapply H; eauto. 
    Qed.

    Lemma head_atom s:
      normal s -> ~ isLam s -> isAtom (head s).
    Proof.
      induction s; cbn; eauto. 
      intros H _; cbn.
      eapply IHs1; eauto.
      destruct s1; eauto.
      intros _. eapply H; eauto.
    Qed.

  End Normality.
  
  Hint Resolve normal_var normal_const normal_lam_intro
       normal_lam_elim normal_app_l normal_app_r normal_app_intro : core.
  
  Hint Resolve head_atom : core. 
  


  (* ** Inversion Lemmas *)
  Section InversionLemmas.
  
    Lemma head_preserved s s':
      s > s' -> isLam (head s') -> isLam (head s).
    Proof.
      induction 1; cbn; eauto. 
    Qed. 

    Lemma steps_lam s v:
      lambda s >* v -> exists s', v = lambda s' /\ s >* s'.
    Proof.
      remember (lambda s) as t. intros H1. revert s Heqt.
      induction H1.
      - intros ? ->; eexists; eauto.
      - intros; subst. inv H. edestruct IHstar; eauto; intuition; subst.
        exists x. eauto. 
    Qed.

    Lemma steps_app s t v:
      app s t >* v -> (exists s', exists t', v = app s' t' /\ s >* s' /\ t >* t')
                    \/ (exists s', s >* lambda s' /\ isLam (head s)).
    Proof.
      remember (s t) as r. intros H1. revert s t Heqr.
      induction H1.
      - intros; subst. left; eexists; eexists; intuition.
      - intros; subst. inv H.
        + right. eexists; split; cbn; eauto.
        + edestruct IHstar; eauto.
          * destruct H as (? & ? & ? & ? & ?); subst.
            left. eexists; eexists; eauto.
          * destruct H as (? & ? & ?). right. eexists; split; eauto.
            eapply head_preserved; eauto.    
        + edestruct IHstar; eauto.
          * destruct H as (? & ? & ? & ? & ?); subst.
            left. eexists; eexists; eauto.
    Qed.

    Lemma steps_app_atom  s t v:
      isAtom s -> s t >* v -> exists t', v = s t' /\ t >* t'.
    Proof.
      destruct s;
        intros ? [(? & ? & ? & ?)|(? & ? & ?)] % steps_app; cbn in *; intuition.
      all: inv H2; eauto; inv H1.
    Qed.

    Lemma injective_upRen_exp_exp delta:
      Injective delta -> Injective (upRen_exp_exp delta).
    Proof.
      intros H [| x] [| y]; eauto.
      all: cbn; discriminate.
    Qed.

    
    Lemma anti_ren delta s t:
      Injective delta -> ren delta s = ren delta t -> s = t.
    Proof.
      intros H; induction s in delta, H, t |-*; destruct t; try discriminate.
      all: cbn; injection 1; intros; subst; eauto. 
      - erewrite IHs.
        3: eapply H1. eauto. eapply injective_upRen_exp_exp; eauto.
      - erewrite IHs1, IHs2; eauto.
    Qed.

    Lemma step_anti_ren delta s t: ren delta s > t -> exists t', s > t' /\ t = ren delta t'.
    Proof.
      remember (ren delta s) as s'; intros H;
        revert s Heqs'; induction H in delta |-*.
      all: intros []; try discriminate; injection 1; intros; subst.
      - destruct e; try discriminate; injection H1; intros; subst.
        exists (beta e e0); intuition. now asimpl.
      - edestruct IHstep; eauto.
        intuition; subst. exists (lambda x). intuition.
      - edestruct IHstep; eauto.
        exists (x e0); intuition; now subst.
      - edestruct IHstep; eauto.
        exists (e x); intuition; now subst.
    Qed. 

    Lemma steps_anti_ren delta s t:
      ren delta s >* t -> exists t', s >* t' /\ t = ren delta t'.
    Proof.
      remember (ren delta s) as s'. intros H; revert s Heqs'; induction H.
      - intros; subst. exists s; eauto. 
      - intros; subst. eapply step_anti_ren in H as []; intuition.
        edestruct (IHstar x); intuition.
        exists x0; eauto. 
    Qed.

  End InversionLemmas.
End Semantics.
   

Notation "s > t" := (step s t) (at level 70).
Notation "s >* t" := (star step s t) (at level 70).
Notation "s ▷ t" := (evaluates step s t) (at level 60).
Notation normal := (Normal step).

#[export] Hint Constructors step star : core.

#[export] Hint Resolve normal_var normal_const normal_lam_intro normal_app_intro : core.
#[export] Hint Resolve head_atom : core. 
