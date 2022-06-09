Set Implicit Arguments.
Require Import Morphisms Setoid.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms semantics. 

(* * Confluence *)
Section Confluence.

  Context {X: Const}.

  Reserved Notation "s ≫ t" (at level 60).

  Inductive par : exp X -> exp X -> Prop :=
  | parVar x: var x ≫ var x
  | parConst c: const c ≫ const c
  | parLam s s': s ≫ s' -> (lambda s) ≫ lambda s'
  | parBeta s s' t t' u: s ≫ s' -> t ≫ t' -> u = beta s' t' -> (lambda s) t ≫ u
  | parApp s s' t t': s ≫ s' -> t ≫ t' -> s t ≫ s' t'
  where "s ≫ t" := (par s t). 

  Hint Constructors par : core.

  Lemma refl_par: forall s, s ≫ s.
  Proof. induction s; eauto. Qed.

  Hint Immediate refl_par : core. 

  Global Instance refl_par_inst: Reflexive par.
  Proof.
    intros ?; eapply refl_par. 
  Qed.

  Lemma ren_compatible_par s s' delta:
    s ≫ s' -> ren delta s ≫ ren delta s'.
  Proof.
    induction 1 in delta |-*; cbn; eauto; subst.
    econstructor; eauto. now asimpl. 
  Qed.

  Lemma subst_compatible_par s s' sigma sigma':
    s ≫ s' -> (forall x, sigma x ≫ sigma' x) -> (sigma • s) ≫ (sigma'• s').
  Proof.
    induction 1 in sigma, sigma' |-*; cbn; eauto.
    - intros; econstructor; eapply IHpar.
      intros []; cbn; eauto using ren_compatible_par. 
    - intros; econstructor.
      eapply IHpar1 with (sigma' := up sigma'); eauto.
      intros []; cbn; eauto using ren_compatible_par. 
      eapply IHpar2; eauto. 
      subst; now asimpl. 
  Qed.

  Global Instance par_lam_proper: Proper (star par ++> star par) lam.
  Proof.
    intros s s' H; induction H; eauto.
  Qed.
  
  Global Instance par_app_proper: Proper (star par ++> star par ++> star par) app.
  Proof.
    intros s s' H; induction H; intros t t' H'; induction H'; eauto.
  Qed.



  Global Instance sandwich_step: subrelation step par.
  Proof.
    intros ??; induction 1; eauto.
  Qed.

  Global Instance sandwich_steps: subrelation par (star step).
  Proof.
    intros ??; induction 1; eauto.
    - rewrite IHpar; eauto.
    - rewrite IHpar1, IHpar2, stepBeta; eauto.
    - rewrite IHpar1, IHpar2; eauto. 
  Qed.


  Fixpoint rho (e: exp X) :=
    match e with
    | var x => var x
    | const c => const c
    | lambda s => lambda (rho s)
    | app (lambda s) t => beta (rho s) (rho t)
    | app s t => (rho s) (rho t)
    end.



  Lemma tak_fun_rho: tak_fun par rho.
  Proof. 
    intros s t H; induction H; cbn; eauto.
    - subst u; eapply subst_compatible_par; eauto.
      intros []; cbn; eauto.
    - destruct s; eauto.
      inv H; inv IHpar1.
      econstructor; eauto.
  Qed.



  Lemma confluence_step: confluent (@step X).
  Proof.
    eapply TMT.
    eapply sandwich_step. eapply sandwich_steps.
    typeclasses eauto.
    eapply tak_fun_rho.
  Qed.

End Confluence.

Notation "s ≫ t" := (par s t) (at level 60).
#[export] Hint Resolve confluence_step tak_fun_rho : core.
