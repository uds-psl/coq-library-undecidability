(* Automatically Synthesized by Autosubst. Considered preliminaries **)
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU Require Export unscoped.

Set Default Proof Using "Type".

Section Terms.

  Inductive type  : Type :=
  | typevar  : nat  -> type 
  | arr  : type  -> type  -> type .
  
  Structure Const :=
  {
    const_type:> Type;
    const_dis: Dis const_type;
    ctype: const_type -> type
  }.

  Context {X: Const}.


Lemma congr_typevar  { s0 : nat  } { t0 : nat  } : s0 = t0 -> typevar s0 = typevar t0 .
Proof. congruence. Qed.

Lemma congr_arr  { s0 : type  } { s1 : type  } { t0 : type  } { t1 : type  } : s0 = t0 -> s1 = t1 -> arr s0 s1 = arr t0 t1 .
Proof. congruence. Qed.

Inductive exp  : Type :=
  | var_exp  : fin  -> exp 
  | const  : X  -> exp 
  | lam  : exp  -> exp 
  | app  : exp  -> exp  -> exp .

Lemma congr_const  { s0 : X  } { t0 : X  } : s0 = t0 -> const  s0 = const  t0 .
Proof. congruence. Qed.

Lemma congr_lam  { s0 : exp  } { t0 : exp  } : s0 = t0 -> lam  s0 = lam  t0 .
Proof. congruence. Qed.

Lemma congr_app  { s0 : exp  } { s1 : exp  } { t0 : exp  } { t1 : exp  } : s0 = t0 -> s1 = t1 -> app  s0 s1 = app  t0 t1 .
Proof. congruence. Qed.

Definition upRen_exp_exp   (xi : fin  -> fin ) : _ :=
  up_ren xi.

Fixpoint ren_exp   (xiexp : fin  -> fin ) (s : exp ) : _ :=
    match s with
    | var_exp  s => (var_exp ) (xiexp s)
    | const  s0 => const  s0
    | lam  s0 => lam  (ren_exp (upRen_exp_exp xiexp) s0)
    | app  s0 s1 => app  (ren_exp xiexp s0) (ren_exp xiexp s1)
    end.

Definition up_exp_exp   (sigma : fin  -> exp ) : _ :=
  scons ((var_exp ) var_zero) (funcomp (ren_exp shift) sigma).

Fixpoint subst_exp   (sigmaexp : fin  -> exp ) (s : exp ) : _ :=
    match s with
    | var_exp  s => sigmaexp s
    | const  s0 => const  s0
    | lam  s0 => lam  (subst_exp (up_exp_exp sigmaexp) s0)
    | app  s0 s1 => app  (subst_exp sigmaexp s0) (subst_exp sigmaexp s1)
    end.

Definition upId_exp_exp  (sigma : fin  -> exp ) (Eq : forall x, sigma x = (var_exp ) x) : forall x, (up_exp_exp sigma) x = (var_exp ) x :=
  fun n => match n with
  | S n => ap (ren_exp shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint idSubst_exp  (sigmaexp : fin  -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp ) : subst_exp sigmaexp s = s :=
    match s with
    | var_exp  s => Eqexp s
    | const  s0 => congr_const (eq_refl s0)
    | lam  s0 => congr_lam (idSubst_exp (up_exp_exp sigmaexp) (upId_exp_exp (_) Eqexp) s0)
    | app  s0 s1 => congr_app (idSubst_exp sigmaexp Eqexp s0) (idSubst_exp sigmaexp Eqexp s1)
    end.

Definition upExtRen_exp_exp   (xi : fin  -> fin ) (zeta : fin  -> fin ) (Eq : forall x, xi x = zeta x) : forall x, (upRen_exp_exp xi) x = (upRen_exp_exp zeta) x :=
  fun n => match n with
  | S n => ap shift (Eq n)
  | 0 => eq_refl
  end.

Fixpoint extRen_exp   (xiexp : fin  -> fin ) (zetaexp : fin  -> fin ) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp ) : ren_exp xiexp s = ren_exp zetaexp s :=
    match s with
    | var_exp  s => ap (var_exp ) (Eqexp s)
    | const  s0 => congr_const (eq_refl s0)
    | lam  s0 => congr_lam (extRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upExtRen_exp_exp (_) (_) Eqexp) s0)
    | app  s0 s1 => congr_app (extRen_exp xiexp zetaexp Eqexp s0) (extRen_exp xiexp zetaexp Eqexp s1)
    end.

Definition upExt_exp_exp   (sigma : fin  -> exp ) (tau : fin  -> exp ) (Eq : forall x, sigma x = tau x) : forall x, (up_exp_exp sigma) x = (up_exp_exp tau) x :=
  fun n => match n with
  | S n => ap (ren_exp shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint ext_exp   (sigmaexp : fin  -> exp ) (tauexp : fin  -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp ) : subst_exp sigmaexp s = subst_exp tauexp s :=
    match s with
    | var_exp  s => Eqexp s
    | const  s0 => congr_const (eq_refl s0)
    | lam  s0 => congr_lam (ext_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (upExt_exp_exp (_) (_) Eqexp) s0)
    | app  s0 s1 => congr_app (ext_exp sigmaexp tauexp Eqexp s0) (ext_exp sigmaexp tauexp Eqexp s1)
    end.

Fixpoint compRenRen_exp    (xiexp : fin  -> fin ) (zetaexp : fin  -> fin ) (rhoexp : fin  -> fin ) (Eqexp : forall x, (funcomp zetaexp xiexp) x = rhoexp x) (s : exp ) : ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s :=
    match s with
    | var_exp  s => ap (var_exp ) (Eqexp s)
    | const  s0 => congr_const (eq_refl s0)
    | lam  s0 => congr_lam (compRenRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upRen_exp_exp rhoexp) (up_ren_ren (_) (_) (_) Eqexp) s0)
    | app  s0 s1 => congr_app (compRenRen_exp xiexp zetaexp rhoexp Eqexp s0) (compRenRen_exp xiexp zetaexp rhoexp Eqexp s1)
    end.

Definition up_ren_subst_exp_exp    (xi : fin  -> fin ) (tau : fin  -> exp ) (theta : fin  -> exp ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_exp_exp tau) (upRen_exp_exp xi)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | S n => ap (ren_exp shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint compRenSubst_exp    (xiexp : fin  -> fin ) (tauexp : fin  -> exp ) (thetaexp : fin  -> exp ) (Eqexp : forall x, (funcomp tauexp xiexp) x = thetaexp x) (s : exp ) : subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s :=
    match s with
    | var_exp  s => Eqexp s
    | const  s0 => congr_const (eq_refl s0)
    | lam  s0 => congr_lam (compRenSubst_exp (upRen_exp_exp xiexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_ren_subst_exp_exp (_) (_) (_) Eqexp) s0)
    | app  s0 s1 => congr_app (compRenSubst_exp xiexp tauexp thetaexp Eqexp s0) (compRenSubst_exp xiexp tauexp thetaexp Eqexp s1)
    end.

Definition up_subst_ren_exp_exp    (sigma : fin  -> exp ) (zetaexp : fin  -> fin ) (theta : fin  -> exp ) (Eq : forall x, (funcomp (ren_exp zetaexp) sigma) x = theta x) : forall x, (funcomp (ren_exp (upRen_exp_exp zetaexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | S n => eq_trans (compRenRen_exp shift (upRen_exp_exp zetaexp) (funcomp shift zetaexp) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_exp zetaexp shift (funcomp shift zetaexp) (fun x => eq_refl) (sigma n))) (ap (ren_exp shift) (Eq n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstRen__exp    (sigmaexp : fin  -> exp ) (zetaexp : fin  -> fin ) (thetaexp : fin  -> exp ) (Eqexp : forall x, (funcomp (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp ) : ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s :=
    match s with
    | var_exp  s => Eqexp s
    | const  s0 => congr_const (eq_refl s0)
    | lam  s0 => congr_lam (compSubstRen__exp (up_exp_exp sigmaexp) (upRen_exp_exp zetaexp) (up_exp_exp thetaexp) (up_subst_ren_exp_exp (_) (_) (_) Eqexp) s0)
    | app  s0 s1 => congr_app (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s0) (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s1)
    end.

Definition up_subst_subst_exp_exp    (sigma : fin  -> exp ) (tauexp : fin  -> exp ) (theta : fin  -> exp ) (Eq : forall x, (funcomp (subst_exp tauexp) sigma) x = theta x) : forall x, (funcomp (subst_exp (up_exp_exp tauexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | S n => eq_trans (compRenSubst_exp shift (up_exp_exp tauexp) (funcomp (up_exp_exp tauexp) shift) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen__exp tauexp shift (funcomp (ren_exp shift) tauexp) (fun x => eq_refl) (sigma n))) (ap (ren_exp shift) (Eq n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstSubst_exp    (sigmaexp : fin  -> exp ) (tauexp : fin  -> exp ) (thetaexp : fin  -> exp ) (Eqexp : forall x, (funcomp (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp ) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s :=
    match s with
    | var_exp  s => Eqexp s
    | const  s0 => congr_const (eq_refl s0)
    | lam  s0 => congr_lam (compSubstSubst_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_subst_subst_exp_exp (_) (_) (_) Eqexp) s0)
    | app  s0 s1 => congr_app (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s0) (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s1)
    end.

Definition rinstInst_up_exp_exp   (xi : fin  -> fin ) (sigma : fin  -> exp ) (Eq : forall x, (funcomp (var_exp ) xi) x = sigma x) : forall x, (funcomp (var_exp ) (upRen_exp_exp xi)) x = (up_exp_exp sigma) x :=
  fun n => match n with
  | S n => ap (ren_exp shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint rinst_inst_exp   (xiexp : fin  -> fin ) (sigmaexp : fin  -> exp ) (Eqexp : forall x, (funcomp (var_exp ) xiexp) x = sigmaexp x) (s : exp ) : ren_exp xiexp s = subst_exp sigmaexp s :=
    match s with
    | var_exp  s => Eqexp s
    | const  s0 => congr_const (eq_refl s0)
    | lam  s0 => congr_lam (rinst_inst_exp (upRen_exp_exp xiexp) (up_exp_exp sigmaexp) (rinstInst_up_exp_exp (_) (_) Eqexp) s0)
    | app  s0 s1 => congr_app (rinst_inst_exp xiexp sigmaexp Eqexp s0) (rinst_inst_exp xiexp sigmaexp Eqexp s1)
    end.

Lemma instId_exp  : subst_exp (var_exp ) = id .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => idSubst_exp (var_exp ) (fun n => eq_refl) (id x))). Qed.

Lemma varL_exp   (sigmaexp : fin  -> exp ) : funcomp (subst_exp sigmaexp) (var_exp ) = sigmaexp .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma rinstInst_exp   (xiexp : fin  -> fin ) : ren_exp xiexp = subst_exp (funcomp (var_exp ) xiexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => rinst_inst_exp xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma compComp_exp    (sigmaexp : fin  -> exp ) (tauexp : fin  -> exp ) (s : exp ) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp (funcomp (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp    (sigmaexp : fin  -> exp ) (tauexp : fin  -> exp ) : funcomp (subst_exp tauexp) (subst_exp sigmaexp) = subst_exp (funcomp (subst_exp tauexp) sigmaexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compComp_exp sigmaexp tauexp n)). Qed.


End Terms.



(* CUSTOM CHANGES *)
Definition beta {X} (s: exp) (t: exp) := @subst_exp X (t .: var_exp) s.
Hint Rewrite @instId_exp @rinstInst_exp @compComp_exp @compComp'_exp @varL_exp : asimpl.
#[export] Hint Unfold beta upRen_exp_exp up_exp_exp : asimpl. 

Ltac asimpl := autounfold with asimpl; autorewrite with asimpl using (cbn [subst_exp ren_exp]; fsimpl).
Tactic Notation "asimpl" "in" hyp(J) :=
  autounfold with asimpl in J; autorewrite with asimpl in J using (cbn [subst_exp ren_exp] in J; fsimplin J).
