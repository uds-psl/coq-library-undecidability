(* * Preliminaries FOL  *)
(* ** Syntax of FOL **)

From Undecidability.FOLP Require Export unscoped.

Class Signature := B_S { Funcs : Type; fun_ar : Funcs -> nat ;
              Preds : Type; pred_ar : Preds -> nat }.



Section fix_sig.

Context {Sigma : Signature}.

Inductive term  : Type :=
  | var_term : (nat)  -> term
  | Func : forall (f : Funcs), Vector.t term (fun_ar f) -> term .

Definition congr_Func { f : Funcs }  { s0 : Vector.t term (fun_ar f) } { t0 : Vector.t term (fun_ar f)} (H1 : s0 = t0) : Func  f s0 = Func  f t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => Func  f x) H1).

Fixpoint subst_term   (sigmaterm : (nat)  -> term ) (s : term ) : _ :=
    match s with
    | var_term  s => sigmaterm s
    | Func  f s0 => Func  f (Vector.map (subst_term sigmaterm) s0)
    end.

Definition up_term_term   (sigma : (nat)  -> term ) : _ :=
  (scons) ((var_term ) (var_zero)) ((funcomp) (subst_term ((funcomp) (var_term ) (shift))) sigma).


Definition upId_term_term  (sigma : (nat)  -> term ) (Eq : forall x, sigma x = (var_term ) x) : forall x, (up_term_term sigma) x = (var_term ) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_term ((funcomp) (var_term ) (shift))) (Eq fin_n)
  | 0 => eq_refl
  end.


Fixpoint idSubst_term  (sigmaterm : (nat)  -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : term ) : subst_term sigmaterm s = s :=
    match s with
    | var_term  s => Eqterm s
    | Func  f s0 => congr_Func ((vec_id (idSubst_term sigmaterm Eqterm)) s0)
    end.

Definition upExt_term_term   (sigma : (nat)  -> term ) (tau : (nat)  -> term ) (Eq : forall x, sigma x = tau x) : forall x, (up_term_term sigma) x = (up_term_term tau) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_term ((funcomp) (var_term) (shift))) (Eq fin_n)
  | 0 => eq_refl
  end.


Fixpoint ext_term   (sigmaterm : (nat)  -> term ) (tauterm : (nat)  -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : term ) : subst_term sigmaterm s = subst_term tauterm s :=
    match s with
    | var_term  s => Eqterm s
    | Func  f s0 => congr_Func ((vec_ext (ext_term sigmaterm tauterm Eqterm)) s0)
    end.

Fixpoint compSubstSubst_term    (sigmaterm : (nat)  -> term ) (tauterm : (nat)  -> term ) (thetaterm : (nat)  -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : term ) : subst_term tauterm (subst_term sigmaterm s) = subst_term thetaterm s :=
    match s with
    | var_term  s => Eqterm s
    | Func  f s0 => congr_Func ((vec_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s0)
    end.

Definition up_subst_subst_term_term    (sigma : (nat)  -> term ) (tauterm : (nat)  -> term ) (theta : (nat)  -> term ) (Eq : forall x, ((funcomp) (subst_term tauterm) sigma) x = theta x) : forall x, ((funcomp) (subst_term (up_term_term tauterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compSubstSubst_term ((funcomp) (var_term) (shift)) (up_term_term tauterm) ((funcomp) (up_term_term tauterm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_term tauterm ((funcomp) (var_term) (shift)) ((funcomp) (subst_term ((funcomp) (var_term ) (shift))) tauterm) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_term ((funcomp) (var_term ) (shift))) (Eq fin_n)))
  | 0 => eq_refl
  end.

Lemma instId_term  : subst_term (var_term ) = (@id) (term ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_term ) (fun n => eq_refl) (((@id) (term )) x))). Qed.

Lemma varL_term   (sigmaterm : (nat)  -> term ) : (funcomp) (subst_term sigmaterm) (var_term ) = sigmaterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_term    (sigmaterm : (nat)  -> term ) (tauterm : (nat)  -> term ) (s : term ) : subst_term tauterm (subst_term sigmaterm s) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_term sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_term    (sigmaterm : (nat)  -> term ) (tauterm : (nat)  -> term ) : (funcomp) (subst_term tauterm) (subst_term sigmaterm) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term sigmaterm tauterm n)). Qed.

Inductive form  : Type :=
  | Fal : form
  | Pred : forall (P : Preds), Vector.t term (pred_ar P) -> form
  | Impl : form  -> form  -> form
  | Conj : form  -> form  -> form
  | Disj : form  -> form  -> form
  | All : form  -> form
  | Ex : form  -> form .

Definition congr_Fal  : Fal  = Fal  :=
  eq_refl.

Definition congr_Pred { P : Preds }  { s0 : Vector.t term (pred_ar P) } { t0 : Vector.t term (pred_ar P) } (H1 : s0 = t0) : Pred  P s0 = Pred  P t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => Pred  P x) H1).

Definition congr_Impl  { s0 : form  } { s1 : form  } { t0 : form  } { t1 : form  } (H1 : s0 = t0) (H2 : s1 = t1) : Impl  s0 s1 = Impl  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => Impl  x (_)) H1)) ((ap) (fun x => Impl  (_) x) H2).

Definition congr_Conj  { s0 : form  } { s1 : form  } { t0 : form  } { t1 : form  } (H1 : s0 = t0) (H2 : s1 = t1) : Conj  s0 s1 = Conj  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => Conj  x (_)) H1)) ((ap) (fun x => Conj  (_) x) H2).

Definition congr_Disj  { s0 : form  } { s1 : form  } { t0 : form  } { t1 : form  } (H1 : s0 = t0) (H2 : s1 = t1) : Disj  s0 s1 = Disj  t0 t1 :=
  (eq_trans) ((eq_trans) (eq_refl) ((ap) (fun x => Disj  x (_)) H1)) ((ap) (fun x => Disj  (_) x) H2).

Definition congr_All  { s0 : form  } { t0 : form  } (H1 : s0 = t0) : All  s0 = All  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => All  x) H1).

Definition congr_Ex  { s0 : form  } { t0 : form  } (H1 : s0 = t0) : Ex  s0 = Ex  t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => Ex  x) H1).

Fixpoint subst_form   (sigmaterm : (nat)  -> term ) (s : form ) : _ :=
    match s with
    | Fal   => Fal
    | Pred  P s0 => Pred  P ((Vector.map (subst_term sigmaterm)) s0)
    | Impl  s0 s1 => Impl  ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | Conj  s0 s1 => Conj  ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | Disj  s0 s1 => Disj  ((subst_form sigmaterm) s0) ((subst_form sigmaterm) s1)
    | All  s0 => All  ((subst_form (up_term_term sigmaterm)) s0)
    | Ex  s0 => Ex  ((subst_form (up_term_term sigmaterm)) s0)
    end.

Fixpoint idSubst_form  (sigmaterm : (nat)  -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : form ) : subst_form sigmaterm s = s :=
    match s with
    | Fal   => congr_Fal
    | Pred  P s0 => congr_Pred ((vec_id (idSubst_term sigmaterm Eqterm)) s0)
    | Impl  s0 s1 => congr_Impl ((idSubst_form sigmaterm Eqterm) s0) ((idSubst_form sigmaterm Eqterm) s1)
    | Conj  s0 s1 => congr_Conj ((idSubst_form sigmaterm Eqterm) s0) ((idSubst_form sigmaterm Eqterm) s1)
    | Disj  s0 s1 => congr_Disj ((idSubst_form sigmaterm Eqterm) s0) ((idSubst_form sigmaterm Eqterm) s1)
    | All  s0 => congr_All ((idSubst_form (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s0)
    | Ex  s0 => congr_Ex ((idSubst_form (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s0)
    end.

Fixpoint ext_form   (sigmaterm : (nat)  -> term ) (tauterm : (nat)  -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : form ) : subst_form sigmaterm s = subst_form tauterm s :=
    match s with
    | Fal   => congr_Fal
    | Pred  P s0 => congr_Pred ((vec_ext (ext_term sigmaterm tauterm Eqterm)) s0)
    | Impl  s0 s1 => congr_Impl ((ext_form sigmaterm tauterm Eqterm) s0) ((ext_form sigmaterm tauterm Eqterm) s1)
    | Conj  s0 s1 => congr_Conj ((ext_form sigmaterm tauterm Eqterm) s0) ((ext_form sigmaterm tauterm Eqterm) s1)
    | Disj  s0 s1 => congr_Disj ((ext_form sigmaterm tauterm Eqterm) s0) ((ext_form sigmaterm tauterm Eqterm) s1)
    | All  s0 => congr_All ((ext_form (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s0)
    | Ex  s0 => congr_Ex ((ext_form (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s0)
    end.

Fixpoint compSubstSubst_form    (sigmaterm : (nat)  -> term ) (tauterm : (nat)  -> term ) (thetaterm : (nat)  -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : form ) : subst_form tauterm (subst_form sigmaterm s) = subst_form thetaterm s :=
    match s with
    | Fal   => congr_Fal
    | Pred  P s0 => congr_Pred ((vec_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s0)
    | Impl  s0 s1 => congr_Impl ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s1)
    | Conj  s0 s1 => congr_Conj ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s1)
    | Disj  s0 s1 => congr_Disj ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_form sigmaterm tauterm thetaterm Eqterm) s1)
    | All  s0 => congr_All ((compSubstSubst_form (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s0)
    | Ex  s0 => congr_Ex ((compSubstSubst_form (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s0)
    end.

Lemma instId_form  : subst_form (var_term ) = (@id) (form ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_form (var_term ) (fun n => eq_refl) (((@id) (form )) x))). Qed.

Lemma compComp_form    (sigmaterm : (nat)  -> term ) (tauterm : (nat)  -> term ) (s : form ) : subst_form tauterm (subst_form sigmaterm s) = subst_form ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_form sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_form    (sigmaterm : (nat)  -> term ) (tauterm : (nat)  -> term ) : (funcomp) (subst_form tauterm) (subst_form sigmaterm) = subst_form ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_form sigmaterm tauterm n)). Qed.

End fix_sig.

Instance Subst_term (Sigma : Signature)   : Subst1 ((nat)  -> term ) (term ) (term ) := @subst_term Sigma.

Instance Subst_form (Sigma : Signature)   : Subst1 ((nat)  -> term ) (form ) (form ) := @subst_form Sigma.

Instance VarInstance_term (Sigma : Signature) : Var ((nat) ) (term ) := @var_term Sigma.

Notation "x '__term'" := (var_term x) (at level 5, format "x __term") : subst_scope.

Notation "x '__term'" := (@ids (_) (_) VarInstance_term x) (at level 5, only printing, format "x __term") : subst_scope.

Notation "'var'" := (var_term) (only printing, at level 1) : subst_scope.

Class Up_term X Y := up_term : X -> Y.

Notation "↑__term" := (up_term) (only printing) : subst_scope.

Notation "↑__term" := (up_term_term) (only printing) : subst_scope.

Instance Up_term_term (Sigma : Signature)   : Up_term (_) (_) := @up_term_term Sigma.

Notation "s [ sigmaterm ]" := (subst_term sigmaterm s) (at level 7, left associativity, format "s '/' [ sigmaterm ]", only printing) : subst_scope.

(* Notation "[ sigmaterm ]" := (subst_term sigmaterm) (at level 0, left associativity, only printing) : fscope. *)

Notation "s [ sigmaterm ]" := (subst_form sigmaterm s) (at level 7, left associativity, format "s '/' [ sigmaterm ]", only printing) : subst_scope.

(* Notation "[ sigmaterm ]" := (subst_form sigmaterm) (at level 0, left associativity, only printing) : fscope. *)

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  Subst_term,  Subst_form,  VarInstance_term.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  Subst_term,  Subst_form,  VarInstance_term in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_term| progress rewrite ?term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?instId_form| progress rewrite ?form| progress rewrite ?compComp_form| progress rewrite ?compComp'_form| progress rewrite ?varL_term| progress (unfold up_ren, up_term_term)| progress (cbn [subst_term subst_form])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_term in *| progress rewrite ?term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?instId_form in *| progress rewrite ?form in *| progress rewrite ?compComp_form in *| progress rewrite ?compComp'_form in *| progress rewrite ?varL_term in *| progress (unfold up_ren, up_term_term)| progress (cbn [subst_term subst_form] in *)| fsimpl in *].
