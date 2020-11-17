Require Import Undecidability.SystemF.Autosubst.unscoped.
Require Import Undecidability.SystemF.SysF.

Require Import Morphisms.

Local Notation "f === g" := (fext_eq f g) (at level 80).

Section pure_term.
(*
(** pure lambda-terms M, N, .. *)
Inductive pure_term : Type :=
  | pure_var : nat -> pure_term 
  | pure_app : pure_term -> pure_term -> pure_term 
  | pure_abs : pure_term -> pure_term.
*)

Lemma congr_pure_app  { s0 : pure_term   } { s1 : pure_term   } { t0 : pure_term   } { t1 : pure_term   } : ( s0 = t0 ) -> ( s1 = t1 ) -> pure_app  s0 s1 = pure_app  t0 t1 .
Proof. congruence. Qed.

Lemma congr_pure_abs  { s0 : pure_term   } { t0 : pure_term   } : ( s0 = t0 ) -> pure_abs  s0 = pure_abs  t0 .
Proof. congruence. Qed.

Definition upRen_pure_term_pure_term   (xi : ( nat  ) -> nat ) : ( nat  ) -> nat  :=
  up_ren xi.

Fixpoint ren_pure_term   (xipure_term : ( nat  ) -> nat ) (s : pure_term ) : pure_term  :=
    match s return pure_term  with
    | pure_var  s => (pure_var ) (xipure_term s)
    | pure_app  s0 s1 => pure_app  (ren_pure_term xipure_term s0) (ren_pure_term xipure_term s1)
    | pure_abs  s0 => pure_abs  (ren_pure_term (upRen_pure_term_pure_term xipure_term) s0)
    end.

Definition up_pure_term_pure_term   (sigma : ( nat  ) -> pure_term ) : ( nat  ) -> pure_term  :=
  scons ((pure_var ) var_zero) (funcomp (ren_pure_term shift) sigma).

Fixpoint subst_pure_term   (sigmapure_term : ( nat  ) -> pure_term ) (s : pure_term ) : pure_term  :=
    match s return pure_term  with
    | pure_var  s => sigmapure_term s
    | pure_app  s0 s1 => pure_app  (subst_pure_term sigmapure_term s0) (subst_pure_term sigmapure_term s1)
    | pure_abs  s0 => pure_abs  (subst_pure_term (up_pure_term_pure_term sigmapure_term) s0)
    end.

Definition upId_pure_term_pure_term  (sigma : ( nat  ) -> pure_term ) (Eq : forall x, sigma x = (pure_var ) x) : forall x, (up_pure_term_pure_term sigma) x = (pure_var ) x :=
  fun n => match n with
  | S n => ap (ren_pure_term shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint idSubst_pure_term  (sigmapure_term : ( nat  ) -> pure_term ) (Eqpure_term : forall x, sigmapure_term x = (pure_var ) x) (s : pure_term ) : subst_pure_term sigmapure_term s = s :=
    match s return subst_pure_term sigmapure_term s = s with
    | pure_var  s => Eqpure_term s
    | pure_app  s0 s1 => congr_pure_app (idSubst_pure_term sigmapure_term Eqpure_term s0) (idSubst_pure_term sigmapure_term Eqpure_term s1)
    | pure_abs  s0 => congr_pure_abs (idSubst_pure_term (up_pure_term_pure_term sigmapure_term) (upId_pure_term_pure_term (_) Eqpure_term) s0)
    end.

Definition upExtRen_pure_term_pure_term   (xi : ( nat  ) -> nat ) (zeta : ( nat  ) -> nat ) (Eq : forall x, xi x = zeta x) : forall x, (upRen_pure_term_pure_term xi) x = (upRen_pure_term_pure_term zeta) x :=
  fun n => match n with
  | S n => ap shift (Eq n)
  | 0 => eq_refl
  end.

Fixpoint extRen_pure_term   (xipure_term : ( nat  ) -> nat ) (zetapure_term : ( nat  ) -> nat ) (Eqpure_term : forall x, xipure_term x = zetapure_term x) (s : pure_term ) : ren_pure_term xipure_term s = ren_pure_term zetapure_term s :=
    match s return ren_pure_term xipure_term s = ren_pure_term zetapure_term s with
    | pure_var  s => ap (pure_var ) (Eqpure_term s)
    | pure_app  s0 s1 => congr_pure_app (extRen_pure_term xipure_term zetapure_term Eqpure_term s0) (extRen_pure_term xipure_term zetapure_term Eqpure_term s1)
    | pure_abs  s0 => congr_pure_abs (extRen_pure_term (upRen_pure_term_pure_term xipure_term) (upRen_pure_term_pure_term zetapure_term) (upExtRen_pure_term_pure_term (_) (_) Eqpure_term) s0)
    end.

Definition upExt_pure_term_pure_term   (sigma : ( nat  ) -> pure_term ) (tau : ( nat  ) -> pure_term ) (Eq : forall x, sigma x = tau x) : forall x, (up_pure_term_pure_term sigma) x = (up_pure_term_pure_term tau) x :=
  fun n => match n with
  | S n => ap (ren_pure_term shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint ext_pure_term   (sigmapure_term : ( nat  ) -> pure_term ) (taupure_term : ( nat  ) -> pure_term ) (Eqpure_term : forall x, sigmapure_term x = taupure_term x) (s : pure_term ) : subst_pure_term sigmapure_term s = subst_pure_term taupure_term s :=
    match s return subst_pure_term sigmapure_term s = subst_pure_term taupure_term s with
    | pure_var  s => Eqpure_term s
    | pure_app  s0 s1 => congr_pure_app (ext_pure_term sigmapure_term taupure_term Eqpure_term s0) (ext_pure_term sigmapure_term taupure_term Eqpure_term s1)
    | pure_abs  s0 => congr_pure_abs (ext_pure_term (up_pure_term_pure_term sigmapure_term) (up_pure_term_pure_term taupure_term) (upExt_pure_term_pure_term (_) (_) Eqpure_term) s0)
    end.

Definition up_ren_ren_pure_term_pure_term    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> nat ) (theta : ( nat  ) -> nat ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (upRen_pure_term_pure_term tau) (upRen_pure_term_pure_term xi)) x = (upRen_pure_term_pure_term theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_pure_term    (xipure_term : ( nat  ) -> nat ) (zetapure_term : ( nat  ) -> nat ) (rhopure_term : ( nat  ) -> nat ) (Eqpure_term : forall x, (funcomp zetapure_term xipure_term) x = rhopure_term x) (s : pure_term ) : ren_pure_term zetapure_term (ren_pure_term xipure_term s) = ren_pure_term rhopure_term s :=
    match s return ren_pure_term zetapure_term (ren_pure_term xipure_term s) = ren_pure_term rhopure_term s with
    | pure_var  s => ap (pure_var ) (Eqpure_term s)
    | pure_app  s0 s1 => congr_pure_app (compRenRen_pure_term xipure_term zetapure_term rhopure_term Eqpure_term s0) (compRenRen_pure_term xipure_term zetapure_term rhopure_term Eqpure_term s1)
    | pure_abs  s0 => congr_pure_abs (compRenRen_pure_term (upRen_pure_term_pure_term xipure_term) (upRen_pure_term_pure_term zetapure_term) (upRen_pure_term_pure_term rhopure_term) (up_ren_ren_pure_term_pure_term (_) (_) (_) Eqpure_term) s0)
    end.

Definition up_ren_subst_pure_term_pure_term    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> pure_term ) (theta : ( nat  ) -> pure_term ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_pure_term_pure_term tau) (upRen_pure_term_pure_term xi)) x = (up_pure_term_pure_term theta) x :=
  fun n => match n with
  | S n => ap (ren_pure_term shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint compRenSubst_pure_term    (xipure_term : ( nat  ) -> nat ) (taupure_term : ( nat  ) -> pure_term ) (thetapure_term : ( nat  ) -> pure_term ) (Eqpure_term : forall x, (funcomp taupure_term xipure_term) x = thetapure_term x) (s : pure_term ) : subst_pure_term taupure_term (ren_pure_term xipure_term s) = subst_pure_term thetapure_term s :=
    match s return subst_pure_term taupure_term (ren_pure_term xipure_term s) = subst_pure_term thetapure_term s with
    | pure_var  s => Eqpure_term s
    | pure_app  s0 s1 => congr_pure_app (compRenSubst_pure_term xipure_term taupure_term thetapure_term Eqpure_term s0) (compRenSubst_pure_term xipure_term taupure_term thetapure_term Eqpure_term s1)
    | pure_abs  s0 => congr_pure_abs (compRenSubst_pure_term (upRen_pure_term_pure_term xipure_term) (up_pure_term_pure_term taupure_term) (up_pure_term_pure_term thetapure_term) (up_ren_subst_pure_term_pure_term (_) (_) (_) Eqpure_term) s0)
    end.

Definition up_subst_ren_pure_term_pure_term    (sigma : ( nat  ) -> pure_term ) (zetapure_term : ( nat  ) -> nat ) (theta : ( nat  ) -> pure_term ) (Eq : forall x, (funcomp (ren_pure_term zetapure_term) sigma) x = theta x) : forall x, (funcomp (ren_pure_term (upRen_pure_term_pure_term zetapure_term)) (up_pure_term_pure_term sigma)) x = (up_pure_term_pure_term theta) x :=
  fun n => match n with
  | S n => eq_trans (compRenRen_pure_term shift (upRen_pure_term_pure_term zetapure_term) (funcomp shift zetapure_term) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_pure_term zetapure_term shift (funcomp shift zetapure_term) (fun x => eq_refl) (sigma n))) (ap (ren_pure_term shift) (Eq n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstRen_pure_term    (sigmapure_term : ( nat  ) -> pure_term ) (zetapure_term : ( nat  ) -> nat ) (thetapure_term : ( nat  ) -> pure_term ) (Eqpure_term : forall x, (funcomp (ren_pure_term zetapure_term) sigmapure_term) x = thetapure_term x) (s : pure_term ) : ren_pure_term zetapure_term (subst_pure_term sigmapure_term s) = subst_pure_term thetapure_term s :=
    match s return ren_pure_term zetapure_term (subst_pure_term sigmapure_term s) = subst_pure_term thetapure_term s with
    | pure_var  s => Eqpure_term s
    | pure_app  s0 s1 => congr_pure_app (compSubstRen_pure_term sigmapure_term zetapure_term thetapure_term Eqpure_term s0) (compSubstRen_pure_term sigmapure_term zetapure_term thetapure_term Eqpure_term s1)
    | pure_abs  s0 => congr_pure_abs (compSubstRen_pure_term (up_pure_term_pure_term sigmapure_term) (upRen_pure_term_pure_term zetapure_term) (up_pure_term_pure_term thetapure_term) (up_subst_ren_pure_term_pure_term (_) (_) (_) Eqpure_term) s0)
    end.

Definition up_subst_subst_pure_term_pure_term    (sigma : ( nat  ) -> pure_term ) (taupure_term : ( nat  ) -> pure_term ) (theta : ( nat  ) -> pure_term ) (Eq : forall x, (funcomp (subst_pure_term taupure_term) sigma) x = theta x) : forall x, (funcomp (subst_pure_term (up_pure_term_pure_term taupure_term)) (up_pure_term_pure_term sigma)) x = (up_pure_term_pure_term theta) x :=
  fun n => match n with
  | S n => eq_trans (compRenSubst_pure_term shift (up_pure_term_pure_term taupure_term) (funcomp (up_pure_term_pure_term taupure_term) shift) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen_pure_term taupure_term shift (funcomp (ren_pure_term shift) taupure_term) (fun x => eq_refl) (sigma n))) (ap (ren_pure_term shift) (Eq n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstSubst_pure_term    (sigmapure_term : ( nat  ) -> pure_term ) (taupure_term : ( nat  ) -> pure_term ) (thetapure_term : ( nat  ) -> pure_term ) (Eqpure_term : forall x, (funcomp (subst_pure_term taupure_term) sigmapure_term) x = thetapure_term x) (s : pure_term ) : subst_pure_term taupure_term (subst_pure_term sigmapure_term s) = subst_pure_term thetapure_term s :=
    match s return subst_pure_term taupure_term (subst_pure_term sigmapure_term s) = subst_pure_term thetapure_term s with
    | pure_var  s => Eqpure_term s
    | pure_app  s0 s1 => congr_pure_app (compSubstSubst_pure_term sigmapure_term taupure_term thetapure_term Eqpure_term s0) (compSubstSubst_pure_term sigmapure_term taupure_term thetapure_term Eqpure_term s1)
    | pure_abs  s0 => congr_pure_abs (compSubstSubst_pure_term (up_pure_term_pure_term sigmapure_term) (up_pure_term_pure_term taupure_term) (up_pure_term_pure_term thetapure_term) (up_subst_subst_pure_term_pure_term (_) (_) (_) Eqpure_term) s0)
    end.

Definition rinstInst_up_pure_term_pure_term   (xi : ( nat  ) -> nat ) (sigma : ( nat  ) -> pure_term ) (Eq : forall x, (funcomp (pure_var ) xi) x = sigma x) : forall x, (funcomp (pure_var ) (upRen_pure_term_pure_term xi)) x = (up_pure_term_pure_term sigma) x :=
  fun n => match n with
  | S n => ap (ren_pure_term shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint rinst_inst_pure_term   (xipure_term : ( nat  ) -> nat ) (sigmapure_term : ( nat  ) -> pure_term ) (Eqpure_term : forall x, (funcomp (pure_var ) xipure_term) x = sigmapure_term x) (s : pure_term ) : ren_pure_term xipure_term s = subst_pure_term sigmapure_term s :=
    match s return ren_pure_term xipure_term s = subst_pure_term sigmapure_term s with
    | pure_var  s => Eqpure_term s
    | pure_app  s0 s1 => congr_pure_app (rinst_inst_pure_term xipure_term sigmapure_term Eqpure_term s0) (rinst_inst_pure_term xipure_term sigmapure_term Eqpure_term s1)
    | pure_abs  s0 => congr_pure_abs (rinst_inst_pure_term (upRen_pure_term_pure_term xipure_term) (up_pure_term_pure_term sigmapure_term) (rinstInst_up_pure_term_pure_term (_) (_) Eqpure_term) s0)
    end.

Lemma rinstInst_pure_term   (xipure_term : ( nat  ) -> nat ) : ren_pure_term xipure_term === subst_pure_term (funcomp (pure_var ) xipure_term) .
Proof. exact ((fun x => rinst_inst_pure_term xipure_term (_) (fun n => eq_refl) x)). Qed.

Lemma instId_pure_term  : subst_pure_term (pure_var ) === id .
Proof. exact ((fun x => idSubst_pure_term (pure_var ) (fun n => eq_refl) (id x))). Qed.

Lemma feq_trans {X Y} {f g h : X -> Y} :
  f === g -> g === h -> f === h.
Proof.
  cbv. congruence.
Qed.

Lemma rinstId_pure_term  : @ren_pure_term   id === id .
Proof. exact (feq_trans (rinstInst_pure_term id) instId_pure_term). Qed.

Lemma varL_pure_term   (sigmapure_term : ( nat  ) -> pure_term ) : funcomp (subst_pure_term sigmapure_term) (pure_var ) === sigmapure_term .
Proof. exact ((fun x => eq_refl)). Qed.

Lemma varLRen_pure_term   (xipure_term : ( nat  ) -> nat ) : funcomp (ren_pure_term xipure_term) (pure_var ) === funcomp (pure_var ) xipure_term .
Proof. exact ((fun x => eq_refl)). Qed.

Lemma compComp_pure_term    (sigmapure_term : ( nat  ) -> pure_term ) (taupure_term : ( nat  ) -> pure_term ) (s : pure_term ) : subst_pure_term taupure_term (subst_pure_term sigmapure_term s) = subst_pure_term (funcomp (subst_pure_term taupure_term) sigmapure_term) s .
Proof. exact (compSubstSubst_pure_term sigmapure_term taupure_term (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_pure_term    (sigmapure_term : ( nat  ) -> pure_term ) (taupure_term : ( nat  ) -> pure_term ) : funcomp (subst_pure_term taupure_term) (subst_pure_term sigmapure_term) === subst_pure_term (funcomp (subst_pure_term taupure_term) sigmapure_term) .
Proof. exact ((fun n => compComp_pure_term sigmapure_term taupure_term n)). Qed.

Lemma compRen_pure_term    (sigmapure_term : ( nat  ) -> pure_term ) (zetapure_term : ( nat  ) -> nat ) (s : pure_term ) : ren_pure_term zetapure_term (subst_pure_term sigmapure_term s) = subst_pure_term (funcomp (ren_pure_term zetapure_term) sigmapure_term) s .
Proof. exact (compSubstRen_pure_term sigmapure_term zetapure_term (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_pure_term    (sigmapure_term : ( nat  ) -> pure_term ) (zetapure_term : ( nat  ) -> nat ) : funcomp (ren_pure_term zetapure_term) (subst_pure_term sigmapure_term) === subst_pure_term (funcomp (ren_pure_term zetapure_term) sigmapure_term) .
Proof. exact ((fun n => compRen_pure_term sigmapure_term zetapure_term n)). Qed.

Lemma renComp_pure_term    (xipure_term : ( nat  ) -> nat ) (taupure_term : ( nat  ) -> pure_term ) (s : pure_term ) : subst_pure_term taupure_term (ren_pure_term xipure_term s) = subst_pure_term (funcomp taupure_term xipure_term) s .
Proof. exact (compRenSubst_pure_term xipure_term taupure_term (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_pure_term    (xipure_term : ( nat  ) -> nat ) (taupure_term : ( nat  ) -> pure_term ) : funcomp (subst_pure_term taupure_term) (ren_pure_term xipure_term) === subst_pure_term (funcomp taupure_term xipure_term) .
Proof. exact ((fun n => renComp_pure_term xipure_term taupure_term n)). Qed.

Lemma renRen_pure_term    (xipure_term : ( nat  ) -> nat ) (zetapure_term : ( nat  ) -> nat ) (s : pure_term ) : ren_pure_term zetapure_term (ren_pure_term xipure_term s) = ren_pure_term (funcomp zetapure_term xipure_term) s .
Proof. exact (compRenRen_pure_term xipure_term zetapure_term (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_pure_term    (xipure_term : ( nat  ) -> nat ) (zetapure_term : ( nat  ) -> nat ) : funcomp (ren_pure_term zetapure_term) (ren_pure_term xipure_term) === ren_pure_term (funcomp zetapure_term xipure_term) .
Proof. exact ((fun n => renRen_pure_term xipure_term zetapure_term n)). Qed.

End pure_term.

Section poly_type.
(*
(** polymorphic types s, t, ..*)
Inductive poly_type : Type :=
  | poly_var : nat -> poly_type 
  | poly_arr : poly_type -> poly_type -> poly_type 
  | poly_abs : poly_type -> poly_type.
*)

Lemma congr_poly_arr  { s0 : poly_type   } { s1 : poly_type   } { t0 : poly_type   } { t1 : poly_type   } : ( s0 = t0 ) -> ( s1 = t1 ) -> poly_arr  s0 s1 = poly_arr  t0 t1 .
Proof. congruence. Qed.

Lemma congr_poly_abs  { s0 : poly_type   } { t0 : poly_type   } : ( s0 = t0 ) -> poly_abs  s0 = poly_abs  t0 .
Proof. congruence. Qed.

Definition upRen_poly_type_poly_type   (xi : ( nat  ) -> nat ) : ( nat  ) -> nat  :=
  up_ren xi.

(*
Fixpoint ren_poly_type   (xipoly_type : ( nat  ) -> nat ) (s : poly_type ) : poly_type  :=
    match s return poly_type  with
    | poly_var  s => (poly_var ) (xipoly_type s)
    | poly_arr  s0 s1 => poly_arr  (ren_poly_type xipoly_type s0) (ren_poly_type xipoly_type s1)
    | poly_abs  s0 => poly_abs  (ren_poly_type (upRen_poly_type_poly_type xipoly_type) s0)
    end.
*)

Definition up_poly_type_poly_type   (sigma : ( nat  ) -> poly_type ) : ( nat  ) -> poly_type  :=
  scons ((poly_var ) var_zero) (funcomp (ren_poly_type shift) sigma).

(*
Fixpoint subst_poly_type   (sigmapoly_type : ( nat  ) -> poly_type ) (s : poly_type ) : poly_type  :=
    match s return poly_type  with
    | poly_var  s => sigmapoly_type s
    | poly_arr  s0 s1 => poly_arr  (subst_poly_type sigmapoly_type s0) (subst_poly_type sigmapoly_type s1)
    | poly_abs  s0 => poly_abs  (subst_poly_type (up_poly_type_poly_type sigmapoly_type) s0)
    end.
*)

Definition upId_poly_type_poly_type  (sigma : ( nat  ) -> poly_type ) (Eq : forall x, sigma x = (poly_var ) x) : forall x, (up_poly_type_poly_type sigma) x = (poly_var ) x :=
  fun n => match n with
  | S n => ap (ren_poly_type shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint idSubst_poly_type  (sigmapoly_type : ( nat  ) -> poly_type ) (Eqpoly_type : forall x, sigmapoly_type x = (poly_var ) x) (s : poly_type ) : subst_poly_type sigmapoly_type s = s :=
    match s return subst_poly_type sigmapoly_type s = s with
    | poly_var  s => Eqpoly_type s
    | poly_arr  s0 s1 => congr_poly_arr (idSubst_poly_type sigmapoly_type Eqpoly_type s0) (idSubst_poly_type sigmapoly_type Eqpoly_type s1)
    | poly_abs  s0 => congr_poly_abs (idSubst_poly_type (up_poly_type_poly_type sigmapoly_type) (upId_poly_type_poly_type (_) Eqpoly_type) s0)
    end.

Definition upExtRen_poly_type_poly_type   (xi : ( nat  ) -> nat ) (zeta : ( nat  ) -> nat ) (Eq : forall x, xi x = zeta x) : forall x, (upRen_poly_type_poly_type xi) x = (upRen_poly_type_poly_type zeta) x :=
  fun n => match n with
  | S n => ap shift (Eq n)
  | 0 => eq_refl
  end.

Fixpoint extRen_poly_type   (xipoly_type : ( nat  ) -> nat ) (zetapoly_type : ( nat  ) -> nat ) (Eqpoly_type : forall x, xipoly_type x = zetapoly_type x) (s : poly_type ) : ren_poly_type xipoly_type s = ren_poly_type zetapoly_type s :=
    match s return ren_poly_type xipoly_type s = ren_poly_type zetapoly_type s with
    | poly_var  s => ap (poly_var ) (Eqpoly_type s)
    | poly_arr  s0 s1 => congr_poly_arr (extRen_poly_type xipoly_type zetapoly_type Eqpoly_type s0) (extRen_poly_type xipoly_type zetapoly_type Eqpoly_type s1)
    | poly_abs  s0 => congr_poly_abs (extRen_poly_type (upRen_poly_type_poly_type xipoly_type) (upRen_poly_type_poly_type zetapoly_type) (upExtRen_poly_type_poly_type (_) (_) Eqpoly_type) s0)
    end.

Definition upExt_poly_type_poly_type   (sigma : ( nat  ) -> poly_type ) (tau : ( nat  ) -> poly_type ) (Eq : forall x, sigma x = tau x) : forall x, (up_poly_type_poly_type sigma) x = (up_poly_type_poly_type tau) x :=
  fun n => match n with
  | S n => ap (ren_poly_type shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint ext_poly_type   (sigmapoly_type : ( nat  ) -> poly_type ) (taupoly_type : ( nat  ) -> poly_type ) (Eqpoly_type : forall x, sigmapoly_type x = taupoly_type x) (s : poly_type ) : subst_poly_type sigmapoly_type s = subst_poly_type taupoly_type s :=
    match s return subst_poly_type sigmapoly_type s = subst_poly_type taupoly_type s with
    | poly_var  s => Eqpoly_type s
    | poly_arr  s0 s1 => congr_poly_arr (ext_poly_type sigmapoly_type taupoly_type Eqpoly_type s0) (ext_poly_type sigmapoly_type taupoly_type Eqpoly_type s1)
    | poly_abs  s0 => congr_poly_abs (ext_poly_type (up_poly_type_poly_type sigmapoly_type) (up_poly_type_poly_type taupoly_type) (upExt_poly_type_poly_type (_) (_) Eqpoly_type) s0)
    end.

Definition up_ren_ren_poly_type_poly_type    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> nat ) (theta : ( nat  ) -> nat ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (upRen_poly_type_poly_type tau) (upRen_poly_type_poly_type xi)) x = (upRen_poly_type_poly_type theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_poly_type    (xipoly_type : ( nat  ) -> nat ) (zetapoly_type : ( nat  ) -> nat ) (rhopoly_type : ( nat  ) -> nat ) (Eqpoly_type : forall x, (funcomp zetapoly_type xipoly_type) x = rhopoly_type x) (s : poly_type ) : ren_poly_type zetapoly_type (ren_poly_type xipoly_type s) = ren_poly_type rhopoly_type s :=
    match s return ren_poly_type zetapoly_type (ren_poly_type xipoly_type s) = ren_poly_type rhopoly_type s with
    | poly_var  s => ap (poly_var ) (Eqpoly_type s)
    | poly_arr  s0 s1 => congr_poly_arr (compRenRen_poly_type xipoly_type zetapoly_type rhopoly_type Eqpoly_type s0) (compRenRen_poly_type xipoly_type zetapoly_type rhopoly_type Eqpoly_type s1)
    | poly_abs  s0 => congr_poly_abs (compRenRen_poly_type (upRen_poly_type_poly_type xipoly_type) (upRen_poly_type_poly_type zetapoly_type) (upRen_poly_type_poly_type rhopoly_type) (up_ren_ren_poly_type_poly_type (_) (_) (_) Eqpoly_type) s0)
    end.

Definition up_ren_subst_poly_type_poly_type    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> poly_type ) (theta : ( nat  ) -> poly_type ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_poly_type_poly_type tau) (upRen_poly_type_poly_type xi)) x = (up_poly_type_poly_type theta) x :=
  fun n => match n with
  | S n => ap (ren_poly_type shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint compRenSubst_poly_type    (xipoly_type : ( nat  ) -> nat ) (taupoly_type : ( nat  ) -> poly_type ) (thetapoly_type : ( nat  ) -> poly_type ) (Eqpoly_type : forall x, (funcomp taupoly_type xipoly_type) x = thetapoly_type x) (s : poly_type ) : subst_poly_type taupoly_type (ren_poly_type xipoly_type s) = subst_poly_type thetapoly_type s :=
    match s return subst_poly_type taupoly_type (ren_poly_type xipoly_type s) = subst_poly_type thetapoly_type s with
    | poly_var  s => Eqpoly_type s
    | poly_arr  s0 s1 => congr_poly_arr (compRenSubst_poly_type xipoly_type taupoly_type thetapoly_type Eqpoly_type s0) (compRenSubst_poly_type xipoly_type taupoly_type thetapoly_type Eqpoly_type s1)
    | poly_abs  s0 => congr_poly_abs (compRenSubst_poly_type (upRen_poly_type_poly_type xipoly_type) (up_poly_type_poly_type taupoly_type) (up_poly_type_poly_type thetapoly_type) (up_ren_subst_poly_type_poly_type (_) (_) (_) Eqpoly_type) s0)
    end.

Definition up_subst_ren_poly_type_poly_type    (sigma : ( nat  ) -> poly_type ) (zetapoly_type : ( nat  ) -> nat ) (theta : ( nat  ) -> poly_type ) (Eq : forall x, (funcomp (ren_poly_type zetapoly_type) sigma) x = theta x) : forall x, (funcomp (ren_poly_type (upRen_poly_type_poly_type zetapoly_type)) (up_poly_type_poly_type sigma)) x = (up_poly_type_poly_type theta) x :=
  fun n => match n with
  | S n => eq_trans (compRenRen_poly_type shift (upRen_poly_type_poly_type zetapoly_type) (funcomp shift zetapoly_type) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_poly_type zetapoly_type shift (funcomp shift zetapoly_type) (fun x => eq_refl) (sigma n))) (ap (ren_poly_type shift) (Eq n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstRen_poly_type    (sigmapoly_type : ( nat  ) -> poly_type ) (zetapoly_type : ( nat  ) -> nat ) (thetapoly_type : ( nat  ) -> poly_type ) (Eqpoly_type : forall x, (funcomp (ren_poly_type zetapoly_type) sigmapoly_type) x = thetapoly_type x) (s : poly_type ) : ren_poly_type zetapoly_type (subst_poly_type sigmapoly_type s) = subst_poly_type thetapoly_type s :=
    match s return ren_poly_type zetapoly_type (subst_poly_type sigmapoly_type s) = subst_poly_type thetapoly_type s with
    | poly_var  s => Eqpoly_type s
    | poly_arr  s0 s1 => congr_poly_arr (compSubstRen_poly_type sigmapoly_type zetapoly_type thetapoly_type Eqpoly_type s0) (compSubstRen_poly_type sigmapoly_type zetapoly_type thetapoly_type Eqpoly_type s1)
    | poly_abs  s0 => congr_poly_abs (compSubstRen_poly_type (up_poly_type_poly_type sigmapoly_type) (upRen_poly_type_poly_type zetapoly_type) (up_poly_type_poly_type thetapoly_type) (up_subst_ren_poly_type_poly_type (_) (_) (_) Eqpoly_type) s0)
    end.

Definition up_subst_subst_poly_type_poly_type    (sigma : ( nat  ) -> poly_type ) (taupoly_type : ( nat  ) -> poly_type ) (theta : ( nat  ) -> poly_type ) (Eq : forall x, (funcomp (subst_poly_type taupoly_type) sigma) x = theta x) : forall x, (funcomp (subst_poly_type (up_poly_type_poly_type taupoly_type)) (up_poly_type_poly_type sigma)) x = (up_poly_type_poly_type theta) x :=
  fun n => match n with
  | S n => eq_trans (compRenSubst_poly_type shift (up_poly_type_poly_type taupoly_type) (funcomp (up_poly_type_poly_type taupoly_type) shift) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen_poly_type taupoly_type shift (funcomp (ren_poly_type shift) taupoly_type) (fun x => eq_refl) (sigma n))) (ap (ren_poly_type shift) (Eq n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstSubst_poly_type    (sigmapoly_type : ( nat  ) -> poly_type ) (taupoly_type : ( nat  ) -> poly_type ) (thetapoly_type : ( nat  ) -> poly_type ) (Eqpoly_type : forall x, (funcomp (subst_poly_type taupoly_type) sigmapoly_type) x = thetapoly_type x) (s : poly_type ) : subst_poly_type taupoly_type (subst_poly_type sigmapoly_type s) = subst_poly_type thetapoly_type s :=
    match s return subst_poly_type taupoly_type (subst_poly_type sigmapoly_type s) = subst_poly_type thetapoly_type s with
    | poly_var  s => Eqpoly_type s
    | poly_arr  s0 s1 => congr_poly_arr (compSubstSubst_poly_type sigmapoly_type taupoly_type thetapoly_type Eqpoly_type s0) (compSubstSubst_poly_type sigmapoly_type taupoly_type thetapoly_type Eqpoly_type s1)
    | poly_abs  s0 => congr_poly_abs (compSubstSubst_poly_type (up_poly_type_poly_type sigmapoly_type) (up_poly_type_poly_type taupoly_type) (up_poly_type_poly_type thetapoly_type) (up_subst_subst_poly_type_poly_type (_) (_) (_) Eqpoly_type) s0)
    end.

Definition rinstInst_up_poly_type_poly_type   (xi : ( nat  ) -> nat ) (sigma : ( nat  ) -> poly_type ) (Eq : forall x, (funcomp (poly_var ) xi) x = sigma x) : forall x, (funcomp (poly_var ) (upRen_poly_type_poly_type xi)) x = (up_poly_type_poly_type sigma) x :=
  fun n => match n with
  | S n => ap (ren_poly_type shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint rinst_inst_poly_type   (xipoly_type : ( nat  ) -> nat ) (sigmapoly_type : ( nat  ) -> poly_type ) (Eqpoly_type : forall x, (funcomp (poly_var ) xipoly_type) x = sigmapoly_type x) (s : poly_type ) : ren_poly_type xipoly_type s = subst_poly_type sigmapoly_type s :=
    match s return ren_poly_type xipoly_type s = subst_poly_type sigmapoly_type s with
    | poly_var  s => Eqpoly_type s
    | poly_arr  s0 s1 => congr_poly_arr (rinst_inst_poly_type xipoly_type sigmapoly_type Eqpoly_type s0) (rinst_inst_poly_type xipoly_type sigmapoly_type Eqpoly_type s1)
    | poly_abs  s0 => congr_poly_abs (rinst_inst_poly_type (upRen_poly_type_poly_type xipoly_type) (up_poly_type_poly_type sigmapoly_type) (rinstInst_up_poly_type_poly_type (_) (_) Eqpoly_type) s0)
    end.

Lemma rinstInst_poly_type   (xipoly_type : ( nat  ) -> nat ) : ren_poly_type xipoly_type === subst_poly_type (funcomp (poly_var ) xipoly_type) .
Proof. exact ((fun x => rinst_inst_poly_type xipoly_type (_) (fun n => eq_refl) x)). Qed.

Lemma instId_poly_type  : subst_poly_type (poly_var ) === id .
Proof. exact ((fun x => idSubst_poly_type (poly_var ) (fun n => eq_refl) (id x))). Qed.

Lemma rinstId_poly_type  : @ren_poly_type   id === id .
Proof. exact (feq_trans (rinstInst_poly_type id) instId_poly_type). Qed.

Lemma varL_poly_type   (sigmapoly_type : ( nat  ) -> poly_type ) : funcomp (subst_poly_type sigmapoly_type) (poly_var ) === sigmapoly_type .
Proof. exact ((fun x => eq_refl)). Qed.

Lemma varLRen_poly_type   (xipoly_type : ( nat  ) -> nat ) : funcomp (ren_poly_type xipoly_type) (poly_var ) === funcomp (poly_var ) xipoly_type .
Proof. exact ((fun x => eq_refl)). Qed.

Lemma compComp_poly_type    (sigmapoly_type : ( nat  ) -> poly_type ) (taupoly_type : ( nat  ) -> poly_type ) (s : poly_type ) : subst_poly_type taupoly_type (subst_poly_type sigmapoly_type s) = subst_poly_type (funcomp (subst_poly_type taupoly_type) sigmapoly_type) s .
Proof. exact (compSubstSubst_poly_type sigmapoly_type taupoly_type (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_poly_type    (sigmapoly_type : ( nat  ) -> poly_type ) (taupoly_type : ( nat  ) -> poly_type ) : funcomp (subst_poly_type taupoly_type) (subst_poly_type sigmapoly_type) === subst_poly_type (funcomp (subst_poly_type taupoly_type) sigmapoly_type) .
Proof. exact ((fun n => compComp_poly_type sigmapoly_type taupoly_type n)). Qed.

Lemma compRen_poly_type    (sigmapoly_type : ( nat  ) -> poly_type ) (zetapoly_type : ( nat  ) -> nat ) (s : poly_type ) : ren_poly_type zetapoly_type (subst_poly_type sigmapoly_type s) = subst_poly_type (funcomp (ren_poly_type zetapoly_type) sigmapoly_type) s .
Proof. exact (compSubstRen_poly_type sigmapoly_type zetapoly_type (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_poly_type    (sigmapoly_type : ( nat  ) -> poly_type ) (zetapoly_type : ( nat  ) -> nat ) : funcomp (ren_poly_type zetapoly_type) (subst_poly_type sigmapoly_type) === subst_poly_type (funcomp (ren_poly_type zetapoly_type) sigmapoly_type) .
Proof. exact ((fun n => compRen_poly_type sigmapoly_type zetapoly_type n)). Qed.

Lemma renComp_poly_type    (xipoly_type : ( nat  ) -> nat ) (taupoly_type : ( nat  ) -> poly_type ) (s : poly_type ) : subst_poly_type taupoly_type (ren_poly_type xipoly_type s) = subst_poly_type (funcomp taupoly_type xipoly_type) s .
Proof. exact (compRenSubst_poly_type xipoly_type taupoly_type (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_poly_type    (xipoly_type : ( nat  ) -> nat ) (taupoly_type : ( nat  ) -> poly_type ) : funcomp (subst_poly_type taupoly_type) (ren_poly_type xipoly_type) === subst_poly_type (funcomp taupoly_type xipoly_type) .
Proof. exact ((fun n => renComp_poly_type xipoly_type taupoly_type n)). Qed.

Lemma renRen_poly_type    (xipoly_type : ( nat  ) -> nat ) (zetapoly_type : ( nat  ) -> nat ) (s : poly_type ) : ren_poly_type zetapoly_type (ren_poly_type xipoly_type s) = ren_poly_type (funcomp zetapoly_type xipoly_type) s .
Proof. exact (compRenRen_poly_type xipoly_type zetapoly_type (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_poly_type    (xipoly_type : ( nat  ) -> nat ) (zetapoly_type : ( nat  ) -> nat ) : funcomp (ren_poly_type zetapoly_type) (ren_poly_type xipoly_type) === ren_poly_type (funcomp zetapoly_type xipoly_type) .
Proof. exact ((fun n => renRen_poly_type xipoly_type zetapoly_type n)). Qed.

End poly_type.

Section term.

(** system F terms P, Q, .. *)
Inductive term : Type :=
  | var : nat -> term  
  | app : term -> term -> term  
  | abs : poly_type -> term -> term  
  | ty_app : term -> poly_type -> term  
  | ty_abs : term -> term.

Lemma congr_app  { s0 : term    } { s1 : term    } { t0 : term    } { t1 : term    } : ( s0 = t0 ) -> ( s1 = t1 ) -> app   s0 s1 = app   t0 t1 .
Proof. congruence. Qed.

Lemma congr_abs  { s0 : poly_type   } { s1 : term    } { t0 : poly_type   } { t1 : term    } : ( s0 = t0 ) -> ( s1 = t1 ) -> abs   s0 s1 = abs   t0 t1 .
Proof. congruence. Qed.

Lemma congr_ty_app  { s0 : term    } { s1 : poly_type   } { t0 : term    } { t1 : poly_type   } : ( s0 = t0 ) -> ( s1 = t1 ) -> ty_app   s0 s1 = ty_app   t0 t1 .
Proof. congruence. Qed.

Lemma congr_ty_abs  { s0 : term    } { t0 : term    } : ( s0 = t0 ) -> ty_abs   s0 = ty_abs   t0 .
Proof. congruence. Qed.

Definition upRen_poly_type_term   (xi : ( nat  ) -> nat ) : ( nat  ) -> nat  :=
  xi.

Definition upRen_term_poly_type   (xi : ( nat  ) -> nat ) : ( nat  ) -> nat  :=
  xi.

Definition upRen_term_term   (xi : ( nat  ) -> nat ) : ( nat  ) -> nat  :=
  up_ren xi.

Fixpoint ren_term   (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (s : term  ) : term   :=
    match s return term   with
    | var   s => (var  ) (xiterm s)
    | app   s0 s1 => app   (ren_term xipoly_type xiterm s0) (ren_term xipoly_type xiterm s1)
    | abs   s0 s1 => abs   (ren_poly_type xipoly_type s0) (ren_term (upRen_term_poly_type xipoly_type) (upRen_term_term xiterm) s1)
    | ty_app   s0 s1 => ty_app   (ren_term xipoly_type xiterm s0) (ren_poly_type xipoly_type s1)
    | ty_abs   s0 => ty_abs   (ren_term (upRen_poly_type_poly_type xipoly_type) (upRen_poly_type_term xiterm) s0)
    end.

Definition up_poly_type_term   (sigma : ( nat  ) -> term  ) : ( nat  ) -> term  :=
  funcomp (ren_term shift id) sigma.

Definition up_term_poly_type   (sigma : ( nat  ) -> poly_type ) : ( nat  ) -> poly_type  :=
  funcomp (ren_poly_type id) sigma.

Definition up_term_term   (sigma : ( nat  ) -> term  ) : ( nat  ) -> term   :=
  scons ((var  ) var_zero) (funcomp (ren_term id shift) sigma).

Fixpoint subst_term   (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (s : term  ) : term   :=
    match s return term   with
    | var   s => sigmaterm s
    | app   s0 s1 => app   (subst_term sigmapoly_type sigmaterm s0) (subst_term sigmapoly_type sigmaterm s1)
    | abs   s0 s1 => abs   (subst_poly_type sigmapoly_type s0) (subst_term (up_term_poly_type sigmapoly_type) (up_term_term sigmaterm) s1)
    | ty_app   s0 s1 => ty_app   (subst_term sigmapoly_type sigmaterm s0) (subst_poly_type sigmapoly_type s1)
    | ty_abs   s0 => ty_abs   (subst_term (up_poly_type_poly_type sigmapoly_type) (up_poly_type_term sigmaterm) s0)
    end.

Definition upId_poly_type_term  (sigma : ( nat  ) -> term  ) (Eq : forall x, sigma x = (var  ) x) : forall x, (up_poly_type_term sigma) x = (var  ) x :=
  fun n => ap (ren_term shift id) (Eq n).

Definition upId_term_poly_type  (sigma : ( nat  ) -> poly_type ) (Eq : forall x, sigma x = (poly_var ) x) : forall x, (up_term_poly_type sigma) x = (poly_var ) x :=
  fun n => ap (ren_poly_type id) (Eq n).

Definition upId_term_term  (sigma : ( nat  ) -> term  ) (Eq : forall x, sigma x = (var  ) x) : forall x, (up_term_term sigma) x = (var  ) x :=
  fun n => match n with
  | S n => ap (ren_term id shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint idSubst_term  (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (Eqpoly_type : forall x, sigmapoly_type x = (poly_var ) x) (Eqterm : forall x, sigmaterm x = (var  ) x) (s : term  ) : subst_term sigmapoly_type sigmaterm s = s :=
    match s return subst_term sigmapoly_type sigmaterm s = s with
    | var   s => Eqterm s
    | app   s0 s1 => congr_app (idSubst_term sigmapoly_type sigmaterm Eqpoly_type Eqterm s0) (idSubst_term sigmapoly_type sigmaterm Eqpoly_type Eqterm s1)
    | abs   s0 s1 => congr_abs (idSubst_poly_type sigmapoly_type Eqpoly_type s0) (idSubst_term (up_term_poly_type sigmapoly_type) (up_term_term sigmaterm) (upId_term_poly_type (_) Eqpoly_type) (upId_term_term (_) Eqterm) s1)
    | ty_app   s0 s1 => congr_ty_app (idSubst_term sigmapoly_type sigmaterm Eqpoly_type Eqterm s0) (idSubst_poly_type sigmapoly_type Eqpoly_type s1)
    | ty_abs   s0 => congr_ty_abs (idSubst_term (up_poly_type_poly_type sigmapoly_type) (up_poly_type_term sigmaterm) (upId_poly_type_poly_type (_) Eqpoly_type) (upId_poly_type_term (_) Eqterm) s0)
    end.

Definition upExtRen_poly_type_term   (xi : ( nat  ) -> nat ) (zeta : ( nat  ) -> nat ) (Eq : forall x, xi x = zeta x) : forall x, (upRen_poly_type_term xi) x = (upRen_poly_type_term zeta) x :=
  fun n => Eq n.

Definition upExtRen_term_poly_type   (xi : ( nat  ) -> nat ) (zeta : ( nat  ) -> nat ) (Eq : forall x, xi x = zeta x) : forall x, (upRen_term_poly_type xi) x = (upRen_term_poly_type zeta) x :=
  fun n => Eq n.

Definition upExtRen_term_term   (xi : ( nat  ) -> nat ) (zeta : ( nat  ) -> nat ) (Eq : forall x, xi x = zeta x) : forall x, (upRen_term_term xi) x = (upRen_term_term zeta) x :=
  fun n => match n with
  | S n => ap shift (Eq n)
  | 0 => eq_refl
  end.

Fixpoint extRen_term   (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) (Eqpoly_type : forall x, xipoly_type x = zetapoly_type x) (Eqterm : forall x, xiterm x = zetaterm x) (s : term  ) : ren_term xipoly_type xiterm s = ren_term zetapoly_type zetaterm s :=
    match s return ren_term xipoly_type xiterm s = ren_term zetapoly_type zetaterm s with
    | var   s => ap (var  ) (Eqterm s)
    | app   s0 s1 => congr_app (extRen_term xipoly_type xiterm zetapoly_type zetaterm Eqpoly_type Eqterm s0) (extRen_term xipoly_type xiterm zetapoly_type zetaterm Eqpoly_type Eqterm s1)
    | abs   s0 s1 => congr_abs (extRen_poly_type xipoly_type zetapoly_type Eqpoly_type s0) (extRen_term (upRen_term_poly_type xipoly_type) (upRen_term_term xiterm) (upRen_term_poly_type zetapoly_type) (upRen_term_term zetaterm) (upExtRen_term_poly_type (_) (_) Eqpoly_type) (upExtRen_term_term (_) (_) Eqterm) s1)
    | ty_app   s0 s1 => congr_ty_app (extRen_term xipoly_type xiterm zetapoly_type zetaterm Eqpoly_type Eqterm s0) (extRen_poly_type xipoly_type zetapoly_type Eqpoly_type s1)
    | ty_abs   s0 => congr_ty_abs (extRen_term (upRen_poly_type_poly_type xipoly_type) (upRen_poly_type_term xiterm) (upRen_poly_type_poly_type zetapoly_type) (upRen_poly_type_term zetaterm) (upExtRen_poly_type_poly_type (_) (_) Eqpoly_type) (upExtRen_poly_type_term (_) (_) Eqterm) s0)
    end.

Definition upExt_poly_type_term   (sigma : ( nat  ) -> term  ) (tau : ( nat  ) -> term  ) (Eq : forall x, sigma x = tau x) : forall x, (up_poly_type_term sigma) x = (up_poly_type_term tau) x :=
  fun n => ap (ren_term shift id) (Eq n).

Definition upExt_term_poly_type   (sigma : ( nat  ) -> poly_type ) (tau : ( nat  ) -> poly_type ) (Eq : forall x, sigma x = tau x) : forall x, (up_term_poly_type sigma) x = (up_term_poly_type tau) x :=
  fun n => ap (ren_poly_type id) (Eq n).

Definition upExt_term_term   (sigma : ( nat  ) -> term  ) (tau : ( nat  ) -> term  ) (Eq : forall x, sigma x = tau x) : forall x, (up_term_term sigma) x = (up_term_term tau) x :=
  fun n => match n with
  | S n => ap (ren_term id shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint ext_term   (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) (Eqpoly_type : forall x, sigmapoly_type x = taupoly_type x) (Eqterm : forall x, sigmaterm x = tauterm x) (s : term  ) : subst_term sigmapoly_type sigmaterm s = subst_term taupoly_type tauterm s :=
    match s return subst_term sigmapoly_type sigmaterm s = subst_term taupoly_type tauterm s with
    | var   s => Eqterm s
    | app   s0 s1 => congr_app (ext_term sigmapoly_type sigmaterm taupoly_type tauterm Eqpoly_type Eqterm s0) (ext_term sigmapoly_type sigmaterm taupoly_type tauterm Eqpoly_type Eqterm s1)
    | abs   s0 s1 => congr_abs (ext_poly_type sigmapoly_type taupoly_type Eqpoly_type s0) (ext_term (up_term_poly_type sigmapoly_type) (up_term_term sigmaterm) (up_term_poly_type taupoly_type) (up_term_term tauterm) (upExt_term_poly_type (_) (_) Eqpoly_type) (upExt_term_term (_) (_) Eqterm) s1)
    | ty_app   s0 s1 => congr_ty_app (ext_term sigmapoly_type sigmaterm taupoly_type tauterm Eqpoly_type Eqterm s0) (ext_poly_type sigmapoly_type taupoly_type Eqpoly_type s1)
    | ty_abs   s0 => congr_ty_abs (ext_term (up_poly_type_poly_type sigmapoly_type) (up_poly_type_term sigmaterm) (up_poly_type_poly_type taupoly_type) (up_poly_type_term tauterm) (upExt_poly_type_poly_type (_) (_) Eqpoly_type) (upExt_poly_type_term (_) (_) Eqterm) s0)
    end.

Definition up_ren_ren_poly_type_term    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> nat ) (theta : ( nat  ) -> nat ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (upRen_poly_type_term tau) (upRen_poly_type_term xi)) x = (upRen_poly_type_term theta) x.
Proof.
  intros. eapply Eq. 
Qed.

Definition up_ren_ren_term_poly_type    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> nat ) (theta : ( nat  ) -> nat ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (upRen_term_poly_type tau) (upRen_term_poly_type xi)) x = (upRen_term_poly_type theta) x.
Proof.
  intros. eapply Eq.
Qed.  

Definition up_ren_ren_term_term    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> nat ) (theta : ( nat  ) -> nat ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (upRen_term_term tau) (upRen_term_term xi)) x = (upRen_term_term theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_term    (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) (rhopoly_type : ( nat  ) -> nat ) (rhoterm : ( nat  ) -> nat ) (Eqpoly_type : forall x, (funcomp zetapoly_type xipoly_type) x = rhopoly_type x) (Eqterm : forall x, (funcomp zetaterm xiterm) x = rhoterm x) (s : term  ) : ren_term zetapoly_type zetaterm (ren_term xipoly_type xiterm s) = ren_term rhopoly_type rhoterm s :=
    match s return ren_term zetapoly_type zetaterm (ren_term xipoly_type xiterm s) = ren_term rhopoly_type rhoterm s with
    | var   s => ap (var  ) (Eqterm s)
    | app   s0 s1 => congr_app (compRenRen_term xipoly_type xiterm zetapoly_type zetaterm rhopoly_type rhoterm Eqpoly_type Eqterm s0) (compRenRen_term xipoly_type xiterm zetapoly_type zetaterm rhopoly_type rhoterm Eqpoly_type Eqterm s1)
    | abs   s0 s1 => congr_abs (compRenRen_poly_type xipoly_type zetapoly_type rhopoly_type Eqpoly_type s0) (compRenRen_term (upRen_term_poly_type xipoly_type) (upRen_term_term xiterm) (upRen_term_poly_type zetapoly_type) (upRen_term_term zetaterm) (upRen_term_poly_type rhopoly_type) (upRen_term_term rhoterm) Eqpoly_type (up_ren_ren_term_term (_) (_) (_) Eqterm) s1)
    | ty_app   s0 s1 => congr_ty_app (compRenRen_term xipoly_type xiterm zetapoly_type zetaterm rhopoly_type rhoterm Eqpoly_type Eqterm s0) (compRenRen_poly_type xipoly_type zetapoly_type rhopoly_type Eqpoly_type s1)
    | ty_abs   s0 => congr_ty_abs (compRenRen_term (upRen_poly_type_poly_type xipoly_type) (upRen_poly_type_term xiterm) (upRen_poly_type_poly_type zetapoly_type) (upRen_poly_type_term zetaterm) (upRen_poly_type_poly_type rhopoly_type) (upRen_poly_type_term rhoterm) (up_ren_ren_poly_type_poly_type (_) (_) (_) Eqpoly_type) Eqterm s0)
    end.

Definition up_ren_subst_poly_type_term    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> term  ) (theta : ( nat  ) -> term  ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_poly_type_term tau) (upRen_poly_type_term xi)) x = (up_poly_type_term theta) x :=
  fun n => ap (ren_term shift id) (Eq n).

Definition up_ren_subst_term_poly_type    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> poly_type ) (theta : ( nat  ) -> poly_type ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_term_poly_type tau) (upRen_term_poly_type xi)) x = (up_term_poly_type theta) x :=
  fun n => ap (ren_poly_type id) (Eq n).

Definition up_ren_subst_term_term    (xi : ( nat  ) -> nat ) (tau : ( nat  ) -> term  ) (theta : ( nat  ) -> term  ) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_term_term tau) (upRen_term_term xi)) x = (up_term_term theta) x :=
  fun n => match n with
  | S n => ap (ren_term id shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint compRenSubst_term    (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) (thetapoly_type : ( nat  ) -> poly_type ) (thetaterm : ( nat  ) -> term  ) (Eqpoly_type : forall x, (funcomp taupoly_type xipoly_type) x = thetapoly_type x) (Eqterm : forall x, (funcomp tauterm xiterm) x = thetaterm x) (s : term  ) : subst_term taupoly_type tauterm (ren_term xipoly_type xiterm s) = subst_term thetapoly_type thetaterm s :=
    match s return subst_term taupoly_type tauterm (ren_term xipoly_type xiterm s) = subst_term thetapoly_type thetaterm s with
    | var   s => Eqterm s
    | app   s0 s1 => congr_app (compRenSubst_term xipoly_type xiterm taupoly_type tauterm thetapoly_type thetaterm Eqpoly_type Eqterm s0) (compRenSubst_term xipoly_type xiterm taupoly_type tauterm thetapoly_type thetaterm Eqpoly_type Eqterm s1)
    | abs   s0 s1 => congr_abs (compRenSubst_poly_type xipoly_type taupoly_type thetapoly_type Eqpoly_type s0) (compRenSubst_term (upRen_term_poly_type xipoly_type) (upRen_term_term xiterm) (up_term_poly_type taupoly_type) (up_term_term tauterm) (up_term_poly_type thetapoly_type) (up_term_term thetaterm) (up_ren_subst_term_poly_type (_) (_) (_) Eqpoly_type) (up_ren_subst_term_term (_) (_) (_) Eqterm) s1)
    | ty_app   s0 s1 => congr_ty_app (compRenSubst_term xipoly_type xiterm taupoly_type tauterm thetapoly_type thetaterm Eqpoly_type Eqterm s0) (compRenSubst_poly_type xipoly_type taupoly_type thetapoly_type Eqpoly_type s1)
    | ty_abs   s0 => congr_ty_abs (compRenSubst_term (upRen_poly_type_poly_type xipoly_type) (upRen_poly_type_term xiterm) (up_poly_type_poly_type taupoly_type) (up_poly_type_term tauterm) (up_poly_type_poly_type thetapoly_type) (up_poly_type_term thetaterm) (up_ren_subst_poly_type_poly_type (_) (_) (_) Eqpoly_type) (up_ren_subst_poly_type_term (_) (_) (_) Eqterm) s0)
    end.

Definition up_subst_ren_poly_type_term    (sigma : ( nat  ) -> term  ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) (theta : ( nat  ) -> term  ) (Eq : forall x, (funcomp (ren_term zetapoly_type zetaterm) sigma) x = theta x) : forall x, (funcomp (ren_term (upRen_poly_type_poly_type zetapoly_type) (upRen_poly_type_term zetaterm)) (up_poly_type_term sigma)) x = (up_poly_type_term theta) x :=
  fun n => eq_trans (compRenRen_term shift id (upRen_poly_type_poly_type zetapoly_type) (upRen_poly_type_term zetaterm) (funcomp shift zetapoly_type) (funcomp id zetaterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_term zetapoly_type zetaterm shift id (funcomp shift zetapoly_type) (funcomp id zetaterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) (ap (ren_term shift id) (Eq n))).

Definition up_subst_ren_term_poly_type    (sigma : ( nat  ) -> poly_type ) (zetapoly_type : ( nat  ) -> nat ) (theta : ( nat  ) -> poly_type ) (Eq : forall x, (funcomp (ren_poly_type zetapoly_type) sigma) x = theta x) : forall x, (funcomp (ren_poly_type (upRen_term_poly_type zetapoly_type)) (up_term_poly_type sigma)) x = (up_term_poly_type theta) x :=
  fun n => eq_trans (compRenRen_poly_type id (upRen_term_poly_type zetapoly_type) (funcomp id zetapoly_type) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_poly_type zetapoly_type id (funcomp id zetapoly_type) (fun x => eq_refl) (sigma n))) (ap (ren_poly_type id) (Eq n))).

Definition up_subst_ren_term_term    (sigma : ( nat  ) -> term  ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) (theta : ( nat  ) -> term  ) (Eq : forall x, (funcomp (ren_term zetapoly_type zetaterm) sigma) x = theta x) : forall x, (funcomp (ren_term (upRen_term_poly_type zetapoly_type) (upRen_term_term zetaterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S n => eq_trans (compRenRen_term id shift (upRen_term_poly_type zetapoly_type) (upRen_term_term zetaterm) (funcomp id zetapoly_type) (funcomp shift zetaterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_term zetapoly_type zetaterm id shift (funcomp id zetapoly_type) (funcomp shift zetaterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) (ap (ren_term id shift) (Eq n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstRen_term    (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) (thetapoly_type : ( nat  ) -> poly_type ) (thetaterm : ( nat  ) -> term  ) (Eqpoly_type : forall x, (funcomp (ren_poly_type zetapoly_type) sigmapoly_type) x = thetapoly_type x) (Eqterm : forall x, (funcomp (ren_term zetapoly_type zetaterm) sigmaterm) x = thetaterm x) (s : term  ) : ren_term zetapoly_type zetaterm (subst_term sigmapoly_type sigmaterm s) = subst_term thetapoly_type thetaterm s :=
    match s return ren_term zetapoly_type zetaterm (subst_term sigmapoly_type sigmaterm s) = subst_term thetapoly_type thetaterm s with
    | var   s => Eqterm s
    | app   s0 s1 => congr_app (compSubstRen_term sigmapoly_type sigmaterm zetapoly_type zetaterm thetapoly_type thetaterm Eqpoly_type Eqterm s0) (compSubstRen_term sigmapoly_type sigmaterm zetapoly_type zetaterm thetapoly_type thetaterm Eqpoly_type Eqterm s1)
    | abs   s0 s1 => congr_abs (compSubstRen_poly_type sigmapoly_type zetapoly_type thetapoly_type Eqpoly_type s0) (compSubstRen_term (up_term_poly_type sigmapoly_type) (up_term_term sigmaterm) (upRen_term_poly_type zetapoly_type) (upRen_term_term zetaterm) (up_term_poly_type thetapoly_type) (up_term_term thetaterm) (up_subst_ren_term_poly_type (_) (_) (_) Eqpoly_type) (up_subst_ren_term_term (_) (_) (_) (_) Eqterm) s1)
    | ty_app   s0 s1 => congr_ty_app (compSubstRen_term sigmapoly_type sigmaterm zetapoly_type zetaterm thetapoly_type thetaterm Eqpoly_type Eqterm s0) (compSubstRen_poly_type sigmapoly_type zetapoly_type thetapoly_type Eqpoly_type s1)
    | ty_abs   s0 => congr_ty_abs (compSubstRen_term (up_poly_type_poly_type sigmapoly_type) (up_poly_type_term sigmaterm) (upRen_poly_type_poly_type zetapoly_type) (upRen_poly_type_term zetaterm) (up_poly_type_poly_type thetapoly_type) (up_poly_type_term thetaterm) (up_subst_ren_poly_type_poly_type (_) (_) (_) Eqpoly_type) (up_subst_ren_poly_type_term (_) (_) (_) (_) Eqterm) s0)
    end.

Definition up_subst_subst_poly_type_term    (sigma : ( nat  ) -> term  ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) (theta : ( nat  ) -> term  ) (Eq : forall x, (funcomp (subst_term taupoly_type tauterm) sigma) x = theta x) : forall x, (funcomp (subst_term (up_poly_type_poly_type taupoly_type) (up_poly_type_term tauterm)) (up_poly_type_term sigma)) x = (up_poly_type_term theta) x :=
  fun n => eq_trans (compRenSubst_term shift id (up_poly_type_poly_type taupoly_type) (up_poly_type_term tauterm) (funcomp (up_poly_type_poly_type taupoly_type) shift) (funcomp (up_poly_type_term tauterm) id) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen_term taupoly_type tauterm shift id (funcomp (ren_poly_type shift) taupoly_type) (funcomp (ren_term shift id) tauterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) (ap (ren_term shift id) (Eq n))).

Definition up_subst_subst_term_poly_type    (sigma : ( nat  ) -> poly_type ) (taupoly_type : ( nat  ) -> poly_type ) (theta : ( nat  ) -> poly_type ) (Eq : forall x, (funcomp (subst_poly_type taupoly_type) sigma) x = theta x) : forall x, (funcomp (subst_poly_type (up_term_poly_type taupoly_type)) (up_term_poly_type sigma)) x = (up_term_poly_type theta) x :=
  fun n => eq_trans (compRenSubst_poly_type id (up_term_poly_type taupoly_type) (funcomp (up_term_poly_type taupoly_type) id) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen_poly_type taupoly_type id (funcomp (ren_poly_type id) taupoly_type) (fun x => eq_refl) (sigma n))) (ap (ren_poly_type id) (Eq n))).

Definition up_subst_subst_term_term    (sigma : ( nat  ) -> term  ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) (theta : ( nat  ) -> term  ) (Eq : forall x, (funcomp (subst_term taupoly_type tauterm) sigma) x = theta x) : forall x, (funcomp (subst_term (up_term_poly_type taupoly_type) (up_term_term tauterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S n => eq_trans (compRenSubst_term id shift (up_term_poly_type taupoly_type) (up_term_term tauterm) (funcomp (up_term_poly_type taupoly_type) id) (funcomp (up_term_term tauterm) shift) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen_term taupoly_type tauterm id shift (funcomp (ren_poly_type id) taupoly_type) (funcomp (ren_term id shift) tauterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) (ap (ren_term id shift) (Eq n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstSubst_term    (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) (thetapoly_type : ( nat  ) -> poly_type ) (thetaterm : ( nat  ) -> term  ) (Eqpoly_type : forall x, (funcomp (subst_poly_type taupoly_type) sigmapoly_type) x = thetapoly_type x) (Eqterm : forall x, (funcomp (subst_term taupoly_type tauterm) sigmaterm) x = thetaterm x) (s : term  ) : subst_term taupoly_type tauterm (subst_term sigmapoly_type sigmaterm s) = subst_term thetapoly_type thetaterm s :=
    match s return subst_term taupoly_type tauterm (subst_term sigmapoly_type sigmaterm s) = subst_term thetapoly_type thetaterm s with
    | var   s => Eqterm s
    | app   s0 s1 => congr_app (compSubstSubst_term sigmapoly_type sigmaterm taupoly_type tauterm thetapoly_type thetaterm Eqpoly_type Eqterm s0) (compSubstSubst_term sigmapoly_type sigmaterm taupoly_type tauterm thetapoly_type thetaterm Eqpoly_type Eqterm s1)
    | abs   s0 s1 => congr_abs (compSubstSubst_poly_type sigmapoly_type taupoly_type thetapoly_type Eqpoly_type s0) (compSubstSubst_term (up_term_poly_type sigmapoly_type) (up_term_term sigmaterm) (up_term_poly_type taupoly_type) (up_term_term tauterm) (up_term_poly_type thetapoly_type) (up_term_term thetaterm) (up_subst_subst_term_poly_type (_) (_) (_) Eqpoly_type) (up_subst_subst_term_term (_) (_) (_) (_) Eqterm) s1)
    | ty_app   s0 s1 => congr_ty_app (compSubstSubst_term sigmapoly_type sigmaterm taupoly_type tauterm thetapoly_type thetaterm Eqpoly_type Eqterm s0) (compSubstSubst_poly_type sigmapoly_type taupoly_type thetapoly_type Eqpoly_type s1)
    | ty_abs   s0 => congr_ty_abs (compSubstSubst_term (up_poly_type_poly_type sigmapoly_type) (up_poly_type_term sigmaterm) (up_poly_type_poly_type taupoly_type) (up_poly_type_term tauterm) (up_poly_type_poly_type thetapoly_type) (up_poly_type_term thetaterm) (up_subst_subst_poly_type_poly_type (_) (_) (_) Eqpoly_type) (up_subst_subst_poly_type_term (_) (_) (_) (_) Eqterm) s0)
    end.

Definition rinstInst_up_poly_type_term   (xi : ( nat  ) -> nat ) (sigma : ( nat  ) -> term  ) (Eq : forall x, (funcomp (var  ) xi) x = sigma x) : forall x, (funcomp (var  ) (upRen_poly_type_term xi)) x = (up_poly_type_term sigma) x :=
  fun n => ap (ren_term shift id) (Eq n).

Definition rinstInst_up_term_poly_type   (xi : ( nat  ) -> nat ) (sigma : ( nat  ) -> poly_type ) (Eq : forall x, (funcomp (poly_var ) xi) x = sigma x) : forall x, (funcomp (poly_var ) (upRen_term_poly_type xi)) x = (up_term_poly_type sigma) x :=
  fun n => ap (ren_poly_type id) (Eq n).

Definition rinstInst_up_term_term   (xi : ( nat  ) -> nat ) (sigma : ( nat  ) -> term  ) (Eq : forall x, (funcomp (var  ) xi) x = sigma x) : forall x, (funcomp (var  ) (upRen_term_term xi)) x = (up_term_term sigma) x :=
  fun n => match n with
  | S n => ap (ren_term id shift) (Eq n)
  | 0 => eq_refl
  end.

Fixpoint rinst_inst_term   (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (Eqpoly_type : forall x, (funcomp (poly_var ) xipoly_type) x = sigmapoly_type x) (Eqterm : forall x, (funcomp (var  ) xiterm) x = sigmaterm x) (s : term  ) : ren_term xipoly_type xiterm s = subst_term sigmapoly_type sigmaterm s :=
    match s return ren_term xipoly_type xiterm s = subst_term sigmapoly_type sigmaterm s with
    | var   s => Eqterm s
    | app   s0 s1 => congr_app (rinst_inst_term xipoly_type xiterm sigmapoly_type sigmaterm Eqpoly_type Eqterm s0) (rinst_inst_term xipoly_type xiterm sigmapoly_type sigmaterm Eqpoly_type Eqterm s1)
    | abs   s0 s1 => congr_abs (rinst_inst_poly_type xipoly_type sigmapoly_type Eqpoly_type s0) (rinst_inst_term (upRen_term_poly_type xipoly_type) (upRen_term_term xiterm) (up_term_poly_type sigmapoly_type) (up_term_term sigmaterm) (rinstInst_up_term_poly_type (_) (_) Eqpoly_type) (rinstInst_up_term_term (_) (_) Eqterm) s1)
    | ty_app   s0 s1 => congr_ty_app (rinst_inst_term xipoly_type xiterm sigmapoly_type sigmaterm Eqpoly_type Eqterm s0) (rinst_inst_poly_type xipoly_type sigmapoly_type Eqpoly_type s1)
    | ty_abs   s0 => congr_ty_abs (rinst_inst_term (upRen_poly_type_poly_type xipoly_type) (upRen_poly_type_term xiterm) (up_poly_type_poly_type sigmapoly_type) (up_poly_type_term sigmaterm) (rinstInst_up_poly_type_poly_type (_) (_) Eqpoly_type) (rinstInst_up_poly_type_term (_) (_) Eqterm) s0)
    end.

Lemma rinstInst_term   (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) : ren_term xipoly_type xiterm === subst_term (funcomp (poly_var ) xipoly_type) (funcomp (var  ) xiterm) .
Proof. exact ((fun x => rinst_inst_term xipoly_type xiterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma instId_term  : subst_term (poly_var ) (var  ) === id .
Proof. exact ((fun x => idSubst_term (poly_var ) (var  ) (fun n => eq_refl) (fun n => eq_refl) (id x))). Qed.

Lemma rinstId_term  : @ren_term     id id === id .
Proof. exact (feq_trans (rinstInst_term id id) instId_term). Qed.

Lemma varL_term   (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) : funcomp (subst_term sigmapoly_type sigmaterm) (var  ) === sigmaterm .
Proof. exact ((fun x => eq_refl)). Qed.

Lemma varLRen_term   (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) : funcomp (ren_term xipoly_type xiterm) (var  ) === funcomp (var  ) xiterm .
Proof. exact ((fun x => eq_refl)). Qed.

Lemma compComp_term    (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) (s : term  ) : subst_term taupoly_type tauterm (subst_term sigmapoly_type sigmaterm s) = subst_term (funcomp (subst_poly_type taupoly_type) sigmapoly_type) (funcomp (subst_term taupoly_type tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_term sigmapoly_type sigmaterm taupoly_type tauterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_term    (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) : funcomp (subst_term taupoly_type tauterm) (subst_term sigmapoly_type sigmaterm) === subst_term (funcomp (subst_poly_type taupoly_type) sigmapoly_type) (funcomp (subst_term taupoly_type tauterm) sigmaterm) .
Proof. exact ((fun n => compComp_term sigmapoly_type sigmaterm taupoly_type tauterm n)). Qed.

Lemma compRen_term    (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) (s : term  ) : ren_term zetapoly_type zetaterm (subst_term sigmapoly_type sigmaterm s) = subst_term (funcomp (ren_poly_type zetapoly_type) sigmapoly_type) (funcomp (ren_term zetapoly_type zetaterm) sigmaterm) s .
Proof. exact (compSubstRen_term sigmapoly_type sigmaterm zetapoly_type zetaterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen'_term    (sigmapoly_type : ( nat  ) -> poly_type ) (sigmaterm : ( nat  ) -> term  ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) : funcomp (ren_term zetapoly_type zetaterm) (subst_term sigmapoly_type sigmaterm) === subst_term (funcomp (ren_poly_type zetapoly_type) sigmapoly_type) (funcomp (ren_term zetapoly_type zetaterm) sigmaterm) .
Proof. exact ((fun n => compRen_term sigmapoly_type sigmaterm zetapoly_type zetaterm n)). Qed.

Lemma renComp_term    (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) (s : term  ) : subst_term taupoly_type tauterm (ren_term xipoly_type xiterm s) = subst_term (funcomp taupoly_type xipoly_type) (funcomp tauterm xiterm) s .
Proof. exact (compRenSubst_term xipoly_type xiterm taupoly_type tauterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp'_term    (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (taupoly_type : ( nat  ) -> poly_type ) (tauterm : ( nat  ) -> term  ) : funcomp (subst_term taupoly_type tauterm) (ren_term xipoly_type xiterm) === subst_term (funcomp taupoly_type xipoly_type) (funcomp tauterm xiterm) .
Proof. exact ((fun n => renComp_term xipoly_type xiterm taupoly_type tauterm n)). Qed.

Lemma renRen_term    (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) (s : term  ) : ren_term zetapoly_type zetaterm (ren_term xipoly_type xiterm s) = ren_term (funcomp zetapoly_type xipoly_type) (funcomp zetaterm xiterm) s .
Proof. exact (compRenRen_term xipoly_type xiterm zetapoly_type zetaterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen'_term    (xipoly_type : ( nat  ) -> nat ) (xiterm : ( nat  ) -> nat ) (zetapoly_type : ( nat  ) -> nat ) (zetaterm : ( nat  ) -> nat ) : funcomp (ren_term zetapoly_type zetaterm) (ren_term xipoly_type xiterm) === ren_term (funcomp zetapoly_type xipoly_type) (funcomp zetaterm xiterm) .
Proof. exact ((fun n => renRen_term xipoly_type xiterm zetapoly_type zetaterm n)). Qed.

End term.


Instance proper1 : Proper (fext_eq ==> fext_eq) ren_poly_type.
Proof.
  repeat intros ?. eapply extRen_poly_type. firstorder.
Qed.

Instance proper2 : Proper (fext_eq ==> fext_eq ==> fext_eq) ren_term.
Proof.
  repeat intros ?. eapply extRen_term; firstorder.
Qed.

Instance proper3 : Proper (fext_eq ==> fext_eq) subst_poly_type.
Proof.
  repeat intros ?. eapply ext_poly_type. firstorder.
Qed.

Instance proper4 : Proper (fext_eq ==> fext_eq ==> fext_eq) subst_term.
Proof.
  repeat intros ?. eapply ext_term; firstorder.
Qed.

Ltac asimpl' := repeat first [progress rewrite ?instId_pure_term| progress rewrite ?rinstId_pure_term| progress rewrite ?compComp_pure_term| progress rewrite ?compComp'_pure_term| progress rewrite ?compRen_pure_term| progress rewrite ?compRen'_pure_term| progress rewrite ?renComp_pure_term| progress rewrite ?renComp'_pure_term| progress rewrite ?renRen_pure_term| progress rewrite ?renRen'_pure_term| progress rewrite ?instId_poly_type| progress rewrite ?rinstId_poly_type| progress rewrite ?compComp_poly_type| progress rewrite ?compComp'_poly_type| progress rewrite ?compRen_poly_type| progress rewrite ?compRen'_poly_type| progress rewrite ?renComp_poly_type| progress rewrite ?renComp'_poly_type| progress rewrite ?renRen_poly_type| progress rewrite ?renRen'_poly_type| progress rewrite ?instId_term| progress rewrite ?rinstId_term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?compRen_term| progress rewrite ?compRen'_term| progress rewrite ?renComp_term| progress rewrite ?renComp'_term| progress rewrite ?renRen_term| progress rewrite ?renRen'_term| progress rewrite ?varL_pure_term| progress rewrite ?varLRen_pure_term| progress rewrite ?varL_poly_type| progress rewrite ?varLRen_poly_type| progress rewrite ?varL_term| progress rewrite ?varLRen_term| progress (unfold up_ren, upRen_pure_term_pure_term, upRen_poly_type_poly_type, upRen_poly_type_term, upRen_term_poly_type, upRen_term_term, up_pure_term_pure_term, up_poly_type_poly_type, up_poly_type_term, up_term_poly_type, up_term_term)| progress (cbn [subst_pure_term subst_poly_type subst_term ren_pure_term ren_poly_type ren_term])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "asimpl" "in" "*" := repeat first [progress rewrite ?instId_pure_term in *| progress rewrite ?rinstId_pure_term in *| progress rewrite ?compComp_pure_term in *| progress rewrite ?compComp'_pure_term in *| progress rewrite ?compRen_pure_term in *| progress rewrite ?compRen'_pure_term in *| progress rewrite ?renComp_pure_term in *| progress rewrite ?renComp'_pure_term in *| progress rewrite ?renRen_pure_term in *| progress rewrite ?renRen'_pure_term in *| progress rewrite ?instId_poly_type in *| progress rewrite ?rinstId_poly_type in *| progress rewrite ?compComp_poly_type in *| progress rewrite ?compComp'_poly_type in *| progress rewrite ?compRen_poly_type in *| progress rewrite ?compRen'_poly_type in *| progress rewrite ?renComp_poly_type in *| progress rewrite ?renComp'_poly_type in *| progress rewrite ?renRen_poly_type in *| progress rewrite ?renRen'_poly_type in *| progress rewrite ?instId_term in *| progress rewrite ?rinstId_term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?compRen_term in *| progress rewrite ?compRen'_term in *| progress rewrite ?renComp_term in *| progress rewrite ?renComp'_term in *| progress rewrite ?renRen_term in *| progress rewrite ?renRen'_term in *| progress rewrite ?varL_pure_term in *| progress rewrite ?varLRen_pure_term in *| progress rewrite ?varL_poly_type in *| progress rewrite ?varLRen_poly_type in *| progress rewrite ?varL_term in *| progress rewrite ?varLRen_term in *| progress (unfold up_ren, upRen_pure_term_pure_term, upRen_poly_type_poly_type, upRen_poly_type_term, upRen_term_poly_type, upRen_term_term, up_pure_term_pure_term, up_poly_type_poly_type, up_poly_type_term, up_term_poly_type, up_term_term in *)| progress (cbn [subst_pure_term subst_poly_type subst_term ren_pure_term ren_poly_type ren_term] in *)| fsimpl in *].
