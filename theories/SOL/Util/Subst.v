(* ** Substitutions *)

Require Import Arith Lia.
From Undecidability.SOL.Util Require Import VectorUtil Syntax.
Require Import Undecidability.SOL.SOL.

#[global] Instance scons_indi `{funcs_signature} : Scons _ := scons_normal term.
#[global] Instance scons_func `{funcs_signature} ar : Scons _ := scons_ar ar function.
#[global] Instance scons_pred `{preds_signature} ar : Scons _ := scons_ar ar predicate.



(* Identity and shift substitutions *)

Class IdSubst X := ids : nat -> X.
Class Shift X := shift : X.

#[global] Instance var_indi' `{funcs_signature} : IdSubst term := var_indi.
#[global] Instance var_func' `{funcs_signature} : IdSubst (forall ar, function ar) := var_func.
#[global] Instance var_pred' `{preds_signature} : IdSubst (forall ar, predicate ar) := var_pred.

#[global] Instance shift_i `{funcs_signature} : Shift (nat -> term) := 
  fun n => var_indi (S n).

#[global] Instance shift_f `{funcs_signature} : Shift (nat -> nat -> forall ar, function ar) := 
  fun ar n ar' => if Nat.eq_dec ar ar' then @var_func _ (S n) ar' else @var_func _ n ar'.

#[global] Instance shift_p `{preds_signature} : Shift (nat -> nat -> forall ar, predicate ar) :=
  fun ar n ar' => if Nat.eq_dec ar ar' then @var_pred _ (S n) ar' else @var_pred _ n ar'.


(* Application of substitutions *)

Class Subst_i `{funcs_signature} X := subst_i : (nat -> term) -> X -> X.
Class Subst_f `{funcs_signature} X := subst_f : (nat -> (forall ar, function ar)) -> X -> X.
Class Subst_p `{preds_signature} X := subst_p : (nat -> (forall ar, predicate ar)) -> X -> X.

Notation "X [ σ ]i" := (subst_i σ X) (at level 7, left associativity, format "X '/' [ σ ]i").
Notation "X [ σ ]f" := (subst_f σ X) (at level 7, left associativity, format "X '/' [ σ ]f").
Notation "X [ σ ]p" := (subst_p σ X) (at level 7, left associativity, format "X '/' [ σ ]p").


#[global] Instance subst_function `{funcs_signature} {ar} : Subst_f (function ar) := fun σf f => match f with
  | var_func f => σf f ar
  | f => f
end.

#[global] Instance subst_term_i `{funcs_signature} : Subst_i term := fix subst_term_i σi t := match t with
  | var_indi x => σi x
  | func f v => func f (Vector.map (subst_term_i σi) v)
end.

#[global] Instance subst_term_f `{funcs_signature} : Subst_f term := fix subst_term_f σf t := match t with
  | var_indi x => var_indi x
  | func f v => func (subst_function σf f) (Vector.map (subst_term_f σf) v)
end.

#[global] Instance subst_predicate `{preds_signature} {ar} : Subst_p (predicate ar) := fun σp P => match P with
  | var_pred P => σp P ar
  | P => P
end.

Definition up_i `{funcs_signature} (σi : nat -> term) := scons (var_indi 0) (fun x => (σi x)[shift]i).
Definition up_f `{funcs_signature} (σf : nat -> forall ar, function ar) ar := scons (@var_func _ 0 ar) (fun x ar' => (σf x ar')[shift ar]f).
Definition up_p `{preds_signature} (σp : nat -> forall ar, predicate ar) ar := scons (@var_pred _ 0 ar) (fun x ar' => (σp x ar')[shift ar]p).

#[global] Instance subst_form_i `{funcs_signature, preds_signature, operators} : Subst_i form := fix subst_form_i σi phi := match phi with
  | fal => fal
  | atom P v => atom P (Vector.map (subst_term_i σi) v)
  | bin op phi psi => bin op (subst_form_i σi phi) (subst_form_i σi psi)
  | quant_indi op phi => quant_indi op (subst_form_i (up_i σi) phi)
  | quant_func op ar phi => quant_func op ar (subst_form_i (fun n => (σi n)[shift ar]f ) phi)
  | quant_pred op ar phi => quant_pred op ar (subst_form_i σi phi)
end.

#[global] Instance subst_form_f `{funcs_signature, preds_signature, operators} : Subst_f form := fix subst_form_f σf phi := match phi with
  | fal => fal
  | atom P v => atom P (Vector.map (subst_term_f σf) v)
  | bin op phi psi => bin op (subst_form_f σf phi) (subst_form_f σf psi)
  | quant_indi op phi => quant_indi op (subst_form_f σf phi)
  | quant_func op ar phi => quant_func op ar (subst_form_f (up_f σf ar) phi)
  | quant_pred op ar phi => quant_pred op ar (subst_form_f σf phi)
end.

#[global] Instance subst_form_p `{funcs_signature, preds_signature, operators} : Subst_p form := fix subst_form_p σp phi := match phi with
  | fal => fal
  | atom P v => atom (subst_predicate σp P) v
  | bin op phi psi => bin op (subst_form_p σp phi) (subst_form_p σp psi)
  | quant_indi op phi => quant_indi op (subst_form_p σp phi)
  | quant_func op ar phi => quant_func op ar (subst_form_p σp phi)
  | quant_pred op ar phi => quant_pred op ar (subst_form_p (up_p σp ar) phi)
end.


Declare Scope subst_scope.
Open Scope subst_scope.

Module SubstNotations.

  Notation "x .: sigma" := (scons x sigma) (at level 70, right associativity) : subst_scope.
  Notation "↑" := (shift) : subst_scope.
  Notation "f >> g" := (fun x => g (f x)) (at level 50) : subst_scope.
  Notation "f >>> g" := (fun x y => g (f x y)) (at level 50) : subst_scope.
  Notation "x '..'" := (scons x ids) (at level 1, format "x ..") : subst_scope.

  (* Open Scope subst_scope. *)

End SubstNotations.



Section SubstLemmas.

  Import SubstNotations.

  Context {Σf2 : funcs_signature}.
  Context {Σp2 : preds_signature}.
  Context {ops : operators}.


  (* Extensionality *)

  Lemma subst_term_ext_i sigma tau (t : term) :
    (forall n, sigma n = tau n) -> t[sigma]i = t[tau]i.
  Proof.
    intros H. induction t; cbn. apply H. all: f_equal; apply map_ext_forall, IH.
  Qed.

  Lemma subst_term_ext_f sigma tau (t : term) :
    (forall n ar, sigma n ar = tau n ar) -> t[sigma]f = t[tau]f.
  Proof.
    intros H. induction t; cbn.
    - reflexivity.
    - f_equal. apply H. apply map_ext_forall, IH.
    - f_equal. apply map_ext_forall, IH.
  Qed.

  Lemma subst_function_ext_f sigma tau ar (f : function ar) :
    (forall n ar, sigma n ar = tau n ar) -> f[sigma]f = f[tau]f.
  Proof.
    intros H. destruct f; cbn. apply H. reflexivity.
  Qed.

  Lemma subst_predicate_ext_p sigma tau ar (P : predicate ar) :
    (forall n ar, sigma n ar = tau n ar) -> P[sigma]p = P[tau]p.
  Proof.
    intros H. destruct P; cbn. apply H. reflexivity.
  Qed.

  Lemma subst_ext_i sigma tau (phi : form) :
    (forall n, sigma n = tau n) -> phi[sigma]i = phi[tau]i.
  Proof.
    revert sigma tau. induction phi; intros sigma tau H; cbn.
    - reflexivity.
    - f_equal. apply map_ext_forall, Forall_in. intros t _. now apply subst_term_ext_i.
    - erewrite IHphi1, IHphi2. reflexivity. easy. easy.
    - erewrite IHphi. reflexivity. intros []; cbn. reflexivity. now rewrite H.
    - erewrite IHphi. reflexivity. intros n'. now rewrite H.
    - erewrite IHphi. reflexivity. easy.
  Qed.

  Lemma subst_ext_f sigma tau (phi : form) :
    (forall n ar, sigma n ar = tau n ar) -> phi[sigma]f = phi[tau]f.
  Proof.
    revert sigma tau. induction phi; intros sigma tau H; cbn.
    - reflexivity.
    - f_equal. apply map_ext_forall, Forall_in. intros t _. now apply subst_term_ext_f.
    - erewrite IHphi1, IHphi2. reflexivity. easy. easy.
    - erewrite IHphi. reflexivity. easy.
    - erewrite IHphi. reflexivity. intros [] ar; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; try easy; now rewrite H.
    - erewrite IHphi. reflexivity. easy.
  Qed.

  Lemma subst_ext_p sigma tau (phi : form) :
    (forall n ar, sigma n ar = tau n ar) -> phi[sigma]p = phi[tau]p.
  Proof.
    revert sigma tau. induction phi; intros sigma tau H; cbn.
    - reflexivity.
    - f_equal. now apply subst_predicate_ext_p.
    - erewrite IHphi1, IHphi2. reflexivity. easy. easy.
    - erewrite IHphi. reflexivity. easy.
    - erewrite IHphi. reflexivity. easy.
    - erewrite IHphi. reflexivity. intros [] ar; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; try easy; now rewrite H.
  Qed.


  (* Identity substitutions *)

  Let forall_map_eq X n (v : vec X n) p :
    Forall (fun x => p x = x) v -> Vector.map p v = v.
  Proof.
    intros H. induction v. reflexivity. cbn. f_equal. apply H. apply IHv, H.
  Qed.

  Lemma subst_term_id_i (t : term) :
    t[ids]i = t.
  Proof.
    induction t; cbn. reflexivity. unfold ids, var_func'. f_equal.
    apply forall_map_eq, IH. f_equal. apply forall_map_eq, IH.
  Qed.

  Lemma subst_term_id_f (t : SOL.term) :
    t[ids]f = t.
  Proof.
    induction t; cbn. reflexivity. unfold ids, var_func'. f_equal.
    apply forall_map_eq, IH. f_equal. apply forall_map_eq, IH.
  Qed.

  Lemma subst_id_i (phi : form) :
    phi[ids]i = phi.
  Proof.
    induction phi; cbn; f_equal; try congruence.
    - apply forall_map_eq, Forall_in. intros t _. apply subst_term_id_i.
    - rewrite <- IHphi at 2. apply subst_ext_i. now intros [].
    - rewrite <- IHphi at 2. apply subst_ext_i. now intros [].
  Qed.

  Lemma subst_id_f (phi : form) :
    phi[ids]f = phi.
  Proof.
    induction phi; cbn; f_equal; try congruence.
    - apply forall_map_eq, Forall_in. intros t _. apply subst_term_id_f.
    - rewrite <- IHphi at 2. apply subst_ext_f.
      intros [] ar; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; cbn. reflexivity. 
      all: unfold shift, shift_f; now destruct PeanoNat.Nat.eq_dec.
  Qed.

  Lemma subst_id_p (phi : form) :
    phi[ids]p = phi.
  Proof.
    induction phi; cbn; f_equal; try congruence.
    - now destruct p.
    - rewrite <- IHphi at 2. apply subst_ext_p.
      intros [] ar; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; cbn. reflexivity. 
      all: unfold shift, shift_p; now destruct PeanoNat.Nat.eq_dec.
  Qed.


  (* Composition *)

  Lemma subst_term_comp_i sigma tau (t : term) :
    t[sigma]i[tau]i = t[sigma >> subst_term_i tau]i.
  Proof.
    induction t; cbn. reflexivity. f_equal. rewrite Vector.map_map.
    apply map_ext, Forall2_identical, IH.
    f_equal. rewrite Vector.map_map. apply map_ext, Forall2_identical, IH.
  Qed.

  Lemma subst_term_comp_f sigma tau (t : SOL.term) :
    t[sigma]f[tau]f = t[sigma >>> subst_function tau]f.
  Proof.
    induction t; cbn. reflexivity. f_equal. rewrite Vector.map_map.
    apply map_ext, Forall2_identical, IH.
    f_equal. rewrite Vector.map_map. apply map_ext, Forall2_identical, IH.
  Qed.

  Lemma up_funcomp_i sigma tau :
    forall n, (up_i sigma >> subst_term_i (up_i tau)) n = up_i (sigma >> subst_term_i tau) n.
  Proof.
    intros [|]; cbn; trivial. setoid_rewrite subst_term_comp_i.
    apply subst_term_ext_i. now intros [|].
  Qed.

  Lemma up_funcomp_f sigma tau ar :
    forall n ar', (up_f sigma ar >>> subst_function (up_f tau ar)) n ar' = up_f (sigma >>> subst_function tau) ar n ar'.
  Proof.
    intros [] ar'; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; unfold up_f; cbn.
      all: try unfold scons, scons_func, scons_ar, shift, shift_f;
      try destruct PeanoNat.Nat.eq_dec as [->|]; try easy; destruct sigma; try easy; cbn.
      + destruct PeanoNat.Nat.eq_dec; try easy; cbn. destruct n0; cbn; now destruct PeanoNat.Nat.eq_dec.
      + repeat (destruct PeanoNat.Nat.eq_dec; try easy; cbn).
      + destruct PeanoNat.Nat.eq_dec; try easy; cbn. destruct n1; cbn; now destruct PeanoNat.Nat.eq_dec.
  Qed.

  Lemma up_funcomp_p sigma tau ar :
    forall n ar', (up_p sigma ar >>> subst_predicate (up_p tau ar)) n ar' = up_p (sigma >>> subst_predicate tau) ar n ar'.
  Proof.
    intros [] ar'; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; unfold up_f; cbn.
      all: try unfold scons, scons_func, scons_ar, shift, shift_p;
      try destruct PeanoNat.Nat.eq_dec as [->|]; try easy; destruct sigma; try easy; cbn.
      + destruct PeanoNat.Nat.eq_dec; try easy; cbn. destruct n0; cbn; now destruct PeanoNat.Nat.eq_dec.
      + repeat (destruct PeanoNat.Nat.eq_dec; try easy; cbn).
      + destruct PeanoNat.Nat.eq_dec; try easy; cbn. destruct n1; cbn; now destruct PeanoNat.Nat.eq_dec.
  Qed.

  Lemma subst_term_swap_i_f tau sigma (t : term) :
    t[tau]i[sigma]f = t[sigma]f[tau >> subst_f sigma]i.
  Proof.
    induction t; cbn.
    + reflexivity.
    + f_equal. rewrite !Vector.map_map. apply map_ext, Forall2_identical, IH.
    + f_equal. rewrite !Vector.map_map. apply map_ext, Forall2_identical, IH.
  Qed.

  Lemma subst_comp_i sigma tau (phi : form) :
    phi[sigma]i[tau]i = phi[sigma >> subst_term_i tau]i.
  Proof.
    revert sigma tau. induction phi; intros sigma tau; cbn.
    - reflexivity.
    - f_equal. rewrite Vector.map_map. apply map_ext, Forall2_identical, Forall_in.
      intros t _. apply subst_term_comp_i.
    - now rewrite IHphi1, IHphi2.
    - f_equal. rewrite IHphi. apply subst_ext_i, up_funcomp_i.
    - f_equal. rewrite IHphi. apply subst_ext_i. intros n'; cbn. 
      now setoid_rewrite subst_term_swap_i_f.
    - f_equal. now rewrite IHphi.
  Qed.

  Lemma subst_comp_f (phi : SOL.form) sigma tau :
    phi[sigma]f[tau]f = phi[sigma >>> subst_function tau]f.
  Proof.
    revert sigma tau. induction phi; intros sigma tau; cbn.
    - reflexivity.
    - f_equal. rewrite Vector.map_map. apply map_ext, Forall2_identical, Forall_in.
      intros t _. apply subst_term_comp_f.
    - f_equal. now rewrite IHphi1. now rewrite IHphi2.
    - f_equal. now rewrite IHphi.
    - f_equal. rewrite IHphi. apply subst_ext_f, up_funcomp_f.
    - f_equal. now rewrite IHphi.
  Qed.

  Lemma subst_comp_p (phi : SOL.form) sigma tau :
    phi[sigma]p[tau]p = phi[sigma >>> subst_predicate tau]p.
  Proof.
    revert sigma tau. induction phi; intros sigma tau; cbn.
    - reflexivity.
    - now destruct p.
    - f_equal. now rewrite IHphi1. now rewrite IHphi2.
    - f_equal. now rewrite IHphi.
    - f_equal. now rewrite IHphi.
    - f_equal. rewrite IHphi. apply subst_ext_p, up_funcomp_p.
  Qed.


  (* Switching substitutions *)

  Lemma subst_term_switch_i_f (t : SOL.term) tau sigma :
    t[sigma]i[tau]f = t[tau]f[sigma >> subst_f tau]i.
  Proof.
    induction t; cbn.
    - reflexivity.
    - f_equal. rewrite !Vector.map_map. apply map_ext_forall, IH.
    - f_equal. rewrite !Vector.map_map. apply map_ext_forall, IH.
  Qed.

  Lemma subst_switch_i_f (phi : SOL.form) tau sigma :
    phi[sigma]i[tau]f = phi[tau]f[sigma >> subst_f tau]i.
  Proof.
    induction phi in sigma, tau |- *; cbn.
    - reflexivity.
    - f_equal. rewrite !Vector.map_map. apply map_ext_in. intros ? _. apply subst_term_switch_i_f.
    - f_equal; firstorder.
    - f_equal. rewrite IHphi. apply subst_ext_i. intros []; cbn. reflexivity.
      symmetry. erewrite subst_term_ext_i. symmetry. apply subst_term_switch_i_f. reflexivity.
    - f_equal. rewrite IHphi. apply subst_ext_i. intros x. rewrite !subst_term_comp_f. 
      apply subst_term_ext_f. intros [] ar; cbn; unfold shift, shift_f;
      now repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn).
    - f_equal. apply IHphi.
  Qed.

  Lemma subst_switch_i_p (phi : SOL.form) tau sigma :
    phi[sigma]i[tau]p = phi[tau]p[sigma]i.
  Proof.
    induction phi in sigma, tau |- *; cbn; f_equal; firstorder.
  Qed.

  Lemma subst_switch_f_p (phi : SOL.form) tau sigma :
    phi[sigma]f[tau]p = phi[tau]p[sigma]f.
  Proof.
    induction phi in sigma, tau |- *; cbn; f_equal; firstorder.
  Qed.


  (* Bounded substitutions *)

  Lemma subst_term_ext_bounded_i n t sigma tau :
    bounded_indi_term n t -> (forall x, x < n -> sigma x = tau x) -> t[sigma]i = t[tau]i.
  Proof.
    intros B H. induction t; cbn in *.
    - apply H. lia.
    - f_equal. eapply map_ext_forall, Forall_ext_Forall. apply IH. apply B.
    - f_equal. eapply map_ext_forall, Forall_ext_Forall. apply IH. apply B.
  Qed.

  Lemma subst_term_ext_bounded_f n ar t sigma tau :
    bounded_func_term ar n t -> (forall x ar', ar <> ar' \/ x < n -> sigma x ar' = tau x ar') -> t[sigma]f = t[tau]f.
  Proof.
    intros B H. induction t; cbn in *.
    - reflexivity.
    - f_equal. apply H. lia. eapply map_ext_forall, Forall_ext_Forall.
      apply IH. apply B.
    - f_equal. eapply map_ext_forall, Forall_ext_Forall. apply IH. apply B.
  Qed.

  Lemma subst_ext_bounded_i n phi sigma tau :
    bounded_indi n phi -> (forall x, x < n -> sigma x = tau x) -> phi[sigma]i = phi[tau]i.
  Proof.
    induction phi in n, sigma, tau |-*; cbn; intros B H.
    - reflexivity.
    - f_equal. apply map_ext_in. intros t H1. eapply subst_term_ext_bounded_i.
      eapply Forall_in in B. apply B. easy. apply H.
    - now erewrite (IHphi1 n), (IHphi2 n).
    - erewrite (IHphi (S n)); try easy. intros [] H1; cbn. reflexivity.
      rewrite H. reflexivity. lia.
    - erewrite (IHphi n); try easy. intros x H1. rewrite H. reflexivity. lia.
    - now erewrite (IHphi n).
  Qed.

  Lemma subst_ext_bounded_f n ar phi sigma tau :
    bounded_func ar n phi -> (forall x ar', ar <> ar' \/ x < n -> sigma x ar' = tau x ar') -> phi[sigma]f = phi[tau]f.
  Proof.
    induction phi in n, sigma, tau |-*; cbn; intros B H.
    - reflexivity.
    - f_equal. apply map_ext_in. intros t H1. eapply subst_term_ext_bounded_f.
      eapply Forall_in in B. apply B. easy. apply H.
    - now erewrite (IHphi1 n), (IHphi2 n).
    - now erewrite (IHphi n).
    - assert (ar = n0 \/ ar <> n0) as [->|H1] by lia.
      + destruct B as [[H2 B]|]; try lia. erewrite (IHphi (S n)); try easy.
        intros [] ar' H1; cbn; destruct PeanoNat.Nat.eq_dec as [->|]. reflexivity.
        all: rewrite H; try reflexivity; lia.
      + destruct B as [|[H2 B]]; try lia. erewrite (IHphi n); try easy.
        intros [] ar' H3; cbn; destruct PeanoNat.Nat.eq_dec as [->|]. reflexivity.
        all: rewrite H; try reflexivity; lia.
    - now erewrite (IHphi n).
  Qed.

  Lemma subst_ext_bounded_p n ar phi sigma tau :
    bounded_pred ar n phi -> (forall x ar', ar <> ar' \/ x < n -> sigma x ar' = tau x ar') -> phi[sigma]p = phi[tau]p.
  Proof.
    induction phi in n, sigma, tau |-*; cbn; intros B H.
    - reflexivity.
    - destruct p; cbn. rewrite H. reflexivity. lia. reflexivity.
    - now erewrite (IHphi1 n), (IHphi2 n).
    - now erewrite (IHphi n).
    - now erewrite (IHphi n).
    - assert (ar = n0 \/ ar <> n0) as [->|H1] by lia.
      + destruct B as [[H2 B]|]; try lia. erewrite (IHphi (S n)); try easy.
        intros [] ar' H1; cbn; destruct PeanoNat.Nat.eq_dec as [->|]. reflexivity.
        all: rewrite H; try reflexivity; lia.
      + destruct B as [|[H2 B]]; try lia. erewrite (IHphi n); try easy.
        intros [] ar' H3; cbn; destruct PeanoNat.Nat.eq_dec as [->|]. reflexivity.
        all: rewrite H; try reflexivity; lia.
  Qed.

  Corollary subst_ext_i_closed phi sigma tau :
    bounded_indi 0 phi -> phi[sigma]i = phi[tau]i.
  Proof.
    intros B. eapply subst_ext_bounded_i. apply B. lia.
  Qed.

  Corollary subst_ext_p_closed phi sigma tau ar :
    bounded_pred ar 0 phi -> (forall ar', ar <> ar' -> forall x, sigma x ar' = tau x ar') -> phi[sigma]p = phi[tau]p.
  Proof.
    intros B H. eapply subst_ext_bounded_p. apply B. intros x ar' []. now apply H. lia.
  Qed.

  Lemma bounded_indi_subst_p n phi sigma :
    bounded_indi n phi -> bounded_indi n (phi[sigma]p).
  Proof.
    revert n sigma. induction phi; firstorder.
  Qed.

  Lemma bounded_pred_subst_p ar b phi sigma :
    (forall x, sigma x ar = var_pred x) -> bounded_pred ar b phi -> bounded_pred ar b (phi[sigma]p).
  Proof.
    revert sigma b. induction phi; intros sigma b' Hsigma H; cbn.
    - easy.
    - destruct p; cbn. 2: easy. destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|].
      rewrite Hsigma. destruct H; lia. destruct sigma; lia.
    - firstorder.
    - firstorder.
    - firstorder.
    - destruct H.
      + left. split. easy. apply IHphi. 2: easy. intros []; unfold up_p, scons, shift, shift_p; cbn;
        destruct PeanoNat.Nat.eq_dec as [->|]; try lia; cbn. reflexivity. specialize (Hsigma n0).
        destruct sigma; cbn. destruct PeanoNat.Nat.eq_dec; try easy. congruence. congruence.
      + right. split. easy. apply IHphi. 2: easy. intros x. specialize (Hsigma x).
        destruct x; unfold up_p, scons, shift, shift_p; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; try lia; 
        destruct sigma; cbn; try destruct PeanoNat.Nat.eq_dec; congruence.
  Qed.


  (* Other facts *)

  Lemma subst_term_shift_i (t : term) x :
    t[↑]i[x..]i = t.
  Proof.
    rewrite subst_term_comp_i. rewrite <- subst_term_id_i. now apply subst_term_ext_i.
  Qed.

  Lemma subst_form_shift_i (phi : form) x :
    phi[↑]i[x..]i = phi.
  Proof.
    rewrite subst_comp_i. rewrite <- subst_id_i. now apply subst_ext_i.
  Qed.

  Lemma subst_term_shift_f (t : term) ar (f : function ar) :
    t[↑ ar]f[f..]f = t.
  Proof.
    rewrite subst_term_comp_f. rewrite <- subst_term_id_f. apply subst_term_ext_f.
    intros n ar'. unfold shift, shift_f. repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn).
    reflexivity. now destruct n; cbn; destruct PeanoNat.Nat.eq_dec; try lia.
  Qed.

  Lemma subst_function_shift_f ar' (f : function ar') ar (x : function ar) :
    f[↑ ar]f[x..]f = f.
  Proof.
    destruct f; cbn. unfold shift, shift_f. now destruct n; repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn).
    reflexivity.
  Qed.

  Lemma subst_form_shift_f (phi : form) ar (f : function ar) :
    phi[↑ ar]f[f..]f = phi.
  Proof.
    rewrite subst_comp_f. rewrite <- subst_id_f. apply subst_ext_f.
    intros n ar'. unfold shift, shift_f. repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn).
    reflexivity. now destruct n; cbn; destruct PeanoNat.Nat.eq_dec; try lia.
  Qed.

  Lemma subst_predicate_shift_p ar' (P : predicate ar') ar (x : predicate ar) :
    P[↑ ar]p[x..]p = P.
  Proof.
    destruct P; cbn. unfold shift, shift_p. now destruct n; repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn).
    reflexivity.
  Qed.

  Lemma subst_form_shift_p (phi : form) ar (P : predicate ar) :
    phi[↑ ar]p[P..]p = phi.
  Proof.
    rewrite subst_comp_p. rewrite <- subst_id_p. apply subst_ext_p.
    intros n ar'. unfold shift, shift_p. repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn).
    reflexivity. now destruct n; cbn; destruct PeanoNat.Nat.eq_dec; try lia.
  Qed.

  Lemma up_form_i phi sigma :
    phi[↑]i[up_i sigma]i = phi[sigma]i[↑]i.
  Proof.
    rewrite !subst_comp_i. now apply subst_ext_i.
  Qed.

  Lemma up_form_f phi sigma ar :
    phi[↑ ar]f[up_f sigma ar]f = phi[sigma]f[↑ ar]f.
  Proof.
    rewrite !subst_comp_f. apply subst_ext_f. intros n ar'. unfold shift, shift_f.
    repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn). now destruct sigma.
    destruct n; cbn; now destruct PeanoNat.Nat.eq_dec.
  Qed.

  Lemma up_form_p phi sigma ar :
    phi[↑ ar]p[up_p sigma ar]p = phi[sigma]p[↑ ar]p.
  Proof.
    rewrite !subst_comp_p. apply subst_ext_p. intros n ar'. unfold shift, shift_p.
    repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn). now destruct sigma.
    destruct n; cbn; now destruct PeanoNat.Nat.eq_dec.
  Qed.

  Lemma funcfreeTerm_subst_i t sigma :
    (forall x, funcfreeTerm (sigma x)) -> funcfreeTerm t -> funcfreeTerm (t[sigma]i).
  Proof.
    intros H F. induction t; cbn; trivial. eapply Forall_map, Forall_ext_Forall.
    apply IH. apply F.
  Qed.

  Lemma funcfreeTerm_subst_f t sigma :
    funcfreeTerm t -> funcfreeTerm (t[sigma]f).
  Proof.
    intros F. induction t; cbn; trivial. now exfalso. eapply Forall_map, Forall_ext_Forall.
    apply IH. apply F.
  Qed.

  Lemma funcfree_subst_i phi sigma :
    (forall x, funcfreeTerm (sigma x)) -> funcfree phi -> funcfree(phi[sigma]i).
  Proof.
    revert sigma. induction phi; intros sigma H F; cbn. 1,3-6: firstorder.
    - apply IHphi; trivial. intros []; cbn. easy. now apply funcfreeTerm_subst_i.
    - apply Forall_map, Forall_in. intros t H1. apply funcfreeTerm_subst_i. easy.
      eapply Forall_in in F. apply F. easy.
  Qed.

  Lemma funcfree_subst_f phi sigma :
    funcfree phi -> funcfree(phi[sigma]f).
  Proof.
    induction phi in sigma |-*; cbn; firstorder. apply Forall_in. 
    intros t [? [<- ?]]%In_map_iff. apply funcfreeTerm_subst_f.
    eapply Forall_in in H. apply H. easy.
  Qed.

  Lemma funcfree_subst_p phi sigma :
    funcfree phi -> funcfree(phi[sigma]p).
  Proof.
    induction phi in sigma |-*; firstorder.
  Qed.

End SubstLemmas.
