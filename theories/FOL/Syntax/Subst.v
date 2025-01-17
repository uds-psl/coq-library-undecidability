From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
Import ListAutomationNotations.

From Stdlib Require Import Eqdep_dec PeanoNat Nat Lia.
From Stdlib Require Import Vectors.Vector.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From Stdlib Require Import EqdepFacts.

Local Notation vec := t.

From Undecidability Require Export FOL.Syntax.Core.


Local Set Implicit Arguments.
Local Unset Strict Implicit.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  (* Substitution induction principle for formulas *)

  Fixpoint size {ff : falsity_flag} (phi : form) :=
    match phi with
    | atom _ _ => 0
    | falsity => 0
    | bin b phi psi => S (size phi + size psi)
    | quant q phi => S (size phi)
    end.

  Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
    (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
  Proof.
    intros H x. apply H.
    induction (f x).
    - intros y. lia.
    - intros y. intros [] % Nat.lt_eq_cases.
      + apply IHn; lia.
      + apply H. injection H0. now intros ->.
  Qed.

  Lemma subst_size {ff : falsity_flag} rho phi :
    size (subst_form rho phi) = size phi.
  Proof.
    revert rho; induction phi; intros rho; cbn; congruence.
  Qed.

  Lemma form_ind_subst' {ff : falsity_flag} :
    forall P : form -> Prop,
      (match ff return ((form Σ_funcs Σ_preds ops ff) -> Prop) -> Prop with 
      | falsity_off => fun _ => True
      | falsity_on => fun P' => P' falsity
      end) P ->
      (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
      (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
      (forall (q : quantop) (f2 : form), (forall sigma, P (subst_form sigma f2)) -> P (quant q f2)) ->
      forall (f4 : form), P f4.
  Proof.
    intros P H1 H2 H3 H4 phi. induction phi using (@size_ind _ size).
    destruct phi; cbn in *.
    - easy.
    - apply H2.
    - apply H3; apply H; lia.
    - apply H4. intros sigma. apply H. rewrite subst_size. econstructor.
  Qed.

  Lemma form_ind_subst :
    forall P : form -> Prop,
      P falsity ->
      (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
      (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
      (forall (q : quantop) (f2 : form), (forall sigma, P (subst_form sigma f2)) -> P (quant q f2)) ->
      forall (f4 : form), P f4.
  Proof.
    apply (form_ind_subst' (ff := falsity_on)).
  Qed.

  Lemma form_ind_falsity  (P : form falsity_on -> Prop) :
    P falsity ->
    (forall  (P0 : Σ_preds ) (t : t term (ar_preds P0)), P (atom P0 t)) ->
    (forall  (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
    (forall (q : quantop) (f2 : form), P f2 -> P (quant q f2)) ->
    forall (f4 : form), P f4.
  Proof.
    intros H1 H2 H3 H4 phi.
    change ((fun ff => match ff with falsity_on => fun phi => P phi | _ => fun _ => True end) falsity_on phi).
    induction phi; try destruct b; [apply H1|easy| apply H2|easy|apply H3|easy|apply H4]. 1: apply IHphi1; assumption. 1: apply IHphi2; assumption. apply IHphi; assumption.
  Qed.

  Lemma form_ind_no_falsity  (P : form falsity_off -> Prop) :
    (forall  (P0 : Σ_preds ) (t : t term (ar_preds P0)), P (atom P0 t)) ->
    (forall  (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
    (forall (q : quantop) (f2 : form), P f2 -> P (quant q f2)) ->
    forall (f4 : form), P f4.
  Proof.
    intros H2 H3 H4 phi.
    change ((fun ff => match ff with falsity_on => fun phi => True | _ => fun _ => P phi end) falsity_off phi).
    induction phi; try destruct b; [easy|apply H2|easy|apply H3|easy|apply H4|easy].
    1: apply IHphi1; assumption.
    1: apply IHphi2; assumption.
       apply IHphi; assumption.
  Qed.

End fix_signature.


(* ** Substituion lemmas *)

Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Lemma subst_term_ext (t : term) sigma tau :
    (forall n, sigma n = tau n) -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now apply map_ext_in.
  Qed.

  Lemma subst_term_id (t : term) sigma :
    (forall n, sigma n = var n) -> t`[sigma] = t.
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now erewrite map_ext_in, map_id.
  Qed.

  Lemma subst_term_var (t : term) :
    t`[var] = t.
  Proof.
    now apply subst_term_id.
  Qed.

  Lemma subst_term_comp (t : term) sigma tau :
    t`[sigma]`[tau] = t`[sigma >> subst_term tau].
  Proof.
    induction t; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. now apply map_ext_in.
  Qed.

  Lemma subst_term_shift (t : term) s :
    t`[↑]`[s..] = t.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. now intros [|].
  Qed.

  Lemma up_term (t : term) xi :
    t`[↑]`[up xi] = t`[xi]`[↑].
  Proof.
    rewrite !subst_term_comp. apply subst_term_ext. reflexivity.
  Qed.

  Lemma up_ext sigma tau :
    (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_var sigma :
    (forall n, sigma n = var n) -> forall n, up sigma n = var n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_funcomp sigma tau :
    forall n, (up sigma >> subst_term (up tau)) n = up (sigma >> subst_term tau) n.
  Proof.
    intros [|]; cbn; trivial.
    setoid_rewrite subst_term_comp.
    apply subst_term_ext. now intros [|].
  Qed.

  Lemma subst_ext {ff : falsity_flag} (phi : form) sigma tau :
    (forall n, sigma n = tau n) -> phi[sigma] = phi[tau].
  Proof.
    induction phi in sigma, tau |- *; cbn; intros H.
    - reflexivity.
    - f_equal. apply map_ext. intros s. now apply subst_term_ext.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_ext.
  Qed.

  Lemma subst_id {ff : falsity_flag} (phi : form) sigma :
    (forall n, sigma n = var n) -> phi[sigma] = phi.
  Proof.
    induction phi in sigma |- *; cbn; intros H.
    - reflexivity.
    - f_equal. erewrite map_ext; try apply map_id. intros s. now apply subst_term_id.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_var.
  Qed.

  Lemma subst_var {ff : falsity_flag} (phi : form) :
    phi[var] = phi.
  Proof.
    now apply subst_id.
  Qed.

  Lemma subst_comp {ff : falsity_flag} (phi : form) sigma tau :
    phi[sigma][tau] = phi[sigma >> subst_term tau].
  Proof.
    induction phi in sigma, tau |- *; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. apply map_ext. intros s. apply subst_term_comp.
    - now rewrite IHphi1, IHphi2.
    - rewrite IHphi. f_equal. now apply subst_ext, up_funcomp.
  Qed.

  Lemma subst_shift {ff : falsity_flag} (phi : form) s :
    phi[↑][s..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [|].
  Qed.

  Lemma up_form {ff : falsity_flag} xi psi :
    psi[↑][up xi] = psi[xi][↑].
  Proof.
    rewrite !subst_comp. apply subst_ext. reflexivity.
  Qed.

  Lemma up_decompose {ff : falsity_flag} sigma phi :
    phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.  
  
End Subst.