(** * First-Order Logic *)


From Undecidability.Synthetic Require Export Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Export Shared.ListAutomation.
Import ListAutomationNotations.

Require Import Vector.
Definition vec := t.


(** Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
          |0 => x
          |S n => xi n
          end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

(** Signatures are a record to allow for easier definitions of general transformations on signatures *)

Class funcs_signature :=
  { syms : Type; ar_syms : syms -> nat }.

Coercion syms : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; ar_preds : preds -> nat }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  (** We use the stdlib definition of vectors to be maximally compatible  *)

  Unset Elimination Schemes.

  Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.

  Set Elimination Schemes.

  Fixpoint subst_term (σ : nat -> term) (t : term) : term :=
    match t with
    | var t => σ t
    | func f v => func f (map (subst_term σ) v)
    end.

  Context {Σ_preds : preds_signature}.

  (** We use a flag to switch on and off a constant for falisity *)

  Inductive falsity_flag := falsity_off | falsity_on.
  Existing Class falsity_flag.
  Existing Instance falsity_on | 1.
  Existing Instance falsity_off | 0.

  (** Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.

  (** Formulas have falsity as fixed constant -- we could parametrise against this in principle *)
  Inductive form : falsity_flag -> Type :=
  | falsity : form falsity_on
  | atom {b} : forall (P : preds), vec term (ar_preds P) -> form b
  | bin {b} : binop -> form b -> form b -> form b
  | quant {b} : quantop -> form b -> form b.
  Arguments form {_}.

  Definition up (σ : nat -> term) := scons (var 0) (funcomp (subst_term (funcomp var S)) σ).

  Fixpoint subst_form `{falsity_flag} (σ : nat -> term) (phi : form) : form :=
    match phi with
    | falsity => falsity
    | atom P v => atom P (map (subst_term σ) v)
    | bin op phi1 phi2 => bin op (subst_form σ phi1) (subst_form σ phi2)
    | quant op phi => quant op (subst_form (up σ) phi)
    end.

  (** Induction principle for terms *)

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type :=
  | vec_inB {n} (v : t A n) : vec_in a (cons A a n v)
  | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
  Hint Constructors vec_in : core.
  
  Lemma term_rect' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.

End fix_signature.



(** Setting implicit arguments is crucial  *)
(** We can write term both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Arguments subst_term {_} _ _.

(** Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
Arguments form  _ _ _ _, _ _ {_ _}, {_ _ _ _}, {_ _ _} _.
Arguments atom  _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments bin   _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments quant _ _ _ _, _ _ {_ _}, {_ _ _ _}.

Arguments up         _, {_}.
Arguments subst_form _ _ _ _, _ _ {_ _}, {_ _ _ _}.



(** Substitution Notation *)

Class Subst {Sigma : funcs_signature} Y := substfun : (nat -> term) -> Y -> Y.

Instance Subst_term (Sigma : funcs_signature) : Subst term := subst_term.

Instance Subst_form (Sigma : funcs_signature) (Sigma' : preds_signature) (ops : operators) (ff : falsity_flag) :
  Subst form := @subst_form Sigma Sigma' ops ff.

Definition shift {Sigma : funcs_signature} : nat -> term :=
  fun n => var (S n).

Declare Scope subst_scope.

Notation "$ x" := (var x) (at level 5, format "$ '/' x").
Notation "↑" := (shift) : subst_scope.
Notation "s [ sigma ]" := (substfun sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 70) : subst_scope.
Notation "f >> g" := (funcomp g f) (at level 50) : subst_scope.
Notation "s '..'" := (scons s var) (at level 1, format "s ..") : subst_scope.

Open Scope subst_scope.



Ltac cbns :=
    cbn; repeat (match goal with [ |- context f[subst_form ?sigma ?phi] ] => change (subst_form sigma phi) with (phi[sigma]) end).

Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Lemma subst_term_ext (t : term) sigma tau :
    (forall n, sigma n = tau n) -> t[sigma] = t[tau].
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now apply map_ext_in.
  Qed.

  Lemma subst_term_id (t : term) sigma :
    (forall n, sigma n = var n) -> t[sigma] = t.
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now erewrite map_ext_in, map_id.
  Qed.

  Lemma subst_term_var (t : term) :
    t[var] = t.
  Proof.
    now apply subst_term_id.
  Qed.

  Lemma subst_term_comp (t : term) sigma tau :
    t[sigma][tau] = t[sigma >> subst_term tau].
  Proof.
    induction t; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. now apply map_ext_in.
  Qed.

  Lemma subst_term_shift (t : term) s :
    t[↑][s..] = t.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. now intros [|].
  Qed.

  Lemma up_term (t : term) xi :
    t[↑][up xi] = t[xi][↑].
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
    induction phi in sigma, tau |- *; cbns; intros H.
    - reflexivity.
    - f_equal. apply map_ext. intros s. now apply subst_term_ext.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_ext.
  Qed.

  Lemma subst_id {ff : falsity_flag} (phi : form) sigma :
    (forall n, sigma n = var n) -> phi[sigma] = phi.
  Proof.
    induction phi in sigma |- *; cbns; intros H.
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
    induction phi in sigma, tau |- *; cbns.
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
  
End Subst.



(** ** Enumerability *)

(*Fixpoint L_term n : list term :=
  match n with
  | 0 => [t_e]
  | S n => L_term n ++ [V n; P n] ++ [ t_f b t | (b,t) ∈ (L_T bool n × L_term n) ]
  end.

Instance enumT_term : list_enumerator__T L_term term.
Proof.
  intros t. induction t.
  + exists (S v); cbn; eauto.
  + exists (S p); cbn; eauto.
  + destruct IHt as [m1], (el_T b) as [m2].
    exists (1 + m1 + m2). cbn. in_app 4. in_collect (b, t); eapply cum_ge'; eauto; lia.
  + exists 0. cbn; eauto.
Qed.

Fixpoint L_form {b} n : list (form b) :=
  match n with
  | 0 => []
  | S n => L_form n
            ++ [Q]
            ++ [ Pr s t | (s,t) ∈ (L_T term n × L_T term n) ]
            ++ [ phi1 --> phi2 | (phi1, phi2) ∈ (L_form n × L_form n) ]
            ++ [ ∀ n; phi | (n,phi) ∈ (L_T nat n × L_form n) ]
            ++ match b with
                 frag => []
               | full => [Fal]
               end
  end.

Instance enumT_form {b} : list_enumerator__T L_form (form b).
Proof with (try eapply cum_ge'; eauto; lia).
  intros phi. induction phi.
  + destruct (el_T t) as [m1], (el_T t0) as [m2]. exists (1 + m1 + m2). cbn.
    in_app 3. in_collect (t, t0)...
  + exists 1. cbn; eauto.
  + exists 1; cbn; firstorder.
  + destruct IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m1 + m2). cbn.
    in_app 4. in_collect (phi1, phi2)...
  + destruct IHphi as [m1], (el_T n) as [m2]. exists (1 + m1 + m2). cbn -[L_T].
    in_app 5. in_collect (n, phi)...
Qed.

Instance dec_term : eq_dec term.
Proof.
  intros ? ?; unfold dec; repeat decide equality.
Qed.

Instance dec_logic : eq_dec logic.
Proof.
  intros ? ?; unfold dec; decide equality.
Qed.

Require Import EqdepFacts.

Lemma dec_form {b1 b2} phi1 phi2 : dec (eq_dep logic form b1 phi1 b2 phi2).
Proof.
  unfold dec. revert phi2; induction phi1; intros; try destruct phi2.
  all: try now right; inversion 1.
  all: try decide (b0 = b); subst; try now right; inversion 1; congruence.
  all: try now left.
  - decide (t = t1); decide (t0 = t2); subst; try now right; inversion 1; congruence.
    now left.
  - destruct (IHphi1_1 phi2_1), (IHphi1_2 phi2_2); subst; try firstorder congruence.
    left. eapply Eqdep_dec.eq_dep_eq_dec in e; eapply Eqdep_dec.eq_dep_eq_dec in e0.
    all: try eapply dec_logic.
    subst; econstructor.

    all: right; intros ? % Eqdep_dec.eq_dep_eq_dec; try eapply dec_logic.
    all: eapply n. all: inversion H0; eapply eq_sigT_eq_dep in H2; eapply Eqdep_dec.eq_dep_eq_dec in H2; try eapply dec_logic; subst. econstructor. 
    all: eapply eq_sigT_eq_dep in H1; eapply Eqdep_dec.eq_dep_eq_dec in H1; try eapply dec_logic; subst.
    all: econstructor. 
  - decide (n = n0); destruct (IHphi1 phi2); subst.
    eapply Eqdep_dec.eq_dep_eq_dec in e0; try eapply dec_logic; subst. now left.
    all: right; inversion 1; try eapply eq_sigT_eq_dep in H2; try eapply Eqdep_dec.eq_dep_eq_dec in H2; try eapply dec_logic; subst.
    eapply n1. econstructor. all:congruence.
Qed.

Instance eq_dec_form {b : logic} phi1 phi2 : dec (phi1 = phi2 :> form b).
Proof.
  destruct (dec_form phi1 phi2).
  - eapply Eqdep_dec.eq_dep_eq_dec in e; try eapply dec_logic; subst. now left.
  - right. intros ->. now eapply n.
Qed.*)
