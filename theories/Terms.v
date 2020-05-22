(** * Preliminaries FOL*  *)

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import Omega.

Ltac capply H := eapply H; try eassumption.

Ltac resolve_existT :=
  match goal with
     | [ H2 : existT _ _ _ = existT _ _ _ |- _ ] => rewrite (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H2) in *
  | _ => idtac
  end.

Ltac inv H :=
  inversion H; subst; repeat (progress resolve_existT).



(** ** Syntax of FOL* **)

From Undecidability.FOLC Require Export unscoped.

Notation vector := Vector.t.
Import Vector.
Arguments nil {A}.
Arguments cons {A} _ {n}.
Derive Signature for vector.

Class Signature := B_S { Funcs : Type; fun_ar : Funcs -> nat ;
              Preds : Type; pred_ar : Preds -> nat }.


Section fix_sig.

Context {Sigma : Signature}.

Inductive term  : Type :=
  | var_term : (fin)  -> term
  | Func : forall (f : Funcs), Vector.t term (fun_ar f) -> term .

Definition congr_Func { f : Funcs }  { s0 : Vector.t term (fun_ar f) } { t0 : Vector.t term (fun_ar f)} (H1 : s0 = t0) : Func  f s0 = Func  f t0 :=
  (eq_trans) (eq_refl) ((ap) (fun x => Func  f x) H1).

Fixpoint subst_term   (sigmaterm : (fin)  -> term ) (s : term ) : _ :=
    match s with
    | var_term  s => sigmaterm s
    | Func  f s0 => Func  f (Vector.map (subst_term sigmaterm) s0)
    end.

Definition up_term_term   (sigma : (fin)  -> term ) : _ :=
  (scons) ((var_term ) (var_zero)) ((funcomp) (subst_term ((funcomp) (var_term ) (shift))) sigma).


Definition upId_term_term  (sigma : (fin)  -> term ) (Eq : forall x, sigma x = (var_term ) x) : forall x, (up_term_term sigma) x = (var_term ) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_term ((funcomp) (var_term ) (shift))) (Eq fin_n)
  | 0 => eq_refl
  end.


Fixpoint idSubst_term  (sigmaterm : (fin)  -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : term ) : subst_term sigmaterm s = s :=
    match s with
    | var_term  s => Eqterm s
    | Func  f s0 => congr_Func ((vec_id (idSubst_term sigmaterm Eqterm)) s0)
    end.

Definition upExt_term_term   (sigma : (fin)  -> term ) (tau : (fin)  -> term ) (Eq : forall x, sigma x = tau x) : forall x, (up_term_term sigma) x = (up_term_term tau) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_term ((funcomp) (var_term) (shift))) (Eq fin_n)
  | 0 => eq_refl
  end.


Fixpoint ext_term   (sigmaterm : (fin)  -> term ) (tauterm : (fin)  -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : term ) : subst_term sigmaterm s = subst_term tauterm s :=
    match s with
    | var_term  s => Eqterm s
    | Func  f s0 => congr_Func ((vec_ext (ext_term sigmaterm tauterm Eqterm)) s0)
    end.

Fixpoint compSubstSubst_term    (sigmaterm : (fin)  -> term ) (tauterm : (fin)  -> term ) (thetaterm : (fin)  -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : term ) : subst_term tauterm (subst_term sigmaterm s) = subst_term thetaterm s :=
    match s with
    | var_term  s => Eqterm s
    | Func  f s0 => congr_Func ((vec_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s0)
    end.

Definition up_subst_subst_term_term    (sigma : (fin)  -> term ) (tauterm : (fin)  -> term ) (theta : (fin)  -> term ) (Eq : forall x, ((funcomp) (subst_term tauterm) sigma) x = theta x) : forall x, ((funcomp) (subst_term (up_term_term tauterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compSubstSubst_term ((funcomp) (var_term) (shift)) (up_term_term tauterm) ((funcomp) (up_term_term tauterm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_term tauterm ((funcomp) (var_term) (shift)) ((funcomp) (subst_term ((funcomp) (var_term ) (shift))) tauterm) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_term ((funcomp) (var_term ) (shift))) (Eq fin_n)))
  | 0 => eq_refl
  end.

Lemma instId_term  : subst_term (var_term ) = (@id) (term ) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_term ) (fun n => eq_refl) (((@id) (term )) x))). Qed.

Lemma varL_term   (sigmaterm : (fin)  -> term ) : (funcomp) (subst_term sigmaterm) (var_term ) = sigmaterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_term    (sigmaterm : (fin)  -> term ) (tauterm : (fin)  -> term ) (s : term ) : subst_term tauterm (subst_term sigmaterm s) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_term sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_term    (sigmaterm : (fin)  -> term ) (tauterm : (fin)  -> term ) : (funcomp) (subst_term tauterm) (subst_term sigmaterm) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term sigmaterm tauterm n)). Qed.

(* **** Forall and Vector.t technology **)

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Inductive Forall {A : Type} (P : A -> Type) : forall {n}, vector A n -> Type :=
| Forall_nil : Forall P (@Vector.nil A)
| Forall_cons : forall n (x : A) (l : vector A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

Inductive vec_in {A : Type} (a : A) : forall {n}, vector A n -> Type :=
| vec_inB {n} (v : vector A n) : vec_in a (cons a v)
| vec_inS a' {n} (v :vector A n) : vec_in a v -> vec_in a (cons a' v).
Hint Constructors vec_in.

Lemma strong_term_ind' (p : term -> Type) :
  (forall x, p (var_term x)) -> (forall F v, (Forall p v) -> p (Func F v)) -> forall (t : term), p t.
Proof.
  intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
  - apply f1.
  - apply f2. induction v.
    + econstructor.
    + econstructor. now eapply strong_term_ind'. eauto.
Qed.  

Lemma strong_term_ind (p : term -> Type) :
  (forall x, p (var_term x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (Func F v)) -> forall (t : term), p t.
Proof.
  intros f1 f2. eapply strong_term_ind'.
  - apply f1.
  - intros. apply f2. intros t. induction 1; inv X; eauto.
Qed.

(** closed terms *)

Inductive unused_term (n : nat) : term -> Prop :=
| uft_var m : n <> m -> unused_term n (var_term m)
| uft_Func F v : (forall t, vec_in t v -> unused_term n t) -> unused_term n (Func F v).

Lemma vec_unused n (v : vector term n)  :
  (forall t, vec_in t v -> { n | forall m, n <= m -> unused_term m t }) ->
  { k | forall t, vec_in t v -> forall m, k <= m -> unused_term m t }.
Proof.
  intros Hun. induction v in Hun |-*.
  - exists 0. intros n H. inv H.
  - destruct IHv as [k H]. 1: eauto. destruct (Hun h (vec_inB h v)) as [k' H'].
    exists (k + k'). intros t H2. inv H2; intros m Hm; [apply H' | apply H]; now try omega.
Qed.

Lemma find_unused_term t :
  { n | forall m, n <= m -> unused_term m t }.
Proof.
  induction t using strong_term_ind.
  - exists (S x). intros m Hm. constructor. omega.
  - destruct (vec_unused X) as [k H]. exists k. eauto using unused_term.
Qed.

End fix_sig.

Hint Constructors vec_in.
  

                                                                     

                                                                     
