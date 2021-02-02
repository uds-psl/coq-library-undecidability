(* * First-Order Logic *)


From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Require Import Coq.Vectors.Vector.
Local Notation vec := t.


(* Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
        | 0 => x
        | S n => xi n
        end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

(* Signatures are a record to allow for easier definitions of general transformations on signatures *)

Class funcs_signature :=
  { syms : Type; ar_syms : syms -> nat }.

Coercion syms : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; ar_preds : preds -> nat }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  (* We use the stdlib definition of vectors to be maximally compatible  *)

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

  (* We use a flag to switch on and off a constant for falisity *)

  Inductive falsity_flag := falsity_off | falsity_on.
  Existing Class falsity_flag.
  Existing Instance falsity_on | 1.
  Existing Instance falsity_off | 0.

  (* Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.

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

End fix_signature.



(* Setting implicit arguments is crucial  *)
(* We can write term both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Arguments subst_term {_} _ _.

(* Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
Arguments form  _ _ _ _, _ _ {_ _}, {_ _ _ _}, {_ _ _} _.
Arguments atom  _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments bin   _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments quant _ _ _ _, _ _ {_ _}, {_ _ _ _}.

Arguments up         _, {_}.
Arguments subst_form _ _ _ _, _ _ {_ _}, {_ _ _ _}.



(* Substitution Notation *)

Declare Scope subst_scope.
Open Scope subst_scope.

Notation "$ x" := (var x) (at level 3, format "$ '/' x") : subst_scope.
Notation "t `[ sigma ]" := (subst_term sigma t) (at level 7, left associativity, format "t '/' `[ sigma ]") : subst_scope.
Notation "phi [ sigma ]" := (subst_form sigma phi) (at level 7, left associativity, format "phi '/' [ sigma ]") : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 70, right associativity) : subst_scope.
Notation "f >> g" := (funcomp g f) (at level 50) : subst_scope.
Notation "s '..'" := (scons s var) (at level 4, format "s ..") : subst_scope.
Notation "↑" := (S >> var) : subst_scope.



(* Full syntax *)

Declare Scope syn.
Open Scope syn.

Module FullSyntax.

  Inductive full_logic_sym : Type :=
  | Conj : full_logic_sym
  | Disj : full_logic_sym
  | Impl : full_logic_sym.

  Inductive full_logic_quant : Type :=
  | All : full_logic_quant
  | Ex : full_logic_quant.

  Definition full_operators : operators :=
    {| binop := full_logic_sym ; quantop := full_logic_quant |}.

  #[export] Hint Immediate full_operators : typeclass_instances.

  Notation "∀ Phi" := (@quant _ _ full_operators _ All Phi) (at level 50) : syn.
  Notation "∃ Phi" := (@quant _ _ full_operators _ Ex Phi) (at level 50) : syn.
  Notation "A ∧ B" := (@bin _ _ full_operators _ Conj A B) (at level 41) : syn.
  Notation "A ∨ B" := (@bin _ _ full_operators _ Disj A B) (at level 42) : syn.
  Notation "A '~>' B" := (@bin _ _ full_operators _ Impl A B) (at level 43, right associativity) : syn.
  Notation "⊥" := (falsity) : syn.
  Notation "¬ A" := (A ~> ⊥) (at level 42) : syn.
  Notation "A '<~>' B" := ((A ~> B) ∧ (B ~> A)) (at level 43) : syn.

End FullSyntax.

Import FullSyntax.



(* Fragment syntax *)

Module FragmentSyntax.

  Inductive frag_logic_binop : Type :=
  | Impl : frag_logic_binop.

  Inductive frag_logic_quant : Type :=
  | All : frag_logic_quant.

  Definition frag_operators : operators :=
    {| binop := frag_logic_binop ; quantop := frag_logic_quant |}.

  #[export] Hint Immediate frag_operators : typeclass_instances.

  Notation "∀ Phi" := (@quant _ _ frag_operators _ All Phi) (at level 50).
  Notation "phi '-->' psi" := (@bin _ _ frag_operators _ Impl phi psi) (at level 43, right associativity).
  Notation "¬ phi" := (phi --> falsity) (at level 42).

End FragmentSyntax.
