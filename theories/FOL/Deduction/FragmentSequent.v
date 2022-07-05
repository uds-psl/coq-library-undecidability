(** ** Normal Sequent Calculus **)

From Undecidability Require Import Shared.ListAutomation.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
Import ListAutomationNotations.
From Undecidability Require Import FOL.Syntax.Facts.
From Undecidability Require Import FOL.Syntax.Theories.
Import FragmentSyntax.
Export FragmentSyntax.

Local Unset Implicit Arguments.
Section Gentzen.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Inductive sprv : forall (b : falsity_flag), list form -> option form -> form -> Prop :=
  | Contr {b} A phi psi : sprv b A (Some phi) psi -> phi el A -> sprv b A None psi
  | IR {b} A phi psi : sprv b (phi :: A) None psi -> sprv b A None (phi → psi)
  | AllR {b} A phi : sprv b (map (subst_form ↑) A) None phi -> sprv b A None (∀ phi)
  | Absurd A phi : sprv falsity_on A None ⊥ -> sprv falsity_on A None phi
  | Ax {b} A phi : sprv b A (Some phi) phi
  | IL {b} A phi psi xi : sprv b A None phi -> sprv b A (Some psi) xi -> sprv b A (Some (phi → psi)) xi
  | AllL {b} A phi t psi : sprv b A (Some (phi[t..])) psi -> sprv b A (Some (∀ phi)) psi.

  Notation "A '⊢S' phi" := (sprv _ A None phi) (at level 30).
  Notation "A ';;' phi '⊢s' psi" := (sprv _ A (Some phi) psi) (at level 70).
  Arguments sprv {_} _ _ _.

  Definition stprv {b : falsity_flag} (T : theory) (phi : form) : Prop :=
    exists A, A ⊏ T /\ sprv A None phi.
End Gentzen.

#[global]
Hint Constructors sprv : core.

Notation "A '⊢S' phi" := (sprv _ A None phi) (at level 30).
Notation "A ';;' phi '⊢s' psi" := (sprv _ A (Some phi) psi) (at level 70).
Notation "A '⊢SE' phi" := (sprv falsity_on A None phi) (at level 30).
Notation "A ';;' phi '⊢sE' psi" := (sprv falsity_on A (Some phi) psi) (at level 70). (*
Notation "A '⊢SL' phi" := (sprv lconst A None phi) (at level 30).
Notation "A ';;' phi '⊢sL' psi" := (sprv lconst A (Some phi) psi) (at level 70). *)
Arguments sprv {_} {_} {_} _ _ _.
Notation "T '⊩SE' phi" := (@stprv _ falsity_on T phi) (at level 30).
