(** ** Natural Deduction *)

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
From Undecidability Require Import FOL.Syntax.Core.
Import FragmentSyntax.
Export FragmentSyntax.

Local Set Implicit Arguments.

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Reserved Notation "A ⊢ phi" (at level 61).
  
  (* ** Definition *)

  Implicit Type p : peirce.
  Implicit Type ff : falsity_flag.

  Inductive prv : forall (ff : falsity_flag) (p : peirce), list form -> form -> Prop :=
  | II {ff} {p} A phi psi : phi::A ⊢ psi -> A ⊢ phi → psi
  | IE {ff} {p} A phi psi : A ⊢ phi → psi -> A ⊢ phi -> A ⊢ psi
  | AllI {ff} {p} A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
  | AllE {ff} {p} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
  | Exp {p} A phi : prv p A falsity -> prv p A phi
  | Ctx {ff} {p} A phi : phi el A -> A ⊢ phi
  | Pc {ff} A phi psi : prv class A (((phi → psi) → phi) → phi)
  where "A ⊢ phi" := (prv _ A phi).

  Definition tprv `{falsity_flag} `{peirce} (T : form -> Prop) phi :=
    exists A, (forall psi, psi el A -> T psi) /\ A ⊢ phi.
  Definition consistent (p : peirce)  (T : form -> Prop) := ~ tprv T ⊥.

End ND_def.


Local Hint Constructors prv : core.

Arguments prv {_ _ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 30).
Notation "A ⊢C phi" := (@prv _ _ _ class A phi) (at level 30).
Notation "A ⊢I phi" := (@prv _ _ _ intu A phi) (at level 30).
Notation "A ⊢M phi" := (@prv _ _ falsity_off intu A phi) (at level 30).
Notation "T ⊢T phi" := (tprv T phi) (at level 55).
Notation "T ⊢TI phi" := (@tprv _ _ _ intu T phi) (at level 55).
Notation "T ⊢TC phi" := (@tprv _ _ _ class T phi) (at level 55).
Notation "T ⊢TM phi" := (@tprv _ _ falsity_off intu T phi) (at level 30).
