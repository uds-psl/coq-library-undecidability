(* ** Natural Deduction *)

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
From Undecidability Require Import FOL.Util.Syntax.
Import FullSyntax.

Local Set Implicit Arguments.

Inductive peirce := class | intu.
Existing Class peirce.

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Reserved Notation "A ⊢ phi" (at level 61).
  
  (* ** Definition *)

  Implicit Type p : peirce.
  Implicit Type ff : falsity_flag.

  Inductive prv : forall (ff : falsity_flag) (p : peirce), list form -> form -> Prop :=
  | II {ff} {p} A phi psi : phi::A ⊢ psi -> A ⊢ phi ~> psi
  | IE {ff} {p} A phi psi : A ⊢ phi ~> psi -> A ⊢ phi -> A ⊢ psi
  | AllI {ff} {p} A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
  | AllE {ff} {p} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
  | ExI {ff} {p} A t phi : A ⊢ phi[t..] -> A ⊢ ∃ phi
  | ExE {ff} {p} A phi psi : A ⊢ ∃ phi -> phi::(map (subst_form ↑) A) ⊢ psi[↑] -> A ⊢ psi
  | Exp {p} A phi : prv p A falsity -> prv p A phi
  | Ctx {ff} {p} A phi : phi el A -> A ⊢ phi
  | CI {ff} {p} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 {ff} {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 {ff} {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
  | DI1 {ff} {p} A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
  | DI2 {ff} {p} A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
  | DE {ff} {p} A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
  | Pc {ff} A phi psi : prv class A (((phi ~> psi) ~> phi) ~> phi)
  where "A ⊢ phi" := (prv _ A phi).

  Definition tprv `{falsity_flag} `{peirce} (T : form -> Prop) phi :=
    exists A, (forall psi, psi el A -> T psi) /\ A ⊢ phi.

End ND_def.

Arguments prv {_ _ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 55).
Notation "A ⊢C phi" := (@prv _ _ _ class A phi) (at level 55).
Notation "A ⊢I phi" := (@prv _ _ _ intu A phi) (at level 55).
Notation "A ⊢M phi" := (@prv _ _ falsity_off intu A phi) (at level 55).
Notation "T ⊢T phi" := (tprv T phi) (at level 55).
Notation "T ⊢TI phi" := (@tprv _ _ _ intu T phi) (at level 55).
Notation "T ⊢TC phi" := (@tprv _ _ _ class T phi) (at level 55).


