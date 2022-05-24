(** ** Natural Deduction *)

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
From Undecidability Require Import FOL.Syntax.Core.
Import FullSyntax.
Export FullSyntax.

Local Set Implicit Arguments.
Section FullSequent.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Inductive fprv : list form -> form -> Prop :=
    (* Structural Rules *)
  | Ax A phi : fprv (phi :: A) phi
  | Contr A phi psi : fprv (phi :: phi :: A) psi -> fprv (phi :: A) psi
  | Weak A phi psi : fprv A psi -> fprv (phi :: A) psi
  | Perm A A' phi psi chi : fprv (A ++ psi :: phi :: A') chi -> fprv (A ++ phi :: psi :: A') chi
    (* Logical rules *)
  | Exp A phi : fprv A ⊥ -> fprv A phi
  | IL A phi psi chi : fprv A phi -> fprv (psi :: A) chi -> fprv (phi → psi :: A) chi
  | IR A phi psi : fprv (phi :: A) psi -> fprv A (phi → psi)
  | AL A phi psi chi : fprv (phi :: psi :: A) chi -> fprv ((phi ∧ psi) :: A) chi
  | AR A phi psi : fprv A phi -> fprv A psi -> fprv A (phi ∧ psi)
  | OL A phi psi chi : fprv (phi :: A) chi -> fprv (psi :: A) chi -> fprv ((phi ∨ psi) :: A) chi
  | OR1 A phi psi : fprv A phi -> fprv A (phi ∨ psi)
  | OR2 A phi psi : fprv A psi -> fprv A (phi ∨ psi)
  | AllL A phi psi t : fprv (phi [t ..] :: A) psi -> fprv (∀ phi :: A) psi
  | AllR A phi : fprv (map (subst_form ↑) A) phi -> fprv A (∀ phi)
  | ExL A phi psi : fprv (phi :: map (subst_form ↑) A) (subst_form ↑ psi) -> fprv (∃ phi :: A) psi
  | ExR A phi t : fprv A (phi [t..]) -> fprv A (∃ phi).

  Definition tfprv (T : form -> Prop) phi :=
    exists A, (forall psi, psi el A -> T psi) /\ fprv A phi.

End FullSequent.

Arguments ExR {_} {_} {A} {phi} t.
Arguments AllL {_} {_} {A} {phi} {psi} t.
#[global] Hint Constructors fprv : core.
#[global] Notation "A ⊢f phi" := (fprv A phi) (at level 30).
