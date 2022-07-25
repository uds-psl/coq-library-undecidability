From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts NatModel.
From Undecidability.FOL.Syntax Require Import Theories.

(** ** Q-decidability *)
Section Qdec.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {p : peirce}.

  Definition Qdec ϕ := forall ρ, bounded 0 ϕ[ρ] -> Qeq ⊢ ϕ[ρ] \/ Qeq ⊢ ¬ϕ[ρ].
End Qdec.

(** ** Sigma1 completeness *)
Section Sigma1.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {p : peirce}.

  Inductive Σ1 : form -> Prop :=
  | Sigma_exists : forall α, Σ1 α -> Σ1 (∃ α)
  | Sigma_Delta : forall α, Qdec α -> Σ1 α.
  Inductive Π1 : form -> Prop :=
  | Pi_forall : forall α, Π1 α -> Π1 (∀ α)
  | Pi_Delta : forall α, Qdec α -> Π1 α.

  Theorem Σ1_completeness ϕ ρ :
    Σ1 ϕ -> bounded 0 ϕ -> sat interp_nat ρ ϕ -> Qeq ⊢ ϕ.
  Proof.
  Admitted.
End Sigma1.