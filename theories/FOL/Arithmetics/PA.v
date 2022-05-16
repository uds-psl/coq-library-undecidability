(** * Peano Arithmetic *)
(* ** Axioms of PA *)
Require Export Undecidability.FOL.Arithmetics.Robinson.
Import Vector.VectorNotations.
Require Import List.

Definition ax_induction (phi : form) :=
  phi[zero..] → (∀ phi → phi[σ $0 .: S >> var]) → ∀ phi.

(* Full axiomatisation of the theory of PA *)
Inductive PA : form -> Prop :=
  PA_FA phi : In phi FA -> PA phi
| PA_discr : PA ax_zero_succ
| PA_inj : PA ax_succ_inj
| PA_induction phi : PA (ax_induction phi).


Inductive PAeq : form -> Prop :=
  PAeq_FA phi : In phi FAeq -> PAeq phi
| PAeq_discr : PAeq ax_zero_succ
| PAeq_inj : PAeq ax_succ_inj
| PAeq_induction phi : PAeq (ax_induction phi).
