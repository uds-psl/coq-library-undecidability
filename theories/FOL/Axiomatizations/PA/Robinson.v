(** * Peano Arithmetic *)
(* ** Axioms of Robinson Arithmetic *)
Require Export Undecidability.FOL.Axiomatizations.PA.FA.
Import Vector.VectorNotations.
Require Import List.

Definition ax_zero_succ := ∀  (zero == σ var 0 → falsity).
Definition ax_succ_inj :=  ∀∀ (σ $1 == σ $0 → $1 == $0).

(* Robinson Arithmetic *)
Definition ax_cases := ∀ $0 == zero ∨ ∃ $1 == σ $0.
Definition Q := FA ++ (ax_zero_succ::ax_succ_inj::ax_cases::nil).
Definition Qeq :=
  EQ ++ Q.