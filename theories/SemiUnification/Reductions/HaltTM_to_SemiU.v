Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.SemiUnification.SemiU.

Require Import Undecidability.StackMachines.Reductions.HaltTM_to_CSSM_UB.
Require Undecidability.SemiUnification.Reductions.CSSM_UB_to_SSemiU.
Require Undecidability.SemiUnification.Reductions.SSemiU_to_SemiU.

(** Many-one reduction from Turing machine halting to semi-unification *)
Lemma HaltTM_to_SemiU : HaltTM 1 ⪯ SemiU.
Proof.
  apply (reduces_transitive HaltTM_to_CSSM_UB).
  apply (reduces_transitive CSSM_UB_to_SSemiU.reduction).
  exact SSemiU_to_SemiU.reduction.
Qed.
