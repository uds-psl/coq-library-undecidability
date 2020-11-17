(* 
  Reduction from:
    Turing Machine Halting (HaltTM 1)
  to:
    Semi-unification (SemiU)
*)

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.
Require Import Undecidability.SemiUnification.SemiU.

Require Undecidability.StackMachines.Reductions.HaltTM_1_to_CSSM_UB.
Require Undecidability.SemiUnification.Reductions.CSSM_UB_to_SSemiU.
Require Undecidability.SemiUnification.Reductions.SSemiU_to_RU2SemiU.
Require Undecidability.SemiUnification.Reductions.RU2SemiU_to_SemiU.

(** Many-one reduction from Turing machine halting to semi-unification *)
Theorem reduction : HaltTM 1 ⪯ SemiU.
Proof.
  apply (reduces_transitive HaltTM_1_to_CSSM_UB.reduction).
  apply (reduces_transitive CSSM_UB_to_SSemiU.reduction).
  apply (reduces_transitive SSemiU_to_RU2SemiU.reduction).
  exact RU2SemiU_to_SemiU.reduction.
Qed.
