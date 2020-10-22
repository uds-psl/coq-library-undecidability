Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.
Require Import Undecidability.StackMachines.SSM.

Require Undecidability.CounterMachines.Reductions.HaltTM_1_to_CM1c4_HALT.
Require Undecidability.StackMachines.Reductions.CM1c4_HALT_to_SMNdl_UB.
Require Undecidability.StackMachines.Reductions.SMNdl_UB_to_CSSM_UB.

(** Many-one reduction from Turing machine halting to 
  uniform boundedness of confluent simple stack machines *)
Theorem reduction : HaltTM 1 ⪯ CSSM_UB.
Proof.
  apply (reduces_transitive HaltTM_1_to_CM1c4_HALT.reduction).
  apply (reduces_transitive CM1c4_HALT_to_SMNdl_UB.reduction).
  exact SMNdl_UB_to_CSSM_UB.reduction.
Qed.
