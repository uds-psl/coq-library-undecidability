(* 
  Reduction from:
    Turing Machine Halting (HaltTM 1)
  to:
    System F Typability (SysF_TYP)
*)

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.
Require Import Undecidability.SystemF.SysF.

Require Undecidability.StackMachines.Reductions.HaltTM_1_to_CSSM_UB.
Require Undecidability.SemiUnification.Reductions.CSSM_UB_to_SSemiU.
Require Undecidability.SemiUnification.Reductions.SSemiU_to_RU2SemiU.
Require Undecidability.SemiUnification.Reductions.RU2SemiU_to_LU2SemiU.

Require Undecidability.SystemF.Reductions.LU2SemiU_to_SysF_TYP.

(** Many-one reduction from Turing machine halting to System F typability*)
Theorem reduction : HaltTM 1 ⪯ SysF_TYP.
Proof.
  apply (reduces_transitive HaltTM_1_to_CSSM_UB.reduction).
  apply (reduces_transitive CSSM_UB_to_SSemiU.reduction).
  apply (reduces_transitive SSemiU_to_RU2SemiU.reduction).
  apply (reduces_transitive RU2SemiU_to_LU2SemiU.reduction).
  exact LU2SemiU_to_SysF_TYP.reduction.
Qed.
