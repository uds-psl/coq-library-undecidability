Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.SemiUnification.SemiU. (* SSemiU, SSemiU, RU2SemiU *)
Require Import Undecidability.StackMachines.SSM. (* CSSM_UB *)
Require Import Undecidability.StackMachines.SMN. (* SMNdl_UB *)
Require Import Undecidability.CounterMachines.CM1. (* CM1_HALT *)
Require Import Undecidability.MinskyMachines.MM2. (* MM2_HALTING *)
Require Import Undecidability.StackMachines.BSM. (* BSM_HALTING *)
Require Import Undecidability.PCP.PCP. (* iPCPb *)
Require Import Undecidability.TM.TM. (* HaltTM 1 *)

Require Undecidability.SemiUnification.Reductions.RU2SemiU_to_SemiU.
Require Undecidability.SemiUnification.Reductions.SSemiU_to_RU2SemiU.
Require Undecidability.SemiUnification.Reductions.CSSM_UB_to_SSemiU.
Require Undecidability.StackMachines.Reductions.SMNdl_UB_to_CSSM_UB.
Require Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.
Require Undecidability.CounterMachines.Reductions.MM2_HALTING_to_CM1_HALT.
Require Undecidability.MinskyMachines.Reductions.BSM_HALTING_to_MM2_HALTING.
Require Undecidability.StackMachines.Reductions.iPCPb_to_BSM_HALTING.
Require Undecidability.PCP.Reductions.HaltTM_1_to_iPCPb.

(* 
  Comprehensive chain of many-one reductions from Turing machine halting to semi-unification 
    HaltTM 1 : Turing machine halting
    iPCPb : indexed, binary Post correspondence problem
    BSM_HALTING : binary stack machine halting
    MM2_HALTING : Minsky machine (with 2 registers) halting
    CM1_HALT : one-counter machine halting
    SMNdl_UB : uniform boundedness of deterministic, length-preserving stack machines
    CSSM_UB : uniform boundedness of confluent, simple stack machines
    SSemiU : simple semi-unification
    RU2SemiU : right-uniform, two-inequality semi-unification
    SemiU : semi-unification
*)
Theorem HaltTM_1_chain_SemiU : 
  HaltTM 1 ⪯ iPCPb /\
  iPCPb ⪯ BSM_HALTING /\
  BSM_HALTING ⪯ MM2_HALTING /\
  MM2_HALTING ⪯ CM1_HALT /\
  CM1_HALT ⪯ SMNdl_UB /\
  SMNdl_UB ⪯ CSSM_UB /\
  CSSM_UB ⪯ SSemiU /\
  SSemiU ⪯ RU2SemiU /\
  RU2SemiU ⪯ SemiU.
Proof.
  constructor. { exact HaltTM_1_to_iPCPb.reduction. }
  constructor. { exact iPCPb_to_BSM_HALTING.iPCPb_to_BSM_HALTING. }
  constructor. { exact BSM_HALTING_to_MM2_HALTING.reduction. } 
  constructor. { exact MM2_HALTING_to_CM1_HALT.reduction. }
  constructor. { exact CM1_HALT_to_SMNdl_UB.reduction. }
  constructor. { exact SMNdl_UB_to_CSSM_UB.reduction. }
  constructor. { exact CSSM_UB_to_SSemiU.reduction. }
  constructor. { exact SSemiU_to_RU2SemiU.reduction. }
  exact RU2SemiU_to_SemiU.reduction.
Qed.
