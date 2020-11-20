(* 
  Reduction from:
    Turing Machine Halting (HaltTM 1)
  to:
    System F Type Checking (SysF_TYP)
*)

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.
Require Import Undecidability.SystemF.SysF.

Require Undecidability.SystemF.Reductions.HaltTM_1_to_SysF_TYP.
Require Undecidability.SystemF.Reductions.SysF_TYP_to_SysF_TC.

(** Many-one reduction from Turing machine halting to System F type checking *)
Theorem reduction : HaltTM 1 ⪯ SysF_TC.
Proof.
  apply (reduces_transitive HaltTM_1_to_SysF_TYP.reduction).
  exact SysF_TYP_to_SysF_TC.reduction.
Qed.
