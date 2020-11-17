(* 
  Reduction from:
    Turing Machine Halting (HaltTM 1)
  to:
    System F Inhabitation (SysF_INH)
*)

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.
Require Import Undecidability.SystemF.SysF.

Require Undecidability.FRACTRAN.Reductions.HaltTM_1_to_FRACTRAN_HALTING.
Require Undecidability.DiophantineConstraints.Reductions.FRACTRAN_to_H10C_SAT.
Require Undecidability.SystemF.Reductions.H10C_SAT_to_SysF_INH.

(** Many-one reduction from Turing machine halting to System F inhabitation*)
Theorem reduction : HaltTM 1 ⪯ SysF_INH.
Proof.
  apply (reduces_transitive HaltTM_1_to_FRACTRAN_HALTING.HaltTM_to_FRACTRAN_HALTING).
  apply (reduces_transitive FRACTRAN_DIO.FRACTRAN_HALTING_DIO_LOGIC_SAT).
  apply (reduces_transitive FRACTRAN_DIO.DIO_LOGIC_ELEM_SAT).
  apply (reduces_transitive FRACTRAN_to_H10C_SAT.DIO_ELEM_H10C_SAT).
  exact H10C_SAT_to_SysF_INH.reduction.
Qed.
