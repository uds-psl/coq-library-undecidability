Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.MinskyMachines.MM2. (* MM2_HALTING *)
Require Import Undecidability.StackMachines.BSM. (* BSM_HALTING *)

Require Undecidability.MinskyMachines.Reductions.BSM_MM.
Require Undecidability.FRACTRAN.Reductions.MM_FRACTRAN.
Require Undecidability.MinskyMachines.Reductions.FRACTRAN_to_MMA2.
Require Undecidability.MinskyMachines.Reductions.MMA2_to_MM2.

(** Many-one reduction from binary stack machine halting to 
    two counters Minsky machine halting *)
Theorem reduction : BSM_HALTING ⪯ MM2_HALTING.
Proof.
  apply (reduces_transitive BSM_MM.BSM_MM_HALTING).
  apply (reduces_transitive MM_FRACTRAN.MM_FRACTRAN_REG_HALTING).
  apply (reduces_transitive FRACTRAN_to_MMA2.FRACTRAN_REG_MMA2_HALTING).
  exact MMA2_to_MM2.MMA2_MM2_HALTING.
Qed.
