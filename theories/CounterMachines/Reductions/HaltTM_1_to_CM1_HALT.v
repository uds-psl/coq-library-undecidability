(* 
  Reduction from:
    Turing Machine Halting (HaltTM 1)
  to:
    Halting of one counter machines (CM1_HALT)
*)

(** ** HaltTM 1 reduces to CM1_HALT  *)

From Undecidability.Synthetic Require Import Definitions ReducibilityFacts.

Require Import Undecidability.TM.TM.

Require Import Undecidability.FRACTRAN.Reductions.HaltTM_1_to_FRACTRAN_HALTING.

From Undecidability.MinskyMachines
  Require Import FRACTRAN_to_MMA2 MMA2_to_MM2.

From Undecidability.CounterMachines
  Require Import CM1 MM2_HALTING_to_CM1_HALT.

(* Many-one reduction from Turing machine halting to 
  one counter machine halting *)
Theorem reduction : HaltTM 1 ⪯ CM1_HALT.
Proof.
  apply (reduces_transitive HaltTM_to_FRACTRAN_REG_HALTING).
  apply (reduces_transitive FRACTRAN_REG_MMA2_HALTING).
  apply (reduces_transitive MMA2_MM2_HALTING).
  exact MM2_HALTING_to_CM1_HALT.reduction.
Qed.
