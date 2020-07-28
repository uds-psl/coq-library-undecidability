Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.CounterMachines.CM1.

Require Import Undecidability.PCP.Reductions.HaltTM_to_iPCPb.
Require Import Undecidability.Reductions.BPCP_to_BSM.
Require Import Undecidability.Reductions.BSM_to_MM.
Require Import Undecidability.Reductions.MM_to_FRACTRAN.
Require Import Undecidability.Reductions.FRACTRAN_to_MMA2.
Require Import Undecidability.Reductions.MMA2_to_MM2.
Require Import Undecidability.CounterMachines.Reductions.MM2_HALTING_to_CM1c4_HALT.

(** Many-one reduction from Turing machine halting to 
  one counter machine (with denominators at most 4) halting *)
Lemma HaltTM_to_CM1c4_HALT : HaltTM 1 ⪯ CM1c4_HALT.
Proof.
  apply (reduces_transitive HaltTM_to_iPCPb).
  apply (reduces_transitive iBPCP_BSM_HALTING).
  apply (reduces_transitive BSM_MM_HALTING).
  apply (reduces_transitive MM_FRACTRAN_REG_HALTING).
  apply (reduces_transitive FRACTRAN_REG_MMA2_HALTING).
  apply (reduces_transitive MM_MMA2_HALTING).
  exact MM2_HALTING_to_CM1c4_HALT.reduction.
Qed.
