(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Results(s):
    Two Counter Machine Halting (CM2_HALT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.CounterMachines.CM2.
Require Import Undecidability.CounterMachines.Reductions.MM2_HALTING_to_CM2_HALT.

Require Import Undecidability.Reductions.BPCP_to_BSM.
Require Import Undecidability.Reductions.BSM_to_MM.
Require Import Undecidability.Reductions.MM_to_FRACTRAN.
Require Import Undecidability.Reductions.FRACTRAN_to_MMA2.
Require Import Undecidability.Reductions.MMA2_to_MM2.
Require Import Undecidability.PCP.PCP_undec.

(** Undecidability of The Two Counter Machine Halting Problem *)
Lemma CM2_HALT_undec : undecidable CM2_HALT.
Proof.
  apply (undecidability_from_reducibility iPCPb_undec).
  apply (reduces_transitive iBPCP_BSM_HALTING).
  apply (reduces_transitive BSM_MM_HALTING).
  apply (reduces_transitive MM_FRACTRAN_REG_HALTING).
  apply (reduces_transitive FRACTRAN_REG_MMA2_HALTING).
  apply (reduces_transitive MM_MMA2_HALTING).
  exact MM2_HALTING_to_CM2_HALT.reduction.
Qed.

Check CM2_HALT_undec.
