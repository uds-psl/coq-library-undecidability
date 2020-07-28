(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Results(s):
    One Counter Machine Halting (CM1_HALT)
    One Counter Machine with Bounded Instructions Halting (CM1c4_HALT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Reductions.MM2_HALTING_to_CM1c4_HALT.

Require Import Undecidability.Reductions.BPCP_to_BSM.
Require Import Undecidability.Reductions.BSM_to_MM.
Require Import Undecidability.Reductions.MM_to_FRACTRAN.
Require Import Undecidability.Reductions.FRACTRAN_to_MMA2.
Require Import Undecidability.Reductions.MMA2_to_MM2.
Require Import Undecidability.PCP.PCP_undec.

(** Undecidability of The One Counter Machine (with Denominators at most 4) Halting Problem *)
Lemma CM1c4_HALT_undec : undecidable CM1c4_HALT.
Proof.
  apply (undecidability_from_reducibility iPCPb_undec).
  apply (reduces_transitive iBPCP_BSM_HALTING).
  apply (reduces_transitive BSM_MM_HALTING).
  apply (reduces_transitive MM_FRACTRAN_REG_HALTING).
  apply (reduces_transitive FRACTRAN_REG_MMA2_HALTING).
  apply (reduces_transitive MMA2_MM2_HALTING).
  exact MM2_HALTING_to_CM1c4_HALT.reduction.
Qed.

Check CM1c4_HALT_undec.

(** Undecidability of The One Counter Machine Halting Problem *)
Lemma CM1_HALT_undec : undecidable CM1_HALT.
Proof.
  apply (undecidability_from_reducibility CM1c4_HALT_undec).
  now exists (fun M => proj1_sig M).
Qed.

Check CM1_HALT_undec.
