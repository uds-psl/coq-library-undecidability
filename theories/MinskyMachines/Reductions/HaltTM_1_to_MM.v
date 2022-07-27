(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.

From Undecidability.MinskyMachines Require Import MM MM_sss BSM_MM.
From Undecidability Require
  TM.Reductions.HaltTM_1_to_SBTM_HALT StackMachines.Reductions.SBTM_HALT_to_HaltBSM.

Theorem HaltTM_to_MM_HALTS_ON_ZERO : HaltTM 1 ⪯ MM_HALTS_ON_ZERO.
Proof.
  eapply reduces_transitive. { exact HaltTM_1_to_SBTM_HALT.reduction. }
  eapply reduces_transitive. { exact SBTM_HALT_to_HaltBSM.reduction. }
  red. unfold reduction.
  setoid_rewrite <- BSM_sss.Halt_BSM_iff.
  exact BSM_MM_HALTS_ON_ZERO.
Qed.

Theorem HaltTM_to_MM_HALTING : HaltTM 1 ⪯ Halt_MM.
Proof.
  eapply reduces_transitive. { exact HaltTM_1_to_SBTM_HALT.reduction. }
  eapply reduces_transitive. { exact SBTM_HALT_to_HaltBSM.reduction. }
  red. unfold reduction.
  setoid_rewrite <- BSM_sss.Halt_BSM_iff.
  exact BSM_MM_HALTING.
Qed.
