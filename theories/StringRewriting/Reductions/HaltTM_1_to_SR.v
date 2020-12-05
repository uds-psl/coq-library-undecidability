Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.
Require Import Undecidability.TM.SBTM.
Require Import Undecidability.StringRewriting.SR.

Require Undecidability.TM.Reductions.HaltTM_1_to_HaltSBTM Undecidability.TM.Reductions.HaltSBTM_to_HaltSBTMu.

From Undecidability.StringRewriting.Reductions Require HaltSBTMu_to_SRH SRH_to_SR.

(* Many-one reduction from Turing machine halting to string rewriting *)
Theorem reduction : HaltTM 1 ⪯ SR.
Proof.
  apply (reduces_transitive HaltTM_1_to_HaltSBTM.reduction).
  apply (reduces_transitive HaltSBTM_to_HaltSBTMu.reduction).
  apply (reduces_transitive HaltSBTMu_to_SRH.reduction).
  exact SRH_to_SR.reduction.
Qed.
