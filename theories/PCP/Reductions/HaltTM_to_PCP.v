Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.PCP.PCP.

Require Import Undecidability.StringRewriting.Reductions.HaltTM_to_SR.
Require Import Undecidability.PCP.Reductions.SR_to_MPCP.
Require Import Undecidability.PCP.Reductions.MPCP_to_PCP.

(** Many-one reduction from Turing machine halting to the Post correspondence problem *)
Lemma HaltTM_to_PCP : HaltTM 1 ⪯ PCP.
Proof.
  apply (reduces_transitive HaltTM_to_SR).
  apply (reduces_transitive SR_to_MPCP.reduction).
  exact MPCP_to_PCP.reduction.
Qed.
