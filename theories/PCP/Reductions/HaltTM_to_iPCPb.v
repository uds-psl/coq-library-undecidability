Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.PCP.PCP.

Require Import Undecidability.PCP.Reductions.HaltTM_to_PCP.
Require Import Undecidability.PCP.Reductions.PCP_to_PCPb.
Require Import Undecidability.PCP.Reductions.PCPb_iff_iPCPb.

(** Many-one reduction from Turing machine halting to the indexed binary Post correspondence problem *)
Lemma HaltTM_to_iPCPb : HaltTM 1 ⪯ iPCPb.
Proof.
  apply (reduces_transitive HaltTM_to_PCP).
  apply (reduces_transitive PCP_to_PCPb.reduction).
  exact PCPb_iff_iPCPb.reductionLR.
Qed.
