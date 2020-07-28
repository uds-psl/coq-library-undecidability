Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.ILL.Mm.mm_defs.

Require Import Undecidability.PCP.Reductions.HaltTM_to_PCP.
Require Import Undecidability.ILL.UNDEC.

(** Many-one reduction from Turing machine halting to Minsky machine halting *)
Lemma HaltTM_to_MM_HALTING : HaltTM 1 ⪯ MM_HALTING.
Proof.
  apply (reduces_transitive HaltTM_to_PCP).
  exact PCP_MM_HALTING.
Qed.
