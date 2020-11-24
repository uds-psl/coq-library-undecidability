Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.
Require Import Undecidability.PCP.PCP.

Require Undecidability.StringRewriting.Reductions.HaltTM_1_to_SR.
Require Import Undecidability.PCP.Reductions.SR_to_MPCP.
Require Import Undecidability.PCP.Reductions.MPCP_to_PCP.

(** ** HaltTM 1 reduces to PCP *)

(* Many-one reduction from Turing machine halting to the Post correspondence problem *)
Lemma reduction : HaltTM 1 ⪯ PCP.
Proof.
  apply (reduces_transitive HaltTM_1_to_SR.reduction).
  apply (reduces_transitive SR_to_MPCP.reduction).
  exact MPCP_to_PCP.reduction.
Qed.
