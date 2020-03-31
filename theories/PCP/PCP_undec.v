Require Import Undecidability.PCP.PCP.

From Undecidability.PCP.Reductions Require 
  SR_to_MPCP MPCP_to_MPCPb MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb PCPb_iff_dPCPb.

Require Import Undecidability.Problems.TM.
Require Import Undecidability.Problems.Reduction.

Require Undecidability.SR.SR_undec.

(** The modified Post correspondence problem is undecidable. *)
Lemma MPCP_undec : HaltTM 1 ⪯ MPCP.
Proof.
  eapply reduces_transitive.
  exact SR_undec.SR_undec.
  exact SR_to_MPCP.reduction.
Qed.

Check MPCP_undec.

(** The modified Post correspondence problem restricted to binary strings is undecidable. *)
Lemma MPCPb_undec : HaltTM 1 ⪯ MPCPb.
Proof.
  eapply reduces_transitive.
  exact MPCP_undec.
  exact MPCP_to_MPCPb.reduction.
Qed.

Check MPCPb_undec.

(** The Post correspondence problem is undecidable. *)
Lemma PCP_undec : HaltTM 1 ⪯ PCP.
Proof.
  eapply reduces_transitive.
  exact MPCP_undec.
  exact MPCP_to_PCP.reduction.
Qed.

Check PCP_undec.

(** The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma PCPb_undec : HaltTM 1 ⪯ PCPb.
Proof.
  eapply reduces_transitive.
  exact PCP_undec.
  exact PCP_to_PCPb.reduction.
Qed.

Check PCPb_undec.

(** The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma iPCPb_undec : HaltTM 1 ⪯ iPCPb.
Proof.
  eapply reduces_transitive.
  exact PCPb_undec.
  exists id. exact PCPb_iff_iPCPb.PCPb_iff_iPCPb.
Qed.

Check iPCPb_undec.

(** The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma dPCPb_undec : HaltTM 1 ⪯ dPCPb.
Proof.
  eapply reduces_transitive.
  exact PCPb_undec.
  exists id. exact PCPb_iff_dPCPb.PCPb_iff_dPCPb.
Qed.

Check dPCPb_undec.
