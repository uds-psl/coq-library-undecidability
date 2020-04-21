Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.PCP.Reductions Require 
  SR_to_MPCP MPCP_to_MPCPb MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb PCPb_iff_dPCPb.

Require Import Undecidability.Problems.TM.
Require Import Undecidability.Problems.Reduction.

Require Undecidability.SR.SR_undec.

(** The modified Post correspondence problem is undecidable. *)
Lemma MPCP_undec : undecidable MPCP.
Proof.
  eapply undecidability_from_reducibility.
  eapply undecidability_HaltTM.
  eapply reduces_transitive.
  exact SR_undec.SR_undec.
  exact SR_to_MPCP.reduction.
Qed.

Check MPCP_undec.

(** The modified Post correspondence problem restricted to binary strings is undecidable. *)
Lemma MPCPb_undec : undecidable MPCPb.
Proof.
  eapply undecidability_from_reducibility.
  eapply MPCP_undec.
  exact MPCP_to_MPCPb.reduction.
Qed.

Check MPCPb_undec.

(** The Post correspondence problem is undecidable. *)
Lemma PCP_undec : undecidable PCP.
Proof.
  eapply undecidability_from_reducibility.
  exact MPCP_undec.
  exact MPCP_to_PCP.reduction.
Qed.

Check PCP_undec.

(** The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma PCPb_undec : undecidable PCPb.
Proof.
  eapply undecidability_from_reducibility.
  exact PCP_undec.
  exact PCP_to_PCPb.reduction.
Qed.

Check PCPb_undec.

(** The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma iPCPb_undec : undecidable iPCPb.
Proof.
  eapply undecidability_from_reducibility.
  exact PCPb_undec.
  exists id. exact PCPb_iff_iPCPb.PCPb_iff_iPCPb.
Qed.

Check iPCPb_undec.

(** The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma dPCPb_undec : undecidable dPCPb.
Proof.
  eapply undecidability_from_reducibility.
  exact PCPb_undec.
  exists id. exact PCPb_iff_dPCPb.PCPb_iff_dPCPb.
Qed.

Check dPCPb_undec.
