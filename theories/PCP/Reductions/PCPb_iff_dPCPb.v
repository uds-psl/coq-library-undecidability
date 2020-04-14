Require Import List.
Import ListNotations.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Reductions.PCPX_iff_dPCP.

Require Import Undecidability.Problems.Reduction.

Require Import Undecidability.Shared.Prelim.

Lemma PCPb_iff_dPCPb P : PCPb P <-> dPCPb P.
Proof. apply PCPX_iff_dPCP. Qed.

Lemma reductionLR : PCPb ⪯ dPCPb.
Proof.
  exists id. exact PCPb_iff_dPCPb.
Qed.

Lemma reductionRL : dPCPb ⪯ PCPb.
Proof.
  exists id. intro. now rewrite PCPb_iff_dPCPb.
Qed.
