Require Import Undecidability.Synthetic.Definitions.

From Undecidability.PCP
  Require Import PCP Util.Facts PCPX_iff_dPCP.

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
