Require Import List.
Import ListNotations.

Require Import Undecidability.CFG.CFP.
Require Import Undecidability.CFG.CFG.
Require Undecidability.CFG.Reductions.CFPP_to_CFP.

Require Import Undecidability.Shared.Prelim.
Require Import Undecidability.Problems.Reduction.

Lemma reduction :
  CFPI ⪯ CFI.
Proof.
  exists (fun '(R1, R2, a) => (CFPP_to_CFP.G R1 a, CFPP_to_CFP.G R2 a)). intros [[R1 R2] a].
  intuition; cbn in *.
  - destruct H as (A1 & A2 & HR1 & HR2 & HA1 & HA2 & H).
    exists (sigma a A1). split; eapply CFPP_to_CFP.reduction_full; eauto.
  - destruct H as (x & HR1 & HR2).
    eapply CFPP_to_CFP.reduction_full in HR1 as (A1 & HR1 & HA1 & H1).
    eapply CFPP_to_CFP.reduction_full in HR2 as (A2 & HR2 & HA2 & H2).
    exists A1, A2. subst; eauto.
Qed.
