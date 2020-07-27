(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Direct reductions from Halting of 1-TM to binary PCP *)

Require Import List.

Import ListNotations.

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.TM.Halting.

From Undecidability.StringRewriting.Reductions
  Require Import TM_to_SRH SRH_to_SR.

From Undecidability.PCP
  Require Import PCP.

From Undecidability.PCP.Reductions
  Require Import SR_to_MPCP MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb.

(* Type hierachy is messed with SR.string, universe inconsistency *)

Local Notation SRHp := (@undec_problem (list (list nat * list nat) * list nat * nat) SR.SRH).
Local Notation SRp := (@undec_problem (list (list nat * list nat) * list nat * list nat) SR.SR).

Lemma HALT_TM1_chain_PCP : ⎩HaltTM 1⎭ ⪯ₗ ⎩PCP⎭ by [⎩singleTM.Halt⎭;
                                              SRHp;
                                              SRp;
                                              ⎩MPCP⎭;
                                              ⎩PCP⎭].
Proof.
  red chain step singleTM.TM_conv.
  red chain step Halt_SRH.
  red chain step SRH_to_SR.reduction.
  red chain step SR_to_MPCP.reduction.
  red chain step MPCP_to_PCP.reduction.
  red chain stop.
Qed.

Lemma PCP_chain_PCPb : ⎩PCP⎭ ⪯ₗ⎩PCPb⎭ by [⎩PCPb⎭].
Proof.
  red chain step PCP_to_PCPb.reduction.
  red chain stop.
Qed.

Lemma PCPb_chain_iPCPb : ⎩PCPb⎭ ⪯ₗ⎩iPCPb⎭ by [⎩iPCPb⎭].
Proof.
  red chain step PCPb_iff_iPCPb.reductionLR.
  red chain stop.
Qed.

Lemma PCP_chain_iPCPb : ⎩PCP⎭ ⪯ₗ⎩iPCPb⎭ by [⎩PCPb⎭;⎩iPCPb⎭].
Proof.
  apply reduction_chain_app with (1 := PCP_chain_PCPb).
  apply PCPb_chain_iPCPb.
Qed.

Lemma HALT_TM1_to_PCP : HaltTM 1 ⪯ PCP.
Proof.
  apply reduction_chain_reduces with (1 := HALT_TM1_chain_PCP).
Qed.

Lemma HALT_TM1_to_PCPb : HaltTM 1 ⪯ PCPb.
Proof.
  eapply reduces_transitive. exact HALT_TM1_to_PCP.
  apply reduction_chain_reduces with (1 := PCP_chain_PCPb).
Qed.

Lemma HALT_TM1_to_iPCPb : HaltTM 1 ⪯ iPCPb.
Proof.
  eapply reduces_transitive. exact HALT_TM1_to_PCP.
  apply reduction_chain_reduces with (1 := PCP_chain_iPCPb).
Qed.
