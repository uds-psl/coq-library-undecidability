(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
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

Notation "p '⪯c' q 'by' l" := (@reduction_chain _ _ p q l) (at level 70).

(*
Check singleTM.TM_conv.
Check Halt_SRH.
Check SRH_to_SR.reduction.
Check SR_to_MPCP.reduction.

Check SR.SRH.

Lemma HALT_TM1_chain_PCP : HaltTM 1 ⪯c PCP by [⎩singleTM.Halt⎭;
                                              ⎩SR.SRH⎭;
                                              ⎩SR.SR⎭;
                                              ⎩MPCP⎭;
                                              ⎩PCP⎭].
*)

Lemma HALT_TM1_to_PCP : HaltTM 1 ⪯ PCP.
Proof.
  eapply reduces_transitive. exact singleTM.TM_conv.
  eapply reduces_transitive. exact Halt_SRH.
  eapply reduces_transitive. exact SRH_to_SR.reduction.
  eapply reduces_transitive. exact SR_to_MPCP.reduction.
  exact MPCP_to_PCP.reduction.
Qed.

Lemma HALT_TM1_to_PCPb : HaltTM 1 ⪯ PCPb.
Proof.
  eapply reduces_transitive. exact HALT_TM1_to_PCP.
  exact PCP_to_PCPb.reduction.
Qed.

Lemma HALT_TM1_to_iPCPb : HaltTM 1 ⪯ iPCPb.
Proof.
  eapply reduces_transitive. exact HALT_TM1_to_PCPb.
  exact PCPb_iff_iPCPb.reductionLR.
Qed.
