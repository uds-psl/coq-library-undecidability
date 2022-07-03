(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.
Import ListNotations.

Require Import Undecidability.Synthetic.Definitions.

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec subcode sss.

From Undecidability.StackMachines.BSM 
  Require Import tiles_solvable bsm_defs bsm_utils bsm_pcp.

From Undecidability.PCP 
  Require Import PCP PCP_facts.

Fact tile_concat_itau ln lt : tile_concat ln lt = (itau1 lt (rev ln), itau2 lt (rev ln)).
Proof.
  induction ln as [ | i ln IH ]; simpl; auto.
  rewrite itau1_app, itau2_app; simpl.
  generalize (nth i lt ([], [])); intros (a,b); rewrite IH.
  repeat rewrite <- app_nil_end; auto.
Qed.

(* tiles_solvable & iBPCP is the same predicate except that the existentially
   quantified list is reversed *)

Theorem tiles_solvable_iBPCP lt : tiles_solvable lt <-> iPCPb lt.
Proof.
  split.
  + intros (ln & H1 & H2 & H3).
    rewrite tile_concat_itau in H3.
    exists (rev ln). 
    rewrite <- Forall_forall.
    repeat split; auto.
    * apply Forall_rev; auto.
    * contradict H1; rewrite <- (rev_involutive ln), H1; auto.
  + intros (ln & H1 & H2 & H3).
    exists (rev ln).
    rewrite tile_concat_itau, rev_involutive.
    repeat split; auto.
    * contradict H2; rewrite <- (rev_involutive ln), H2; auto.
    * apply Forall_rev, Forall_forall; auto.
Qed.

Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@bsm_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@bsm_sss _) P s). 

Section iPCPb_to_BSM_HALTING.

  Let f (lt : list (card bool)) : BSM_PROBLEM.
  Proof.
    exists 4, 1, (pcp_bsm lt).
    exact (vec_set_pos (fun _ => nil)).
  Defined.

  Goal forall x, length(pcp_bsm x) >= 80.
  Proof.
    intros; rewrite pcp_bsm_size; lia.
  Qed.
  
  Theorem iPCPb_to_BSM_HALTING : iPCPb ⪯ Halt_BSM.
  Proof.
    exists f.
    intros lt.
    rewrite <- tiles_solvable_iBPCP.
    rewrite Halt_BSM_iff.
    unfold BSM_HALTING; split.
    * intros H.
      apply pcp_bsm_sound with (v := vec_set_pos (fun _ => nil)) in H.
      match type of H with  _ // _ ->> (?q,?w) => exists (q, w) end.
      split; auto.
      simpl; lia.
    * intros ((q & w) & H).
      apply pcp_bsm_complete in H; tauto.
  Qed.

End iPCPb_to_BSM_HALTING.
