(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

From Undecidability.Shared.Libs.DLW 
  Require Import pos sss.

From Undecidability.TM 
  Require Import SBTM PCTM pctm_sbtm.

Set Default Goal Selector "!".
Set Implicit Arguments.

Theorem reduction : SBTM_HALT ⪯ PCTM_HALT.
Proof.
  apply reduces_dependent; exists.
  intros (M,(i,t)).
  exists (sbtm2pctm M i,t); split.
  + intros (k & Hk).
    apply sbtm2pctm_sound in Hk as (t' & Ht').
    exists (0,t'); split; auto; left; auto.
  + apply sbtm2pctm_complete.
Qed.
