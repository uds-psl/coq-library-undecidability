(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Synthetic
  Require Import Undecidability ReducibilityFacts.

From Undecidability.Shared.Libs.DLW 
  Require Import pos sss.

From Undecidability.TM 
  Require Import SBTM PCTM pctm_sbtm.

Set Implicit Arguments.

Set Default Proof Using "Type".

Theorem SBTM_PCTM_reduction : SBTM_HALT ⪯ PCTM_HALT.
Proof.
  apply reduces_dependent; exists.
  intros (M,(i,t)).
  exists (sbtm2pctm M i,t); split.
  + intros (k & Hk).
    apply sbtm2pctm_sound in Hk as (t' & Ht').
    exists (0,t'); split; auto; left; auto.
  + apply sbtm2pctm_complete.
Qed.


