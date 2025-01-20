(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW
  Require Import utils_tac utils_nat pos vec sss.

From Undecidability.MinskyMachines 
  Require Import mm_defs.

From Undecidability.MuRec.Util 
  Require Import recalg ra_mm.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Local Notation "P // s -+> t" := (sss_progress (@mm_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@mm_sss _) P s t).
Local Notation "P // s ↓"     := (sss_terminates (@mm_sss _) P s).

Theorem ra_mm_simulator n (f : recalg n) :
      { m & { P : list (mm_instr (pos (n+S m))) | forall v, ex (⟦f⟧ v) <-> (1,P) // (1,vec_app v vec_zero) ↓ } }.
Proof.
  destruct (ra_mm_compiler f) as (m & P & H1 & H2).
  exists m, P; split.
  + intros (x & Hx).
    exists (1+length P,vec_app v (x##vec_zero)); split; auto.
    simpl; lia.
  + intros H; apply H2; eq goal H; do 2 f_equal.
Qed.

Corollary ra_mm_simulator_0 (f : recalg 0) :
      { m & { P : list (mm_instr (pos (S m))) | ex (⟦f⟧ vec_nil) <-> (1,P) // (1,vec_zero) ↓ } }.
Proof.
  destruct (ra_mm_simulator f) as (m & P & HP).
  exists m, P; rewrite (HP vec_nil), vec_app_nil; tauto.
Qed.
