(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Undecidability.Synthetic.Definitions.

From Undecidability.Shared.Libs.DLW 
  Require Import pos vec sss.

From Undecidability.MinskyMachines
  Require Import MM.

From Undecidability.MuRec 
  Require Import recalg ra_simul.

Set Default Proof Using "Type".

Local Notation "'⟦' f '⟧'"  := (@ra_rel _ f) (at level 0).
Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).

Section MUREC_MM_HALTING.

 Let f : MUREC_PROBLEM -> MM_PROBLEM.
  Proof.
    intros g.
    destruct (ra_mm_simulator g) as (m & P & _).
    exists (S m), P; apply vec_zero.
  Defined.

  Theorem MUREC_MM_HALTING : MUREC_HALTING ⪯ MM_HALTING.
  Proof.
    exists f; unfold f.
    intros g; simpl; unfold MUREC_HALTING, MM_HALTING.
    destruct (ra_mm_simulator g) as (m & P & H); simpl.
    rewrite H, vec_app_nil; tauto.
  Qed.

End MUREC_MM_HALTING.

(* Check MUREC_MM_HALTING. *)
(* Print Assumptions MUREC_MM_HALTING. *)
