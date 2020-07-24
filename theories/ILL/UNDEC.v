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

From Undecidability Require Import ILL.Definitions.
From Undecidability.BinaryStackMachines  Require Import BSM BSM_undec.
From Undecidability.MinskyMachines       Require Import mm_defs.
From Undecidability.ILL.Ll               Require Import eill ill.

From Undecidability.ILL Require Import BSM_MM MM_EILL EILL_ILL.

Require Import Undecidability.Synthetic.Undecidability.

Check BSM_MM_HALTS_ON_ZERO.
Check BSM_MM_HALTING.

Theorem EILL_undec : undecidable EILL_PROVABILITY.
Proof.
  apply (undecidability_from_reducibility BSM_undec).
  eapply reduces_transitive. exact BSM_MM_HALTS_ON_ZERO.
  exact MM_HALTS_ON_ZERO_EILL_PROVABILITY.
Qed.

Theorem ILL_undec : undecidable ILL_PROVABILITY.
Proof.
  apply (undecidability_from_reducibility EILL_undec).
  exact EILL_ILL_PROVABILITY.
Qed.
