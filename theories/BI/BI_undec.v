(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.MinskyMachines
  Require Import ACM2 ACM2_undec.

From Undecidability.BI
  Require Import BI.

From Undecidability
  Require ACM2_to_BI.

(** The Logic of Bunched Implications is undecidable *)

Lemma BI_undec : undecidable (@BI_SEQ_PROVABLE_cut_free nat).
Proof.
  apply (undecidability_from_reducibility ACM2_undec).
  apply ACM2_to_BI.reduction.
Qed.

Check BI_undec.
