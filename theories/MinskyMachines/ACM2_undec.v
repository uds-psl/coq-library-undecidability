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
  Require Import ndMM2 ndMM2_undec ACM2.

From Undecidability.MinskyMachines
  Require ndMM2_to_ACM2_ACCEPT.

(** ACM_ACCEPT2 is undecidable *)

Lemma ACM2_undec : undecidable (@ACM2_ACCEPT nat).
Proof.
  apply (undecidability_from_reducibility ndMM2_undec).
  apply ndMM2_to_ACM2_ACCEPT.reduction.
Qed.

Check ACM2_undec.
