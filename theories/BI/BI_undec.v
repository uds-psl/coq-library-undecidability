(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Utf8.

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.MinskyMachines
  Require Import ACM2 ACM2_undec.

From Undecidability.BI
  Require Import BI ACM2_to_BI.

(** The Logic of Bunched Implications is undecidable 

    Remark: we know that BI has cut-elimination, hence
    there are conservative extensions everywhere but
    the undecidability results below are proved w/o 
    using the elimination of the cut rule. *)

(* Consider any fragment of LBI that contains
   the connectives (-∗,⇒,⩑,1) and there respective
   left/right sequent rules, and possibly (or not)
   with the cut rule, then provability is undecidable *)
Theorem LBI_undec (µ : BI_conn → bool) cut :
    µ (BI_impl BI_mult) = true   (* -∗ *)
  → µ (BI_impl BI_addi) = true   (* ⇒  *)
  → µ (BI_conj BI_addi) = true   (* ⩑  *)
  → µ (BI_unit BI_mult) = true   (* 1  *)
  → undecidable (@BI_SEQ_PROVABLE µ nat cut).
Proof.
  intros.
  apply (undecidability_from_reducibility ACM2_undec).
  now apply ACM2_to_BI.reduction_LBI.
Qed.

(* The notion of fragment is harder to manipulate
   for Hilbert style proof systems because axioms
   may relate connectives to each other. *)

Theorem HBI_undec : undecidable (@BI_HILBERT_PROVABLE nat).
Proof.
  apply (undecidability_from_reducibility ACM2_undec).
  now apply ACM2_to_BI.reduction_HBI.
Qed.

Check LBI_undec.
Check HBI_undec.
