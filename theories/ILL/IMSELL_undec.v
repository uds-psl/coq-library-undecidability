(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.CounterMachines
  Require Import ndMM2 ndMM2_undec.

From Undecidability.ILL
  Require Import IMSELL ndMM2_IMSELL.

Local Infix "≤" := (@IMSELL_le _) (at level 70).
Local Notation "u ≰ v" := (~ u ≤ v) (at level 70).
Local Notation U := (@IMSELL_U _).

(* Undecidability of IMSELL3, ie IMSELL with
   3 modalities {a,b,∞} with a,b < ∞ and 
   ∞ is the only universal modality *)

Theorem IMSELL_undec (S : IMSELL_sig) : 
     (exists a b i : S, a ≤ i /\ b ≤ i /\ a ≰ b /\ b ≰ a /\ ~ U a /\ ~ U b /\ U i)
  -> undecidable (@IMSELL_cf_PROVABILITY S).
Proof.
  intro. 
  apply (undecidability_from_reducibility ndMM2_undec).
  now apply ndMM2_IMSELL.reduction.
Qed.

Theorem IMSELL3_undec : undecidable (@IMSELL_cf_PROVABILITY imsell3).
Proof.
  apply IMSELL_undec.
  now exists (Some true), (Some false), None.
Qed.


