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

(* Undecidability of IMSELL3, ie IMSELL with
   3 modalities {a,b,∞} with a,b < ∞ and 
   ∞ is the only universal modality *)

Theorem IMSELL3_undec : undecidable (@IMSELL_cf_provable imsell3).
Proof.
  apply (undecidability_from_reducibility ndMM2_undec).
  apply ndMM2_IMSELL.reduction.
Qed.




    


