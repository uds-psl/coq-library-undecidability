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

(** ACM_ACCEPT2 is undecidable

    It should be possible to get it on the finite type
    (fin n) for some sufficiently large n, instead of
    on the infinite type nat. But one would need a single 
    2-counters Minsky machine with an undecidable 
    termination predicate. It should be possible to get 
    it from this library using eg H10 like what is
    done for recursive algorithms see
 
        Murec/Util/RA_UNIV_HALT.v *)

Lemma ACM2_undec : undecidable (@ACM2_ACCEPT nat).
Proof.
  apply (undecidability_from_reducibility ndMM2_undec).
  apply ndMM2_to_ACM2_ACCEPT.reduction.
Qed.

Check ACM2_undec.
