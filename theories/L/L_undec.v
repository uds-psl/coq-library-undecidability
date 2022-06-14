Require Import Undecidability.TM.TM_undec.
From Undecidability.L Require Import L Reductions.TM_to_L.
Require Import Undecidability.Synthetic.Undecidability.

(** ** HaltL is undecidable *)

Lemma HaltL_undec :
  undecidable (HaltL).
Proof.
  apply (undecidability_from_reducibility HaltMTM_undec).
  eapply HaltMTM_to_HaltL.
Qed.
