Require Import Undecidability.L.L Undecidability.TM.TM.
Require Import Undecidability.L.Reductions.TM_to_L.
Require Import Undecidability.TM.TM_undec.
Require Import Undecidability.Synthetic.Undecidability.

(*** ** HaltL is undecidable *)

Lemma HaltL_undec :
  undecidable HaltL. 
Proof.
  apply (undecidability_from_reducibility HaltMTM_undec).
  eapply HaltMTM_to_HaltL.
Qed.
