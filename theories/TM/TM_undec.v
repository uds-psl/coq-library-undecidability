Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.TM.TM.

Require Import Undecidability.TM.Reductions.mTM_to_TM.
Require Import Undecidability.TM.Reductions.L_to_mTM.
Require Import Undecidability.L.L_undec.
(** ** HaltMTM and HaltTM 1 are undecidable *)

Lemma HaltMTM_undec :
  undecidable HaltMTM.
Proof.
  apply (undecidability_from_reducibility HaltL_undec).
  apply (reduces_transitive HaltL_HaltTM).
  apply nTM_to_MTM.
Qed.

Lemma HaltTM_1_undec :
  undecidable (HaltTM 1).
Proof.
  apply (undecidability_from_reducibility HaltMTM_undec).
  apply MTM_to_stM.
Qed.
