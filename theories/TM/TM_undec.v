Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.TM.TM.

Require Import Undecidability.TM.Reductions.SBTM_HALT_to_HaltTM_1.
Require Import Undecidability.TM.SBTM_undec.
(** ** HaltMTM and HaltTM 1 are undecidable *)

Lemma HaltMTM_undec :
  undecidable HaltMTM.
Proof.
  apply (undecidability_from_reducibility SBTM_HALT_undec).
  apply (reduces_transitive SBTM_HALT_to_HaltTM_1.reduction).
  unshelve eexists.
  - intros [Sig M t]. exists (1, Sig); eassumption.
  - now intros [Sig M t].
Qed.

Lemma HaltTM_1_undec :
  undecidable (HaltTM 1).
Proof.
  apply (undecidability_from_reducibility SBTM_HALT_undec).
  exact SBTM_HALT_to_HaltTM_1.reduction.
Qed.
