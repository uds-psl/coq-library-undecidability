Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.TM_undec.
Require Import Undecidability.TM.SBTM.
Require Undecidability.TM.Reductions.HaltTM_1_to_SBTM_HALT.

(** ** SBTM_HALT is undecidable  *)

Lemma SBTM_HALT_undec :
  undecidable SBTM_HALT.
Proof.
  apply (undecidability_from_reducibility HaltTM_1_undec).
  exact HaltTM_1_to_SBTM_HALT.reduction.
Qed.
