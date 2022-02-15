Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.TM_undec.
Require Import Undecidability.TM.SBTM2.
Require Undecidability.TM.Reductions.HaltTM_1_to_SBTM2_HALT.

(** ** SBTM2_HALT is undecidable  *)

Lemma SBTM2_HALT_undec :
  undecidable SBTM2_HALT.
Proof.
  apply (undecidability_from_reducibility HaltTM_1_undec).
  exact HaltTM_1_to_SBTM2_HALT.reduction.
Qed.
