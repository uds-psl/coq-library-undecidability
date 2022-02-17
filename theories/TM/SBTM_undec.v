Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.Synthetic.EnumerabilityFacts.
Require Import Undecidability.TM.TM_undec.
Require Import Undecidability.TM.SBTM.
Require Undecidability.TM.Reductions.HaltTM_1_to_SBTM_HALT.
Require Undecidability.TM.Enumerators.SBTM_HALT_enum.

(** ** SBTM_HALT is undecidable  *)

Lemma SBTM_HALT_undec :
  undecidable SBTM_HALT.
Proof.
  apply (undecidability_from_reducibility HaltTM_1_undec).
  exact HaltTM_1_to_SBTM_HALT.reduction.
Qed.

(** ** complement SBTM_HALT is undecidable *)

(* TODO restate if SBTM_HALT becomes seed *)
Lemma complement_SBTM_HALT_undec :
  decidable (complement SBTM_HALT) -> enumerable (complement SBTM_HALT).
Proof.
  intros H.
  eapply (dec_count_enum H), enumerator_enumerable.
  apply enumerator__T_sigT.
  - now apply (proj2_sig SBTM_HALT_enum.SBTM_enumeration).
  - intros M. now apply (proj2_sig (SBTM_HALT_enum.config_enumeration M)).
Qed.
