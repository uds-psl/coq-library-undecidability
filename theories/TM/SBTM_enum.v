Require Import Undecidability.TM.SBTM Undecidability.TM.Enumerators.SBTM_HALT_enum.
Require Import Undecidability.Synthetic.Definitions.

(** ** SBTM_HALT is enumerable *)

Lemma SBTM_HALT_enum :
  enumerable (SBTM_HALT).
Proof.
  exists SBTM_HALT_enumerator.
  exact SBTM_HALT_enumerator_spec.
Qed.
