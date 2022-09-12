Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
Require Import Undecidability.TM.SBTM.
Require Undecidability.TM.Reductions.HaltTM_1_to_SBTM_HALT.
Require Undecidability.TM.Enumerators.SBTM_HALT_enum.

(* ** complement SBTM_HALT is undecidable *)

Lemma complement_SBTM_HALT_undec :
  undecidable (complement SBTM_HALT).
Proof.
  intros H.
  eapply (dec_count_enum H), enumerator_enumerable.
  apply enumerator__T_sigT.
  - now apply (proj2_sig SBTM_HALT_enum.SBTM_enumeration).
  - intros M. now apply (proj2_sig (SBTM_HALT_enum.config_enumeration M)).
Qed.


(* ** SBTM_HALT is undecidable  *)

Lemma SBTM_HALT_undec :
  undecidable SBTM_HALT.
Proof.
  intros H. now apply complement_SBTM_HALT_undec, dec_compl.
Qed.
