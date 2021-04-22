From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.SeparationLogic Require Import SL MSL_undec Reductions.MSLSAT_to_SLSAT.

Definition SLSAT_undec :
  undecidable SLSAT.
Proof.
  apply (undecidability_from_reducibility MSLSAT_undec). apply reduction.
Qed.
