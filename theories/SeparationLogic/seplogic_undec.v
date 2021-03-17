From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.SeparationLogic Require Import seplogic min_seplogic_undec Reductions.MSPSAT_to_SPSAT.

Definition SPSAT_undec :
  undecidable SPSAT.
Proof.
  apply (undecidability_from_reducibility MSPSAT_undec). apply reduction.
Qed.
