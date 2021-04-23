From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.SeparationLogic Require Import MSL Reductions.FSATdc_to_MSLSAT.
From Undecidability.FOL Require Import FSAT_undec.

Definition MSLSAT_undec :
  undecidable MSLSAT.
Proof.
  apply (undecidability_from_reducibility FSATdc_undec). apply reduction.
Qed.
  
