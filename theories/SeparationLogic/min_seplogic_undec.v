From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.SeparationLogic Require Import min_seplogic Reductions.FSATdc_to_MSPSAT.
From Undecidability.FOL Require Import FSAT_undec.

Definition MSPSAT_undec :
  undecidable MSPSAT.
Proof.
  apply (undecidability_from_reducibility FSATdc_undec). apply reduction.
Qed.
  
