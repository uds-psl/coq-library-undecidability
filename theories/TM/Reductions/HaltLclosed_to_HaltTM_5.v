From Undecidability Require Import 
  L.L TM.TM Synthetic.Definitions Synthetic.ReducibilityFacts.

From Undecidability Require 
  LambdaCalculus.Reductions.HaltLclosed_to_wCBNclosed
  LambdaCalculus.Reductions.wCBNclosed_to_KrivineMclosed_HALT
  MinskyMachines.Reductions.KrivineMclosed_HALT_to_MMA_HALTING
  TM.Reductions.MMA_HALTING_n_to_HaltTM_n.

Lemma reduction : HaltLclosed ⪯ HaltTM 5.
Proof.
  apply (reduces_transitive HaltLclosed_to_wCBNclosed.reduction).
  apply (reduces_transitive wCBNclosed_to_KrivineMclosed_HALT.reduction).
  apply (reduces_transitive KrivineMclosed_HALT_to_MMA_HALTING.reduction).
  exact MMA_HALTING_n_to_HaltTM_n.reduction.
Qed.
