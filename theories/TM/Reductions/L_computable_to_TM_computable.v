From Undecidability Require Import
  MinskyMachines.Reductions.L_computable_to_MMA_computable
  MinskyMachines.Reductions.MMA_computable_to_MMA_mon_computable
  TM.Reductions.MMA_mon_computable_to_TM_computable
  L.L TM.TM.

Lemma L_computable_to_TM_computable k (R : Vector.t nat k -> nat -> Prop) :
  L_computable R -> TM_computable R.
Proof.
  intros H.
  apply MMA_mon_computable_to_TM_computable.
  apply MMA_computable_to_MMA_mon_computable.
  apply L_computable_to_MMA_computable.
  exact H.
Qed.
