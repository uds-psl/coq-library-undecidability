From Undecidability Require Import TM.TM MinskyMachines.MMA.
From Undecidability Require Import
  MinskyMachines.Reductions.MMA_computable_to_MMA_mon_computable
  TM.Reductions.MMA_mon_computable_to_TM_computable.

Theorem MMA_computable_to_TM_computable k (R : Vector.t nat k -> nat -> Prop) :
  MMA_computable R -> TM_computable R.
Proof.
  intros H.
  apply MMA_mon_computable_to_TM_computable.
  apply MMA_computable_to_MMA_mon_computable.
  apply H.
Qed.
