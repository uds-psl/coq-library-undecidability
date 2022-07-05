Require Import
  Undecidability.L.L
  Undecidability.TM.TM
  Undecidability.StackMachines.BSM
  Undecidability.MinskyMachines.MM
  Undecidability.FRACTRAN.FRACTRAN
  Undecidability.H10.H10
  Undecidability.MuRec.MuRec.

From Undecidability Require Import
  L_computable_to_TM_computable
  (* TM_computable_to_BSM_computable *)
  (* BSM_computable_to_MM_computable *)
  MM_computable_to_FRACTRAN_computable
  FRACTRAN_computable_to_Diophantine
  Diophantine
  Diophantine_to_MuRec_computable
  MuRec_computable_to_L_computable.

Theorem equivalence {k} (R : Vector.t nat k -> nat -> Prop) :
  (L_computable R -> TM_computable R) /\
  (MM_computable R -> FRACTRAN_computable R) /\
  (FRACTRAN_computable R -> Diophantine' R /\ functional R) /\
  (Diophantine' R /\ functional R -> MuRec_computable R) /\
  (MuRec_computable R -> L_computable R).
Proof.
  repeat split.
  - apply L_computable_to_TM_computable.
  - apply MM_computable_to_FRACTRAN_computable.
  - eapply FRACTRAN_computable_to_Diophantine; assumption.
  - intros ? ? ? ? ?. eapply FRACTRAN_computable.FRACTRAN_computable_functional; eauto.
  - intros []. eapply Diophantine_to_MuRec_computable; eauto.
  - eapply MuRec_computable_to_L_computable.
Qed.
