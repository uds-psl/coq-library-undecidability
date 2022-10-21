
From Undecidability.L Require Import L HaltMuRec_to_HaltL.
From Undecidability.MuRec Require Import MuRec.

Theorem MuRec_computable_to_L_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  MuRec_computable R -> L_computable R.
Proof.
  eapply HaltMuRec_to_HaltL.computable_MuRec_to_L.
Qed.
