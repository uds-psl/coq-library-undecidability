From Undecidability Require Import Compiler_spec MuRec_computable LVector.
From Undecidability.TM Require Import NaryApp ClosedLAdmissible.
From Undecidability.L Require Import HaltMuRec_to_HaltL.
From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode.
From Undecidability.Shared Require Import DLW.Utils.finite DLW.Vec.vec DLW.Vec.pos.
From Undecidability.MuRec Require Import MuRec recalg ra_sem_eq.

Import L_Notations.

Theorem MuRec_computable_to_L_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  MuRec_computable R -> L_computable R.
Proof.
  eapply HaltMuRec_to_HaltL.computable_MuRec_to_L.
Qed.
