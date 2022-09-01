(** * Halting problem for a fixed, universal, single-tape, binary Turing machine (HaltUTM) *)

From Coq Require Import Vector.
Import VectorNotations.

From Undecidability Require Import TM Shared.Libs.PSL.FiniteTypes.FinTypesDef.

From Undecidability Require
  MinskyMachines.Reductions.KrivineMclosed_HALT_to_MMA_HALTING
  TM.Reductions.MMA_HALTING_n_to_HaltTM_n
  TM.Reductions.mTM_to_TM
  TM.Reductions.Arbitrary_to_Binary.

(* Universal, binary Turing machine with 1 tape *)
Definition UTM : TM (finType_CS bool) 1.
Proof.
  (* universal Minsky machine with 5 registers *)
  assert (MM5 := KrivineMclosed_HALT_to_MMA_HALTING.Argument.PROG 1).
  (* universal Turing machine with 5 tapes *)
  assert (TM5 := MMA_HALTING_n_to_HaltTM_n.Argument.P MM5).
  (* universal Turing machine with 1 tape *)
  assert (TM1 := mTM_to_TM.M' TM5).
  (* universal, binary Turing machine with 1 tape *)
  exact (Arbitrary_to_Binary.M' TM1).
Defined.

(* Given a binary tape t, does the machine UTM halt starting with t? *)
Definition HaltUTM : tape (finType_CS bool) -> Prop :=
  fun t => HaltsTM UTM [t].
