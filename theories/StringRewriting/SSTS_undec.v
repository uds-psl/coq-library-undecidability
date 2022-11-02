
Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.StringRewriting.SSTS.
Require Import Undecidability.MinskyMachines.MM2_undec.

Require Undecidability.StringRewriting.Reductions.MM2_ZERO_HALTING_to_SSTS01.

(* Simple Semi-Thue System 01 Rewriting is undecidable. *)
Lemma SSTS01_undec : undecidable SSTS01.
Proof.
  apply (undecidability_from_reducibility MM2_ZERO_HALTING_undec).
  apply MM2_ZERO_HALTING_to_SSTS01.reduction.
Qed.

Check SSTS01_undec.
