(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Result(s):
    Simple Semi-unification (SSemiU)
    Right-uniform Two-inequality Semi-unification (RU2SemiU)
    Left-uniform Two-inequality Semi-unification (LU2SemiU)
    Semi-unification (SemiU)
*)

(*
  Literature:
  [1] Andrej Dudenhefner. "Undecidability of Semi-Unification on a Napkin"
      5th International Conference on Formal Structures for Computation and Deduction (FSCD 2020): 9:1-9:16
      https://drops.dagstuhl.de/opus/volltexte/2020/12331
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.SemiUnification.SemiU.

Require Undecidability.SemiUnification.Reductions.CSSM_UB_to_SSemiU.
Require Undecidability.SemiUnification.Reductions.SSemiU_to_RU2SemiU.
Require Undecidability.SemiUnification.Reductions.RU2SemiU_to_LU2SemiU.
Require Undecidability.SemiUnification.Reductions.RU2SemiU_to_SemiU.
Require Import Undecidability.StackMachines.SSM_undec.

(* Undecidability of Simple Semi-unification *)
Theorem SSemiU_undec : undecidable SSemiU.
Proof.
  apply (undecidability_from_reducibility CSSM_UB_undec).
  exact CSSM_UB_to_SSemiU.reduction.
Qed.

Check SSemiU_undec.

(* Undecidability of Right-uniform Two-inequality Semi-unification *)
Theorem RU2SemiU_undec : undecidable RU2SemiU.
Proof.
  apply (undecidability_from_reducibility SSemiU_undec).
  exact SSemiU_to_RU2SemiU.reduction.
Qed.

Check RU2SemiU_undec.

(* Undecidability of Left-uniform Two-inequality Semi-unification *)
Theorem LU2SemiU_undec : undecidable LU2SemiU.
Proof.
  apply (undecidability_from_reducibility RU2SemiU_undec).
  exact RU2SemiU_to_LU2SemiU.reduction.
Qed.

Check LU2SemiU_undec.

(* Undecidability of Semi-unification *)
Theorem SemiU_undec : undecidable SemiU.
Proof.
  apply (undecidability_from_reducibility RU2SemiU_undec).
  exact RU2SemiU_to_SemiU.reduction.
Qed.

Check SemiU_undec.
