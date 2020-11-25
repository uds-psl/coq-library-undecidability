(* 
  Autor(s):
    Dominique Larchey-Wendling (1)
    Andrej Dudenhefner (2) 
  Affiliation(s):
    (1) LORIA -- CNRS
    (2) Saarland University, Saarbrücken, Germany
*)

(** ** H10C_sat and H10UC_sat are undecidable *)

(* 
  Undecidability Result(s):
    Diophantine Constraint Solvability (H10C_SAT)
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.DiophantineConstraints.H10C.

From Undecidability.DiophantineConstraints.Reductions Require
  H10C_SAT_to_H10UC_SAT FRACTRAN_to_H10C_SAT.

From Undecidability.FRACTRAN Require Import FRACTRAN FRACTRAN_undec.

(* Undecidability of Diophantine Constraint Solvability *)
Theorem H10C_SAT_undec : undecidable H10C_SAT.
Proof.
  apply (undecidability_from_reducibility FRACTRAN_undec).
  apply (reduces_transitive FRACTRAN_DIO.FRACTRAN_HALTING_DIO_LOGIC_SAT).
  apply (reduces_transitive FRACTRAN_DIO.DIO_LOGIC_ELEM_SAT).
  exact FRACTRAN_to_H10C_SAT.DIO_ELEM_H10C_SAT.
Qed.

Check H10C_SAT_undec.

(* Undecidability of Uniform Diophantine Constraint Solvability *)
Theorem H10UC_SAT_undec : undecidable H10UC_SAT.
Proof.
  apply (undecidability_from_reducibility H10C_SAT_undec).
  exact H10C_SAT_to_H10UC_SAT.reduction.
Qed.

Check H10UC_SAT_undec.
