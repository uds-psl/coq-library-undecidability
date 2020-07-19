(* 
  Autor(s):
    Dominique Larchey-Wendling (1)
    Andrej Dudenhefner (2) 
  Affiliation(s):
    (1) LORIA -- CNRS
    (2) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Result(s):
    Diophantine Constraint Solvability (H10C_SAT)
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.DiophantineConstraints.H10C.

From Undecidability.DiophantineConstraints.Reductions Require
  H10C_SAT_to_H10UC_SAT FRACTRAN_to_H10C_SAT.

Require Import Undecidability.PCP.PCP_undec.
Require Undecidability.ILL.UNDEC Undecidability.H10.MM_FRACTRAN Undecidability.H10.FRACTRAN_DIO.

(* Undecidability of Diophantine Constraint Solvability *)
Theorem H10C_SAT_undec : undecidable H10C_SAT.
Proof.
  apply (undecidability_from_reducibility PCP_undec).
  apply (reduces_transitive UNDEC.PCP_MM_HALTING).
  apply (reduces_transitive MM_FRACTRAN.MM_FRACTRAN_HALTING).
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
