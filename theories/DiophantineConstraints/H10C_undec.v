(* 
  Autor(s):
    Dominique Larchey-Wendling (1)
    Andrej Dudenhefner (2)
    Johannes Hostert (2)
  Affiliation(s):
    (1) LORIA -- CNRS
    (2) Saarland University, Saarbrücken, Germany
*)

(* ** H10C_SAT, H10SQC_SAT, and H10UC_SAT are undecidable *)

(* 
  Undecidability Result(s):
    Diophantine Constraint Solvability (H10C_SAT)
    Square Diophantine Constraint Solvability (H10SQC_SAT)
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
    Uniform Diophantine Pair Constraint Solvability (H10UPC_SAT)
*)

Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.DiophantineConstraints.H10C.

(* For the reduction chain to complement_HaltL_undec *)
From Undecidability.FRACTRAN  Require Import FRACTRAN Reductions.MM_FRACTRAN.
From Undecidability.MinskyMachines Require Import MM Reductions.BSM_MM.
From Undecidability.StackMachines Require Import BSM Reductions.SBTM_HALT_to_HaltBSM.
Require Import Undecidability.TM.SBTM_undec.

From Undecidability.DiophantineConstraints.Reductions Require
  FRACTRAN_to_H10C_SAT H10C_SAT_to_H10SQC_SAT H10SQC_SAT_to_H10UC_SAT H10UC_SAT_to_H10UPC_SAT.

From Undecidability.FRACTRAN Require Import FRACTRAN FRACTRAN_undec.

(* Undecidability of Diophantine Constraint Solvability *)
Theorem H10C_SAT_undec : undecidable H10C_SAT.
Proof.
  apply (undecidability_from_reducibility FRACTRAN_undec).
  apply (reduces_transitive FRACTRAN_DIO.FRACTRAN_HALTING_DIO_LOGIC_SAT).
  apply (reduces_transitive FRACTRAN_DIO.DIO_LOGIC_ELEM_SAT).
  exact FRACTRAN_to_H10C_SAT.DIO_ELEM_H10C_SAT.
Qed.

(* Undecidability of Square Diophantine Constraint Solvability *)
Theorem H10SQC_SAT_undec : undecidable H10SQC_SAT.
Proof.
  apply (undecidability_from_reducibility H10C_SAT_undec).
  exact H10C_SAT_to_H10SQC_SAT.reduction.
Qed.

(* Undecidability of Uniform Diophantine Constraint Solvability *)
Theorem H10UC_SAT_undec : undecidable H10UC_SAT.
Proof.
  apply (undecidability_from_reducibility H10SQC_SAT_undec).
  exact H10SQC_SAT_to_H10UC_SAT.reduction.
Qed.

Theorem H10UPC_SAT_undec : undecidable H10UPC_SAT.
Proof.
  apply (undecidability_from_reducibility H10UC_SAT_undec).
  exact H10UC_SAT_to_H10UPC_SAT.reduction.
Qed.

Theorem H10UPC_SAT_compl_undec : undecidable (complement H10UPC_SAT).
Proof. 
  apply (undecidability_from_reducibility complement_SBTM_HALT_undec).
  apply reduces_complement.
  eapply reduces_transitive; last apply H10UC_SAT_to_H10UPC_SAT.reduction.
  eapply reduces_transitive; last apply H10SQC_SAT_to_H10UC_SAT.reduction.
  eapply reduces_transitive; last apply H10C_SAT_to_H10SQC_SAT.reduction.
  eapply reduces_transitive; last apply FRACTRAN_to_H10C_SAT.DIO_ELEM_H10C_SAT.
  eapply reduces_transitive; last apply FRACTRAN_DIO.DIO_LOGIC_ELEM_SAT.
  eapply reduces_transitive; last apply FRACTRAN_DIO.FRACTRAN_HALTING_DIO_LOGIC_SAT.
  eapply reduces_transitive; last apply FRACTRAN_REG_FRACTRAN_HALTING.
  eapply reduces_transitive; last apply MM_FRACTRAN_REG_HALTING.
  eapply reduces_transitive; last apply BSM_MM_HALTING.
  exact SBTM_HALT_to_HaltBSM.reduction.
Qed.
