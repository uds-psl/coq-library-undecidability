(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(** ** FMsetC_SAT is undecidable *)

(* 
  Undecidability Result(s):
    Finite Multiset Constraint Solvability (FMsetC_SAT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.SetConstraints.FMsetC.
Require Undecidability.SetConstraints.Reductions.H10UC_SAT_to_FMsetC_SAT.

Require Import Undecidability.DiophantineConstraints.H10C_undec.

(* Undecidability of Finite Multiset Constraint Solvability *)
Theorem FMsetC_SAT_undec : undecidable FMsetC_SAT.
Proof.
  apply (undecidability_from_reducibility H10UC_SAT_undec).
  exact H10UC_SAT_to_FMsetC_SAT.reduction.
Qed.

Check FMsetC_SAT_undec.
