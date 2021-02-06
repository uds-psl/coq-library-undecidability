(** ** H10UPC_SAT is undecidable *)

(* 
  Undecidability Result(s):
    Uniform Diophantine Pair Constraint Solvability (H10UPC_SAT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.DiophantineConstraints.H10UPC.

From Undecidability.DiophantineConstraints Require Import H10C H10C_undec.
From Undecidability.DiophantineConstraints.Reductions Require H10UC_SAT_to_H10UPC_SAT.

Theorem H10UPC_SAT_undec : undecidable H10UPC_SAT.
Proof.
  apply (undecidability_from_reducibility H10UC_SAT_undec).
  exact H10UC_SAT_to_H10UPC_SAT.reduction.
Qed.