(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Result(s):
    Linear Polynomial (over N) Constraint Solvability (LPolyNC_SAT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Undecidability.PolynomialConstraints.Reductions.FMsetC_SAT_to_LPolyNC_SAT.

Require Import Undecidability.SetConstraints.FMsetC_undec.

(* Undecidability of Finite Multiset Constraint Solvability *)
Theorem LPolyNC_SAT_undec : undecidable LPolyNC_SAT.
Proof.
  apply (undecidability_from_reducibility FMsetC_SAT_undec).
  exact FMsetC_SAT_to_LPolyNC_SAT.reduction.
Qed.

Check LPolyNC_SAT_undec.
