(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Result(s):
    Uniform Boundedness of Deterministic, Length-preserving Stack Machines (SMNdl_UB)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.StackMachines.SMN.

Require Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.
Require Import Undecidability.CounterMachines.CM1_undec.

(* Undecidability of Uniform Boundedness of Deterministic, Length-preserving Stack Machines *)
Theorem SMNdl_UB_undec : undecidable SMNdl_UB.
Proof.
  apply (undecidability_from_reducibility CM1_HALT_undec).
  exact CM1_HALT_to_SMNdl_UB.reduction.
Qed.

Check SMNdl_UB_undec.
