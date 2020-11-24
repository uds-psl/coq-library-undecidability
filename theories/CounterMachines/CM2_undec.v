(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Results(s):
    Two Counter Machine Halting (CM2_HALT)
*)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.CounterMachines
  Require Import CM2 Reductions.MM2_HALTING_to_CM2_HALT.

From Undecidability.MinskyMachines
  Require Import MM2 MM2_undec.

(* Undecidability of The Two Counter Machine Halting Problem *)
Lemma CM2_HALT_undec : undecidable CM2_HALT.
Proof.
  apply (undecidability_from_reducibility MM2_HALTING_undec).
  exact MM2_HALTING_to_CM2_HALT.reduction.
Qed.

Check CM2_HALT_undec.
