(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction(s):
    Halting of Minsky machines with two counters (MM2_HALTING) to
    Halting of one counter machines (CM1_HALT)
*)

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.CounterMachines.CM1.

From Undecidability.CounterMachines.Reductions Require
  MM2_HALTING_to_CM2_HALT CM2_HALT_to_CM1_HALT.

(* halting of Minsky machines with two counters 
  many-one reduces to halting of one counter machines *)
Theorem reduction : MM2_HALTING ⪯ CM1_HALT.
Proof.
  apply (reduces_transitive MM2_HALTING_to_CM2_HALT.reduction).
  exact CM2_HALT_to_CM1_HALT.reduction.
Qed.
