(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Two Counter Machine Halting (CM2_HALT)
  to:
    Simple Semi-Thue System 01 Rewriting (SSTS01)
*)

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.CounterMachines.CM2.
Require Import Undecidability.StringRewriting.SSTS.

From Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01 
  Require CM2_HALT_to_SR2ab SR2ab_to_SSTS01.

(* Two Counter Machine Halting many-one reduces to Simple Semi-Thue System 01 Rewriting *)
Theorem reduction : CM2_HALT ⪯ SSTS01.
Proof.
  apply (reduces_transitive CM2_HALT_to_SR2ab.reduction).
  exact SR2ab_to_SSTS01.reduction.
Qed.
