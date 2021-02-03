(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(*** ** CM1_HALT is undecidable *)

(* 
  Undecidability Results(s):
    One Counter Machine Halting with Denominators at most 4 (CM1_HALT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Reductions.CM2_HALT_to_CM1_HALT.

Require Import Undecidability.CounterMachines.CM2_undec.

(* Undecidability of The One Counter Machine (with Denominators at most 4) Halting Problem *)
Lemma CM1_HALT_undec : undecidable CM1_HALT.
Proof.
  apply (undecidability_from_reducibility CM2_HALT_undec).
  exact CM2_HALT_to_CM1_HALT.reduction.
Qed.

Check CM1_HALT_undec.
