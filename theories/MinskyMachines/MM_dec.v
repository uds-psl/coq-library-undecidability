(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Decidability Results(s):
    Decidability of MM_HALTING with two counters (MM_2_HALTING_dec)
*)

Require Import Undecidability.Synthetic.Definitions.

Require Import Undecidability.MinskyMachines.MM.
From Undecidability.MinskyMachines.Deciders Require
  MM_2_HALTING_dec.

(* Decidability of MM_HALTING with two counters *)
Theorem MM_2_HALTING_dec : decidable MM_2_HALTING.
Proof.
  exists MM_2_HALTING_dec.decide.
  exact MM_2_HALTING_dec.decide_spec.
Qed.

Check MM_2_HALTING_dec.
