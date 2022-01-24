(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Decidability Results(s):
    Decidability of Two-counter Machine Reversibility (CM2_REV_dec)
    Decidability of Reversible Two-counter Machine Halting (CM2_REV_HALT_dec)
    Decidability of Two-counter Machine Uniform Boundedness (CM2_UBOUNDED_dec)
    Decidability of Two-counter Machine Uniform Mortality (CM2_UMORTAL_dec)
*)

Require Import Undecidability.Synthetic.Definitions.

Require Import Undecidability.CounterMachines.CM2.
From Undecidability.CounterMachines.Deciders Require
  CM2_REV_dec CM2_REV_HALT_dec CM2_UBOUNDED_dec CM2_UMORTAL_dec.

(* Decidability of Two-counter Machine Reversibility *)
Theorem CM2_REV_dec : decidable CM2_REV.
Proof.
  exists CM2_REV_dec.decide.
  exact CM2_REV_dec.decide_spec.
Qed.

Check CM2_REV_dec.

(* Decidability of Reversible Two-counter Machine Halting *)
Theorem CM2_REV_HALT_dec : decidable CM2_REV_HALT.
Proof.
  exists CM2_REV_HALT_dec.decide.
  exact CM2_REV_HALT_dec.decide_spec.
Qed.

Check CM2_REV_HALT_dec.

(* Decidability ofTwo-counter Machine Uniform Boundedness *)
Theorem CM2_UBOUNDED_dec : decidable CM2_UBOUNDED.
Proof.
  exists CM2_UBOUNDED_dec.decide.
  exact CM2_UBOUNDED_dec.decide_spec.
Qed.

Check CM2_UBOUNDED_dec.
(* Decidability ofTwo-counter Machine Uniform Mortality *)
Theorem CM2_UMORTAL_dec : decidable CM2_UMORTAL.
Proof.
  exists CM2_UMORTAL_dec.decide.
  exact CM2_UMORTAL_dec.decide_spec.
Qed.

Check CM2_UMORTAL_dec.
