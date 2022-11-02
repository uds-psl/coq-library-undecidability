(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Decidability Results(s):
    Decidability of Two-counter Machine Reversibility (MM2_REV_dec)
    Decidability of Reversible Two-counter Machine Halting (MM2_REV_HALT_dec)
    Decidability of Two-counter Machine Uniform Boundedness (MM2_UBOUNDED_dec)
    Decidability of Two-counter Machine Uniform Mortality (MM2_UMORTAL_dec)

  References:
  [1] Dudenhefner, Andrej. "Certified Decision Procedures for Two-Counter Machines."
      FSCD 2022. https://drops.dagstuhl.de/opus/volltexte/2022/16297/
*)

Require Import Undecidability.Synthetic.Definitions.

Require Import Undecidability.MinskyMachines.MM2.
From Undecidability.MinskyMachines.Deciders Require
  MM2_REV_dec MM2_REV_HALT_dec MM2_UBOUNDED_dec MM2_UMORTAL_dec.

(* Decidability of Two-counter Machine Reversibility *)
Theorem MM2_REV_dec : decidable MM2_REV.
Proof.
  exists MM2_REV_dec.decide.
  exact MM2_REV_dec.decide_spec.
Qed.

Check MM2_REV_dec.

(* Decidability of Reversible Two-counter Machine Halting *)
Theorem MM2_REV_HALT_dec : decidable MM2_REV_HALT.
Proof.
  exists MM2_REV_HALT_dec.decide.
  exact MM2_REV_HALT_dec.decide_spec.
Qed.

Check MM2_REV_HALT_dec.

(* Decidability ofTwo-counter Machine Uniform Boundedness *)
Theorem MM2_UBOUNDED_dec : decidable MM2_UBOUNDED.
Proof.
  exists MM2_UBOUNDED_dec.decide.
  exact MM2_UBOUNDED_dec.decide_spec.
Qed.

Check MM2_UBOUNDED_dec.

(* Decidability ofTwo-counter Machine Uniform Mortality *)
Theorem MM2_UMORTAL_dec : decidable MM2_UMORTAL.
Proof.
  exists MM2_UMORTAL_dec.decide.
  exact MM2_UMORTAL_dec.decide_spec.
Qed.

Check MM2_UMORTAL_dec.
