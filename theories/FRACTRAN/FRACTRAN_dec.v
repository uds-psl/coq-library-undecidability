(*
  Author(s):
    Hizbullah Abdul Aziz Jabbar (1)
    Andrej Dudenhefner (2)
    Dominique Larchey-Wendling (3)
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
    (2) TU Dortmund University, Dortmund, Germany
    (3) LORIA -- CNRS
*)

(*
  Decidability Results(s):
    Decidability of Reversible FRACTRAN Halting (Halt_REV_FRACTRAN_dec)
*)

Require Import Undecidability.Synthetic.Definitions.

Require Import Undecidability.FRACTRAN.FRACTRAN.
From Undecidability.FRACTRAN.Deciders Require
  Halt_REV_FRACTRAN_dec.

(* Decidability of Reversible FRACTRAN Halting *)
Theorem Halt_REV_FRACTRAN_dec : decidable Halt_REV_FRACTRAN.
Proof.
  exists Halt_REV_FRACTRAN_dec.decide.
  exact Halt_REV_FRACTRAN_dec.decide_spec.
Qed.

Check Halt_REV_FRACTRAN_dec.
