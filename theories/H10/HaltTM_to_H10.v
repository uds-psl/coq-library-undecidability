Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.H10.H10.

Require Import Undecidability.H10.HaltTM_to_FRACTRAN_HALTING.
Require Import Undecidability.H10.FRACTRAN_DIO.

(** Many-one reduction from Turing machine halting to Hilbert's tenth problem *)
Lemma HaltTM_to_H10 : HaltTM 1 ⪯ H10.
Proof.
  apply (reduces_transitive HaltTM_to_FRACTRAN_HALTING).
  apply (reduces_transitive FRACTRAN_HALTING_DIO_LOGIC_SAT).
  apply (reduces_transitive DIO_LOGIC_ELEM_SAT).
  apply (reduces_transitive DIO_ELEM_SINGLE_SAT).
  exact DIO_SINGLE_SAT_H10.
Qed.
