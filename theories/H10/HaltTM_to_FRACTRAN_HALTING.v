Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.H10.Fractran.fractran_defs.

Require Import Undecidability.H10.HaltTM_to_MM_HALTING.
Require Import Undecidability.H10.MM_FRACTRAN.

(** Many-one reduction from Turing machine halting to FRACTRAN halting *)
Lemma HaltTM_to_FRACTRAN_HALTING : HaltTM 1 ⪯ FRACTRAN_HALTING.
Proof.
  apply (reduces_transitive HaltTM_to_MM_HALTING).
  exact MM_FRACTRAN_HALTING.
Qed.
