Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.TM.Halting.

From Undecidability.MinskyMachines 
  Require Import MM HaltTM_to_MM.

From Undecidability.FRACTRAN
  Require Import FRACTRAN Reductions.MM_FRACTRAN.

(** Many-one reduction from Turing machine halting to FRACTRAN (regular) halting *)
Lemma HaltTM_to_FRACTRAN_REG_HALTING : HaltTM 1 ⪯ FRACTRAN_REG_HALTING.
Proof.
  apply (reduces_transitive HaltTM_to_MM_HALTING).
  exact MM_FRACTRAN_REG_HALTING.
Qed.

(** Many-one reduction from Turing machine halting to FRACTRAN halting *)
Lemma HaltTM_to_FRACTRAN_HALTING : HaltTM 1 ⪯ FRACTRAN_HALTING.
Proof.
  apply (reduces_transitive HaltTM_to_MM_HALTING).
  exact MM_FRACTRAN_HALTING.
Qed.
