Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.

Require Undecidability.StringRewriting.Util.singleTM.

Require Import Undecidability.TM.Halting.
Require Import Undecidability.StringRewriting.SR.

Require Import Undecidability.StringRewriting.Reductions.TM_to_SRH.
Require Import Undecidability.StringRewriting.Reductions.SRH_to_SR.

(** Many-one reduction from Turing machine halting to string rewriting *)
Lemma HaltTM_to_SR : HaltTM 1 ⪯ SR.
Proof.
  apply (reduces_transitive singleTM.TM_conv).
  apply (reduces_transitive Halt_SRH).
  exact SRH_to_SR.reduction.
Qed.
