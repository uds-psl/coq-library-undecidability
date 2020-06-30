
Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.StringRewriting.SR.

From Undecidability.StringRewriting.Reductions Require 
  TM_to_SRH SRH_to_SR.

(** String rewriting with a halting symbol is undecidable. *)
Lemma SRH_undec : undecidable SRH.
Proof.
  apply (undecidability_from_reducibility undecidability_HaltTM).
  apply (reduces_transitive singleTM.TM_conv).
  exact TM_to_SRH.Halt_SRH.
Qed.

Check SRH_undec.

(** String rewriting is undecidable. *)
Lemma SR_undec : undecidable SR.
Proof.
  apply (undecidability_from_reducibility SRH_undec).
  exact SRH_to_SR.reduction.
Qed.

Check SR_undec.
