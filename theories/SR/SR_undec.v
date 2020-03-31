Require Import Undecidability.SR.SR.
Require Undecidability.SR.Util.singleTM.
Require Import Undecidability.Problems.TM.
Require Import Undecidability.Problems.Reduction.

From Undecidability.SR.Reductions Require 
  TM_to_SRH SRH_to_SR.

(** String rewriting with a halting symbol is undecidable. *)
Lemma SRH_undec : HaltTM 1 ⪯ SRH.
Proof.
  eapply reduces_transitive.
  exact singleTM.TM_conv.
  exact TM_to_SRH.Halt_SRH.
Qed.

Check SRH_undec.

(** String rewriting is undecidable. *)
Lemma SR_undec : HaltTM 1 ⪯ SR.
Proof.
  eapply reduces_transitive.
  exact SRH_undec.
  exact SRH_to_SR.reduction.
Qed.

Check SR_undec.
