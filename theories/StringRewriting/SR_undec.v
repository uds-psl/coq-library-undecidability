
Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.StringRewriting.SR.
Require Import Undecidability.TM.SBTM_undec.

From Undecidability.StringRewriting.Reductions Require HaltSBTMu_to_SRH SRH_to_SR HaltSBTMu_to_TSR.

(* String rewriting with a halting symbol is undecidable. *)
Lemma SRH_undec : undecidable SRH.
Proof.
  apply (undecidability_from_reducibility HaltSBTMu_undec).
  apply HaltSBTMu_to_SRH.reduction.
Qed.

Check SRH_undec.

(* String rewriting is undecidable. *)
Lemma SR_undec : undecidable SR.
Proof.
  apply (undecidability_from_reducibility SRH_undec).
  exact SRH_to_SR.reduction.
Qed.

Check SR_undec.

(* Thue system reachability is undecidable. *)
Lemma TSR_undec : undecidable TSR.
Proof.
  apply (undecidability_from_reducibility HaltSBTMu_undec).
  exact HaltSBTMu_to_TSR.reduction.
Qed.

Check SR_undec.
