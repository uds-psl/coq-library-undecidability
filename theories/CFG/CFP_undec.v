Require Import Undecidability.CFG.CFP.

From Undecidability.CFG.Reductions Require 
  PCP_to_CFPP PCP_to_CFPI.

Require Import Undecidability.Synthetic.Undecidability.

Require Undecidability.PCP.PCP_undec.

(* The Context-free Post Grammar Palindrome Problem is undecidable. *)
Lemma CFPP_undec : undecidable CFPP.
Proof.
  eapply undecidability_from_reducibility.
  exact PCP_undec.PCP_undec.
  exact PCP_to_CFPP.reduction.
Qed.

(* The Context-free Post Grammar Intersection Problem is undecidable. *)
Lemma CFPI_undec : undecidable CFPI.
Proof.
  eapply undecidability_from_reducibility.
  exact PCP_undec.PCP_undec.
  exact PCP_to_CFPI.reduction.
Qed.
