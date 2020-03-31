Require Import Undecidability.CFG.CFP.

From Undecidability.CFG.Reductions Require 
  PCP_to_CFPP PCP_to_CFPI.

Require Import Undecidability.Problems.TM.
Require Import Undecidability.Problems.Reduction.

Require Undecidability.PCP.PCP_undec.

(** The Context-free Post Grammar Palindrome Problem is undecidable. *)
Lemma CFPP_undec : HaltTM 1 ⪯ CFPP.
Proof.
  eapply reduces_transitive.
  exact PCP_undec.PCP_undec.
  exact PCP_to_CFPP.reduction.
Qed.

(** The Context-free Post Grammar Intersection Problem is undecidable. *)
Lemma CFPI_undec : HaltTM 1 ⪯ CFPI.
Proof.
  eapply reduces_transitive.
  exact PCP_undec.PCP_undec.
  exact PCP_to_CFPI.reduction.
Qed.
