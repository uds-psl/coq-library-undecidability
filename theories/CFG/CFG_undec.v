Require Import Undecidability.CFG.CFG.

From Undecidability.CFG.Reductions Require 
  CFPP_to_CFP CFPI_to_CFI.

Require Import Undecidability.Problems.TM.
Require Import Undecidability.Problems.Reduction.

Require Undecidability.CFG.CFP_undec.

(** The Context-free Palindrome Problem is undecidable. *)
Lemma CFP_undec : HaltTM 1 ⪯ CFP.
Proof.
  eapply reduces_transitive.
  exact CFP_undec.CFPP_undec.
  exact CFPP_to_CFP.reduction.
Qed.

Check CFP_undec.

(** The Context-free Intersection Problem is undecidable. *)
Lemma CFI_undec : HaltTM 1 ⪯ CFI.
Proof.
  eapply reduces_transitive.
  exact CFP_undec.CFPI_undec.
  exact CFPI_to_CFI.reduction.
Qed.

Check CFI_undec.
