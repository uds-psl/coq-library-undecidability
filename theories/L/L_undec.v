Require Import Undecidability.L.L.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Synthetic Require Import
  DecidabilityFacts EnumerabilityFacts.
Require Import Undecidability.L.Enumerators.term_enum.

Require Import Undecidability.TM.TM.
Require Import Undecidability.TM.TM_undec.
Require Import Undecidability.L.Reductions.TM_to_L.

(* ** HaltL is undecidable *)

Lemma HaltL_undec :
  undecidable (HaltL).
Proof.
  apply (undecidability_from_reducibility HaltMTM_undec).
  eapply HaltMTM_to_HaltL.
Qed.
