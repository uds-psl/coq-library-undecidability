Require Import Undecidability.L.L.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Synthetic Require Import DecidabilityFacts.

Require Import Undecidability.MinskyMachines.MMA2_undec.
Require Undecidability.L.Reductions.MMA_HALTING_to_HaltLclosed.

(* The Halting problem for weak call-by-value lambda-calculus is undecidable *)
Lemma HaltLclosed_undec :
  undecidable (HaltLclosed).
Proof.
  apply (undecidability_from_reducibility MMA2_HALTING_undec).
  eapply MMA_HALTING_to_HaltLclosed.reduction.
Qed.

(** ** HaltL is undecidable *)
Lemma HaltL_undec :
  undecidable (HaltL).
Proof.
  apply (undecidability_from_reducibility HaltLclosed_undec).
  now exists (fun '(exist _ M _) => M).
Qed.
