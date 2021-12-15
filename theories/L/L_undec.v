Require Import Undecidability.L.L.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Synthetic Require Import
  DecidabilityFacts EnumerabilityFacts.
Require Import Undecidability.L.Enumerators.term_enum.

(** ** HaltL is undecidable *)

Lemma HaltL_undec :
  undecidable (HaltL).
Proof.
  intros H%dec_compl.
  now eapply (dec_count_enum H), enumerator_enumerable, enumerator__T_term.
Qed.
